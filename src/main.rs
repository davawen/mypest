use std::{hash::Hash, fmt::Debug, str::Chars, fs, env, io, path::Path, error::Error};

use pest::{iterators::{Pair, Pairs}, Parser, Span};
use pest_derive::Parser;

trait ExpectIterator<T>: Iterator<Item = T> {
    /// Expects that a value is in this iterator, panics otherwise
    fn expect(&mut self) -> T {
        self.next().unwrap()
    }
}

extern crate alloc;

#[derive(Parser)]
#[grammar = "pest3.pest"]
struct Pest3;

fn print_record(record: Pair<Rule>, depth: usize) {
    let indent = " ".repeat(depth * 2);

    let (r, span, s) = (record.as_rule(), record.as_span(), record.as_str());

    let show = matches!(r, Rule::doc_comment | Rule::line_doc | Rule::ident | Rule::char_range | Rule::insensitive_string | Rule::string | Rule::char);

    println!("{indent}- {r:?} {}", if show { format!("\"{s}\"") } else { String::new() });

    for pair in record.into_inner() {
        print_record(pair, depth + 1);
    }
}

mod ast {
    use std::{str::Chars, fmt::Debug, hash::Hash};

    use itertools::Itertools;
    use lazy_static::lazy_static;
    use pest::{iterators::{Pair, Pairs}, pratt_parser::{PrattParser, Op, Assoc, PrattParserMap}};

    use crate::ExpectIterator;

    use super::Rule;

    impl<'a, T: Copy + Debug + Hash + Ord> ExpectIterator<Pair<'a, T>> for Pairs<'a, T> {}
    impl ExpectIterator<char> for Chars<'_> {}

    #[derive(Debug)]
    pub struct Grammar {
        pub docs: Vec<String>,
        pub rules: Vec<AstRule>
    }

    #[derive(Debug)]
    pub struct AstRule {
        pub docs: Vec<String>,
        pub name: Ident,
        pub modifier: Option<Modifier>,
        pub expr: Expr
    }

    #[derive(Debug)]
    pub struct Ident(pub String);

    #[derive(Debug, Clone, Copy)]
    pub enum Modifier {
        Atomic,
        Silent,
        Compound,
        NonAtomic
    }

    #[derive(Debug)]
    pub enum Expr {
        Parenthesized(Box<Expr>),
        CharRange(char, char),
        String(String),
        CaseInsensitive(String),
        Rule(Ident),
        Order(Box<Expr>, Box<Expr>),
        Sequence(Box<Expr>, Box<Expr>),
        PositivePredicate(Box<Expr>),
        NegativePredicate(Box<Expr>),
        ZeroOrMore(Box<Expr>),
        OneOrMore(Box<Expr>),
        Optional(Box<Expr>),
        MinMax(u32, u32, Box<Expr>),
        Max(u32, Box<Expr>),
        Min(u32, Box<Expr>),
        Exact(u32, Box<Expr>)
    }

    lazy_static! {
        static ref PRATT: PrattParser<Rule> = PrattParser::new()
            .op(Op::infix(Rule::order, Assoc::Left))
            .op(Op::infix(Rule::sequence, Assoc::Left))
            .op(Op::prefix(Rule::positive_predicate) | Op::prefix(Rule::negative_predicate))
            .op(Op::postfix(Rule::zero_or_more) | Op::postfix(Rule::one_or_more) | Op::postfix(Rule::optional) | Op::postfix(Rule::numbered));
    }

    pub fn parse(record: Pair<Rule>) -> Grammar {
        assert_eq!(record.as_rule(), Rule::grammar);

        let mut pairs = record.into_inner().filter(|r| !matches!(r.as_rule(), Rule::EOI));

        Grammar {
            docs: pairs.take_while_ref(|r| matches!(r.as_rule(), Rule::doc_comment)).map(parse_doc).collect(),
            rules: pairs.map(parse_rule).collect()
        }
    }

    fn parse_doc(record: Pair<Rule>) -> String {
        match record.as_rule() {
            Rule::doc_comment => parse_doc(record.into_inner().expect()),
            Rule::line_doc => parse_doc(record.into_inner().expect()),
            Rule::inner_doc => record.as_str().to_owned(),
            _ => unreachable!()
        }
    }

    fn parse_rule(record: Pair<Rule>) -> AstRule {
        assert_eq!(record.as_rule(), Rule::rule);
        let mut pairs = record.into_inner();

        let docs = pairs.take_while_ref(|r| matches!(r.as_rule(), Rule::line_doc)).map(parse_doc).collect();

        let name = Ident(pairs.expect().as_str().to_owned());
        let modifier = if let Rule::modifier = pairs.peek().unwrap().as_rule() {
            let m = match pairs.expect().into_inner().expect().as_rule() {
                Rule::atomic => Modifier::Atomic,
                Rule::silent => Modifier::Silent,
                Rule::compound => Modifier::Compound,
                Rule::non_atomic => Modifier::NonAtomic,
                _ => unreachable!()
            };
            Some(m)
        } else { None };
        let expr = parse_expr(pairs.expect());
        AstRule {
            docs, name, modifier, expr
        }
    }

    fn parse_expr(record: Pair<Rule>) -> Expr {
        PRATT
            .map_primary(|r| match r.as_rule() {
                Rule::char_range => {
                    let mut chars = r.into_inner();
                    let mut get_char = || chars.expect().as_str().chars().take(2).last().unwrap();
                    Expr::CharRange(
                        get_char(), get_char()
                    )
                }
                Rule::insensitive_string => Expr::CaseInsensitive(parse_string(r.into_inner().expect())),
                Rule::string => Expr::String(parse_string(r)),
                Rule::ident => Expr::Rule(Ident(r.as_str().to_owned())),
                Rule::parenthesized => Expr::Parenthesized(Box::new(parse_expr(r.into_inner().expect()))),
                Rule::expr => parse_expr(r),
                _ => unreachable!()
            })
            .map_infix(|lhs, r, rhs| match r.as_rule() {
                Rule::order => Expr::Order(Box::new(lhs), Box::new(rhs)),
                Rule::sequence => Expr::Sequence(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!("{r:#?}")
            })
            .map_prefix(|r, rhs| match r.as_rule() {
                Rule::positive_predicate => Expr::PositivePredicate(Box::new(rhs)),
                Rule::negative_predicate => Expr::NegativePredicate(Box::new(rhs)),
                _ => unreachable!()
            })
            .map_postfix(|lhs, r| match r.as_rule() {
                Rule::zero_or_more => Expr::ZeroOrMore(Box::new(lhs)),
                Rule::one_or_more => Expr::OneOrMore(Box::new(lhs)),
                Rule::optional => Expr::Optional(Box::new(lhs)),
                Rule::numbered => parse_numbered(Box::new(lhs), r.into_inner().expect()),
                _ => unreachable!()
            })
            .parse(record.into_inner())
    }

    fn parse_numbered(lhs: Box<Expr>, record: Pair<Rule>) -> Expr {
        let r = record.as_rule();
        let mut pairs = record.into_inner();
        let mut num = || -> u32 {
            pairs.expect().as_str().parse().unwrap()
        };

        match r {
            Rule::between_n_and_m => Expr::MinMax(num(), num(), lhs),
            Rule::at_most_n => Expr::Max(num(), lhs),
            Rule::at_least_n => Expr::Min(num(), lhs),
            Rule::exactly_n => Expr::Exact(num(), lhs),
            _ => unreachable!()
        }
    }

    fn parse_string(record: Pair<Rule>) -> String {
        assert_eq!(record.as_rule(), Rule::string);
        let inner_string = record.into_inner();
        inner_string.as_str().to_owned()
    }
}

mod process {
    use std::fmt::{Write, Display, self, Formatter};

    use crate::ast::{self, Ident};
    impl Display for ast::Grammar {
        fn fmt(&self, out: &mut Formatter<'_>) -> fmt::Result {
            for doc in &self.docs {
                writeln!(out, "//! {doc}")?
            }
            writeln!(out)?;

            for rule in &self.rules {
                writeln!(out, "{rule}")?;
            }

            Ok(())
        }
    }

    impl Display for ast::AstRule {
        fn fmt(&self, out: &mut Formatter<'_>) -> fmt::Result {
            for doc in &self.docs {
                writeln!(out, "/// {doc}")?;
            }
            let modifier = if let Some(modifier) = self.modifier { format!("{modifier}") } else { String::new() };
            write!(out, "{} = {}{{ {} }}", self.name, modifier, self.expr)?;

            Ok(())
        }
    }

    impl Display for ast::Ident {
        fn fmt(&self, out: &mut Formatter<'_>) -> fmt::Result {
            write!(out, "{}", self.0)
        }
    }

    impl Display for ast::Modifier {
        fn fmt(&self, out: &mut Formatter<'_>) -> fmt::Result {
            let chr = match self {
                Self::Atomic => '@', Self::NonAtomic => '!', Self::Compound => '$', Self::Silent => '_' 
            };
            write!(out, "{chr}")
        }
    }

    macro_rules! match_format {
        ($e:expr, $f:expr, { $($p:pat => $format:literal),+ }) => {
            match $e {
                $($p => write!($f, $format)),+
            }
        };
    }
    impl Display for ast::Expr {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            match_format!( self, f, {
                Self::Parenthesized(e) => "({e})",
                Self::CharRange(a, b) => "'{a}'..'{b}'",
                Self::String(s) => "\"{s}\"",
                Self::CaseInsensitive(s) => "^\"{s}\"",
                Self::Rule(Ident(i)) => "{i}",
                Self::Order(a, b) => "{a} | {b}",
                Self::Sequence(a, b) => "{a} ~ {b}",
                Self::PositivePredicate(p) => "&{p}",
                Self::NegativePredicate(p) => "!{p}",
                Self::ZeroOrMore(e) => "{e}*",
                Self::OneOrMore(e) => "{e}+",
                Self::Optional(e) => "{e}?",
                Self::MinMax(min, max, e) => "{e}{{{min}, {max}}}",
                Self::Max(max, e) => "{e}{{, {max}}}",
                Self::Min(min, e) => "{e}{{{min},}}",
                Self::Exact(n, e) => "{e}{{{n}}}"
            })
        }
    }
}

/// Preprocess pest3 grammars into pest
#[derive(clap::Parser)]
struct Args {
    /// Wether to print the structure of the parsed grammar
    #[arg(short, long)]
    show_grammar: bool,

    /// Wether to print the resulting ast structure
    #[arg(short, long)]
    print_ast: bool,

    /// Input pest3 grammar
    input_file: String,

    /// Output grammar, or if not present output to STDOUT
    output_file: Option<String>
}

fn main() -> Result<(), Box<dyn Error>> {
    use clap::Parser;
    let args = Args::parse();

    let src = fs::read_to_string(args.input_file)?;

    let mut tree = Pest3::parse(Rule::grammar, &src)?;

    if args.show_grammar {
        for r in tree.clone() {
            print_record(r, 0);
        }
    }

    let grammar = ast::parse(tree.expect());
    if args.print_ast {
        println!("{grammar:#?}");
    }

    let generated = format!("{grammar}");
    if let Some(out) = args.output_file {
        fs::write(out, generated)?;
    } else {
        println!("{generated}");
    }

    Ok(())
}
