use std::{str::Chars, fmt::Debug, hash::Hash};

use itertools::Itertools;
use lazy_static::lazy_static;
use pest::{iterators::{Pair, Pairs}, pratt_parser::{PrattParser, Op, Assoc}};

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
    Silent,
}

#[derive(Debug, Clone, Copy)]
pub enum SequenceKind {
    Direct, // -
    Implicit, // ~
    Spaced, // ^
}

#[derive(Debug)]
pub enum Expr {
    Parenthesized(Box<Expr>),
    CharRange(char, char),
    String(String),
    CaseInsensitive(String),
    Rule(Ident),
    Sequence(SequenceKind, Box<Expr>, Box<Expr>),
    Order(Box<Expr>, Box<Expr>),
    PositivePredicate(Box<Expr>),
    NegativePredicate(Box<Expr>),
    Optional(Box<Expr>),
    Repetition(Box<Expr>, SequenceKind, Repetition)
}

#[derive(Debug)]
pub enum Repetition {
    ZeroOrMore,
    OneOrMore,
    MinMax(u32, u32),
    Max(u32),
    Min(u32),
    Exact(u32)
}

lazy_static! {
    static ref PRATT: PrattParser<Rule> = PrattParser::new()
        .op(Op::infix(Rule::order, Assoc::Left))
        .op(Op::infix(Rule::sequence, Assoc::Left))
        .op(Op::prefix(Rule::positive_predicate) | Op::prefix(Rule::negative_predicate))
        .op(Op::postfix(Rule::multiplier) | Op::postfix(Rule::optional));
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
    let modifier = if let Rule::silent = pairs.peek().unwrap().as_rule() {
        let m = match pairs.expect().as_rule() {
            Rule::silent => Modifier::Silent,
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
            Rule::sequence => Expr::Sequence(
                parse_sequence_kind(r.into_inner().expect()),
                Box::new(lhs), Box::new(rhs)
            ),
            Rule::order => Expr::Order(Box::new(lhs), Box::new(rhs)),
            _ => unreachable!("{r:#?}")
        })
        .map_prefix(|r, rhs| match r.as_rule() {
            Rule::positive_predicate => Expr::PositivePredicate(Box::new(rhs)),
            Rule::negative_predicate => Expr::NegativePredicate(Box::new(rhs)),
            _ => unreachable!()
        })
        .map_postfix(|lhs, r| match r.as_rule() {
            Rule::optional => Expr::Optional(Box::new(lhs)),
            Rule::multiplier => {
                let mut pairs = r.into_inner();
                let kind = parse_sequence_kind(pairs.expect());

                let r = pairs.expect();
                let m = match r.as_rule() {
                    Rule::zero_or_more => Repetition::ZeroOrMore,
                    Rule::one_or_more => Repetition::OneOrMore,
                    Rule::numbered => parse_numbered(r.into_inner().expect()),
                    _ => unreachable!()
                };

                Expr::Repetition(Box::new(lhs), kind, m)
            }
            _ => unreachable!()
        })
        .parse(record.into_inner())
}

fn parse_sequence_kind(record: Pair<Rule>) -> SequenceKind {
    match record.as_rule() {
        Rule::direct => SequenceKind::Direct,
        Rule::implicit => SequenceKind::Implicit,
        Rule::spaced => SequenceKind::Spaced,
        _ => unreachable!()
    }
}

fn parse_numbered(record: Pair<Rule>) -> Repetition {
    let r = record.as_rule();
    let mut pairs = record.into_inner();
    let mut num = || -> u32 {
        pairs.expect().as_str().parse().unwrap()
    };

    match r {
        Rule::between_n_and_m => Repetition::MinMax(num(), num()),
        Rule::at_most_n => Repetition::Max(num()),
        Rule::at_least_n => Repetition::Min(num()),
        Rule::exactly_n => Repetition::Exact(num()),
        _ => unreachable!()
    }
}

fn parse_string(record: Pair<Rule>) -> String {
    assert_eq!(record.as_rule(), Rule::string);
    let inner_string = record.into_inner();
    inner_string.as_str().to_owned()
}
