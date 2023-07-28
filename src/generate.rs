use std::fmt::{Display, self, Formatter};

use crate::{ast::{self, Ident}, custom_format::CustomFormat};
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

        write!(out, "{} = {}{{ {} }}", self.name, self.modifier.my_fmt(&()), self.expr)?;

        Ok(())
    }
}

impl Display for ast::Ident {
    fn fmt(&self, out: &mut Formatter<'_>) -> fmt::Result {
        write!(out, "{}", self.0)
    }
}

impl CustomFormat<()> for Option<ast::Modifier> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _: &()) -> fmt::Result {
        let c = match self {
            Some(ast::Modifier::Silent) => '_' ,
            None => '$'
        };
        write!(f, "{c}")
    }
}

impl Display for ast::Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use ast::SequenceKind as Kind;
        match self {
            Self::Parenthesized(e)               => write!(f, "({e})"),
            Self::CharRange(a, b)                => write!(f, "'{a}'..'{b}'"),
            Self::String(s)                      => write!(f, "\"{s}\""),
            Self::CaseInsensitive(s)             => write!(f, "^\"{s}\""),
            Self::Rule(Ident(i))                 => write!(f, "{i}"),
            Self::Sequence(Kind::Direct, a, b)   => write!(f, "{a} ~ {b}"),
            Self::Sequence(Kind::Implicit, a, b) => write!(f, "{a} ~ BLANK* ~ {b}"),
            Self::Sequence(Kind::Spaced, a, b)   => write!(f, "{a} ~ BLANK+ ~ {b}"),
            Self::Order(a, b)                    => write!(f, "{a} | {b}"),
            Self::PositivePredicate(p)           => write!(f, "&{p}"),
            Self::NegativePredicate(p)           => write!(f, "!{p}"),
            Self::Optional(e)                    => write!(f, "{e}?"),
            Self::Repetition(e, kind, r)         => {
                match kind {
                    Kind::Direct => write!(f, "{e}")?,
                    Kind::Implicit => write!(f, "({e} ~ BLANK*)")?,
                    Kind::Spaced => write!(f, "({e} ~ BLANK+)")?,
                };
                write!(f, "{r}")
            }
            Self::FuncCall(..) => unreachable!()
        }
    }
}

impl Display for ast::Repetition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroOrMore       => write!(f, "*"),
            Self::OneOrMore        => write!(f, "+"),
            Self::MinMax(min, max) => write!(f, "{{{min}, {max}}}"),
            Self::Max(max)         => write!(f, "{{, {max}}}"),
            Self::Min(min)         => write!(f, "{{{min},}}"),
            Self::Exact(n)         => write!(f, "{{{n}}}"),
        }
    }
}
