use pest::{ Parser, error::Error as PestError };
use pest_derive::Parser;

mod ast;
mod process;
mod generate;
mod custom_format;

trait ExpectIterator<T>: Iterator<Item = T> {
    /// Expects that a value is in this iterator, panics otherwise
    fn expect(&mut self) -> T {
        self.next().unwrap()
    }
}

#[derive(Parser)]
#[grammar = "my_pest.pest"]
pub struct MyPest;

pub enum PreprocessError {
    Pest(Box<PestError<Rule>>),
    MissingRule {
        has_whitespace: bool,
        has_comment: bool
    },
    BlankRedefinition
}

impl From<PestError<Rule>> for PreprocessError {
    fn from(value: PestError<Rule>) -> Self {
        PreprocessError::Pest(Box::new(value))
    }
}

impl std::error::Error for PreprocessError {}

impl std::fmt::Display for PreprocessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Pest(p) => writeln!(f, "{p}"),
            &Self::MissingRule { has_whitespace, has_comment } => {
                write!(f, "missing implementation for rule ")?;
                if !has_whitespace { write!(f, "`WHITESPACE`")? }
                if !has_whitespace && !has_comment { write!(f, " and ")? }
                if !has_comment { write!(f, "`COMMENT`")? }
                writeln!(f)
            }
            Self::BlankRedefinition => writeln!(f, "redefining built-in `BLANK` rule.")
        }
    }
}

impl std::fmt::Debug for PreprocessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

pub fn preprocess(src: &str) -> Result<String, PreprocessError> {
    let mut tree = MyPest::parse(Rule::grammar, src)?;

    let mut grammar = ast::parse(tree.expect());

    let has_whitespace = grammar.rules.iter().any(|r| r.name.0 == "WHITESPACE");
    let has_comment = grammar.rules.iter().any(|r| r.name.0 == "COMMENT");
    if !has_whitespace || !has_comment {
        return Err(PreprocessError::MissingRule { has_whitespace, has_comment })
    }

    if grammar.rules.iter().any(|r| r.name.0 == "BLANK") {
        return Err(PreprocessError::BlankRedefinition)
    }

    grammar.rules.push(ast::AstRule {
        name: ast::Ident("BLANK".to_owned()),
        docs: vec![],
        modifier: Some(ast::Modifier::Silent),
        expr: ast::Expr::Order(
            Box::new(ast::Expr::Rule(ast::Ident("WHITESPACE".to_owned()))),
            Box::new(ast::Expr::Rule(ast::Ident("COMMENT".to_owned())))
        )
    });
    
    for rule in &mut grammar.rules {
        process::expand_calls(rule, &grammar.funcs);
    }

    Ok(format!("{grammar}"))
}
