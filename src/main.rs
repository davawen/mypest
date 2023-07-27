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

mod ast;
mod process;

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

    let tree = Pest3::parse(Rule::grammar, &src);
    let mut tree = match tree { 
        Ok(t) => t, Err(e) => { println!("{e}"); Err(e)? }
    };

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
