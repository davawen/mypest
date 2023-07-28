use std::collections::HashMap;

use crate::ast::{self, Expr};

pub fn expand_calls(expr: &mut Expr, funcs: &HashMap<String, ast::Func>) {
    match expr {
        Expr::FuncCall(f, args) => {
            *expr = expand_func(args, &funcs[&f.0], funcs);
        }
        Expr::Parenthesized(e)
        | Expr::PositivePredicate(e)
        | Expr::NegativePredicate(e)
        | Expr::Optional(e)
        | Expr::Repetition(e, _, _) => expand_calls(e, funcs),
        Expr::Sequence(_, a, b) | Expr::Order(a, b) => {
            expand_calls(a, funcs);
            expand_calls(b, funcs);
        }
        Expr::CharRange(_, _) | Expr::String(_) | Expr::CaseInsensitive(_) | Expr::Rule(_) => (),
    }
}

fn expand_func(args: &Vec<Expr>, func: &ast::Func, funcs: &HashMap<String, ast::Func>) -> Expr {
    let mut expr = func.expr.clone();
    expand_func_expr(&mut expr, args, func, funcs);
    Expr::Parenthesized(Box::new(expr))
}

fn expand_func_expr(expr: &mut Expr, args: &Vec<Expr>, func: &ast::Func, funcs: &HashMap<String, ast::Func>) {
    match expr {
        Expr::Rule(i) => if let Some(idx) = func.params.iter().position(|p| p.0 == i.0) {
            *expr = args[idx].clone();
        }
        Expr::FuncCall(f, args) => {
            *expr = expand_func(args, &funcs[&f.0], funcs);
        }
        Expr::Parenthesized(e)
        | Expr::PositivePredicate(e)
        | Expr::NegativePredicate(e)
        | Expr::Optional(e)
        | Expr::Repetition(e, _, _) => expand_func_expr(e, args, func, funcs),
        Expr::Sequence(_, a, b) | Expr::Order(a, b) => {
            expand_func_expr(a, args, func, funcs);
            expand_func_expr(b, args, func, funcs);
        }
        Expr::CharRange(_, _) | Expr::String(_) | Expr::CaseInsensitive(_) => (),
    }
}
