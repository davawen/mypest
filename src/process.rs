use std::collections::HashMap;

use crate::ast::{self, Expr};

pub fn expand_calls(rule: &mut ast::AstRule, funcs: &HashMap<String, ast::Func>) {
    expand_call_expr(&mut rule.expr, None, funcs);
}

#[derive(Clone, Copy)]
struct Call<'a> {
    args: &'a Vec<Expr>,
    func: &'a ast::Func
}

fn expand_func(call: Call, funcs: &HashMap<String, ast::Func>) -> Expr {
    let mut expr = call.func.expr.clone();
    expand_call_expr(&mut expr, Some(call), funcs);
    Expr::Parenthesized(Box::new(expr))
}

fn expand_call_expr(expr: &mut Expr, call: Option<Call>, funcs: &HashMap<String, ast::Func>) {
    match expr {
        Expr::Rule(i) => if let Some(call) = call {
            if let Some(idx) = call.func.params.iter().position(|p| p.0 == i.0) {
                *expr = call.args[idx].clone();
            }
        }
        Expr::FuncCall(f, args) => {
            // expand arguments in case you have function calls as arguments
            for arg in args.iter_mut() {
                expand_call_expr(arg, call, funcs);
            }

            *expr = expand_func(Call { args, func: &funcs[&f.0] }, funcs);
        }
        Expr::Parenthesized(e)
        | Expr::PositivePredicate(e)
        | Expr::NegativePredicate(e)
        | Expr::Optional(e)
        | Expr::Repetition(e, _, _) => expand_call_expr(e, call, funcs),
        Expr::Sequence(_, a, b) | Expr::Order(a, b) => {
            expand_call_expr(a, call, funcs);
            expand_call_expr(b, call, funcs);
        }
        Expr::CharRange(_, _) | Expr::String(_) | Expr::CaseInsensitive(_) => (),
    }
}
