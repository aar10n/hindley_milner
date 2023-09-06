use crate::{term, ty};
use crate::{Context, Term, Ty, P};

use std::collections::HashMap;

use internment::Intern;

pub trait ResFn<C, T> = FnMut(&C, Intern<String>) -> Option<T>;

/// An AST node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    /// Term (M)
    Term(P<TermNode>),
    /// Definition (def x = M : A)
    Def(Intern<String>, P<TermNode>, P<TyNode>),
    /// Eager definition (def! x = M : A) (evaluates M)
    DefEager(Intern<String>, P<TermNode>, P<TyNode>),
    /// Equality (M == N)
    Eq(P<TermNode>, P<TermNode>),
    /// Command (:<command> <args>)
    Command(String, String),
}

/// An AST node representing a term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermNode {
    /// Name (x)
    Name(Intern<String>),
    /// Application (M N)
    Apply(P<TermNode>, P<TermNode>),
    /// Lambda abstraction (λx.M)
    Lambda(Intern<String>, P<TermNode>),
}

impl TermNode {
    pub fn convert_with(self, ctx: &Context) -> Term {
        self.convert_into_term(ctx, &mut Vec::new())
    }

    fn convert_into_term(self, ctx: &Context, params: &mut Vec<Intern<String>>) -> Term {
        match self {
            TermNode::Name(x) => {
                if let Some(i) = params.iter().rev().position(|y| *y == x) {
                    let i = params.len() - i - 1;
                    Term::Param(i)
                } else if ctx.defs.contains_key(&x) {
                    Term::Var(x)
                } else {
                    Term::Const(x)
                }
            }
            TermNode::Apply(t1, t2) => Term::Apply(
                t1.convert_into_term(ctx, params).into(),
                t2.convert_into_term(ctx, params).into(),
            ),
            TermNode::Lambda(x, t) => {
                let id = params.len();
                params.push(x);
                let t = t.convert_into_term(ctx, params).into();
                params.pop();
                Term::Lambda(id, t)
            }
        }
    }
}

/// An AST node representing a type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyNode {
    /// Infer type (_)
    Infer,
    /// Unit type (())
    Unit,
    /// Type name (A)
    Name(Intern<String>),
    /// Type application (A B)
    Apply(P<TyNode>, P<TyNode>),
    /// Function type (A -> B)
    Func(P<TyNode>, P<TyNode>),
    /// Product type (A * B)
    Product(P<TyNode>, P<TyNode>),
    /// Universal quantification (∀a.A)
    Forall(Intern<String>, P<TyNode>),
    /// Existential quantification (∃a.A)
    Exists(Intern<String>, P<TyNode>),
}

impl TyNode {
    pub fn convert_with(self, ctx: &Context) -> Ty {
        self.convert_into_ty(ctx, &mut Vec::new())
    }

    fn convert_into_ty(self, ctx: &Context, params: &mut Vec<Intern<String>>) -> Ty {
        match self {
            TyNode::Infer => Ty::Infer,
            TyNode::Unit => Ty::Unit,
            TyNode::Name(x) => {
                if let Some(i) = params.iter().rev().position(|y| *y == x) {
                    let i = params.len() - i - 1;
                    Ty::Param(i)
                } else if ctx.tydefs.contains_key(&x) {
                    Ty::Var(x)
                } else {
                    Ty::Const(x)
                }
            }
            TyNode::Apply(t1, t2) => Ty::Apply(
                t1.convert_into_ty(ctx, params).into(),
                t2.convert_into_ty(ctx, params).into(),
            ),
            TyNode::Func(t1, t2) => Ty::Func(
                t1.convert_into_ty(ctx, params).into(),
                t2.convert_into_ty(ctx, params).into(),
            ),
            TyNode::Product(t1, t2) => Ty::Product(
                t1.convert_into_ty(ctx, params).into(),
                t2.convert_into_ty(ctx, params).into(),
            ),
            TyNode::Forall(x, t) => {
                let id = params.len();
                params.push(x);
                let t = t.convert_into_ty(ctx, params).into();
                params.pop();
                Ty::Forall(id, t)
            }
            TyNode::Exists(x, t) => {
                let id = params.len();
                params.push(x);
                let t = t.convert_into_ty(ctx, params).into();
                params.pop();
                Ty::Exists(id, t)
            }
        }
    }
}
