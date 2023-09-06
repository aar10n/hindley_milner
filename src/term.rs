use crate::reduce::StepResult;
use crate::{Context, P};

use std::fmt;
use std::io;

use internment::Intern;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    /// Constant (name)
    Const(Intern<String>),
    /// Free variable (name)
    Var(Intern<String>),
    /// Bound parameter (de Bruijn level)
    Param(usize),
    /// Application
    Apply(P<Term>, P<Term>),
    /// Lambda abstraction
    Lambda(usize, P<Term>),
}

impl Term {
    pub fn is_const(&self) -> bool {
        matches!(self, Term::Const(_))
    }

    pub fn to_string(&self, ctx: &Context) -> String {
        let mut buf = Vec::new();
        format(ctx, self, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }
}

/// Reduces a term using normal order reduction.
pub fn reduce(ctx: &Context, t: Term) -> Term {
    nor(ctx, t, 0)
}

/// Expands all free variables in a term and reduces it.
pub fn reduce_all(ctx: &Context, t: Term) -> Term {
    expand(ctx, t, 0, nor)
}

/// Reduces a single step of the term using normal order reduction.
pub fn reduce_step(ctx: &Context, t: Term) -> (Term, bool) {
    let (t, r) = nor_step(ctx, t, 0, 1);
    (t, r == 0)
}

/// Substitute `r` for `x` in `e`.
fn subst(ctx: &Context, r: &Term, x: usize, e: Term) -> Term {
    use Term::*;
    let e = match e {
        Param(y) if y == x => r.clone(),
        Apply(e1, e2) => Apply(subst(ctx, r, x, *e1).into(), subst(ctx, r, x, *e2).into()),
        Lambda(y, e) => Lambda(y, subst(ctx, r, x, *e).into()),
        _ => e,
    };
    e
}

/// Shift all parameters in `e` greater or equal to `c` by `k`
fn shift(ctx: &Context, e: Term, c: usize, k: isize) -> Term {
    use Term::*;
    match e {
        Param(x) if x >= c => Param((x as isize + k) as usize),
        Apply(e1, e2) => Apply(shift(ctx, *e1, c, k).into(), shift(ctx, *e2, c, k).into()),
        Lambda(x, e) => Lambda((x as isize + k) as usize, shift(ctx, *e, c, k).into()),
        _ => e,
    }
}

/// Reduces a term using a reduction function while expanding all free variables.
fn expand(
    ctx: &Context,
    t: Term,
    l: usize,
    reduce_fn: impl Fn(&Context, Term, usize) -> Term + Copy,
) -> Term {
    use Term::*;
    match reduce_fn(ctx, t, l) {
        Var(x) => {
            let (e, _) = ctx.defs.get(&x).unwrap().clone();
            expand(ctx, e, l, reduce_fn)
        }
        Apply(e1, e2) => Apply(
            expand(ctx, *e1, l, reduce_fn).into(),
            expand(ctx, *e2, l, reduce_fn).into(),
        ),
        Lambda(x, e) => Lambda(x, expand(ctx, *e, l + 1, reduce_fn).into()),
        e @ _ => reduce_fn(ctx, e, l),
    }
}

/// Call-by-name reduction reduces the leftmost outermost redex first.
fn cbn(ctx: &Context, t: Term, l: usize) -> Term {
    use Term::*;
    match t {
        Apply(e1, e2) => match cbn(ctx, *e1, l) {
            Var(y) => {
                let (e1, _) = ctx.defs.get(&y).unwrap().clone();
                let e1 = shift(ctx, e1, 0, l as isize);
                cbn(ctx, Apply(cbn(ctx, e1, l).into(), e2), l)
            }
            Lambda(x, e) => {
                let e = shift(ctx, subst(ctx, &e2, x, *e), l, -1);
                cbn(ctx, e, l)
            }
            e1 @ _ => Apply(e1.into(), e2),
        },
        _ => t,
    }
}

/// Stepped Call-by-name reduction.
fn cbn_step(ctx: &Context, t: Term, l: usize, steps: usize) -> (Term, usize) {
    use Term::*;
    if steps == 0 {
        return (t, 0);
    }

    match t {
        Apply(e1, e2) => {
            let (e1, steps) = cbn_step(ctx, *e1, l, steps);
            if steps == 0 {
                return (Apply(e1.into(), e2), 0);
            }

            match e1 {
                Var(y) => {
                    let (e1, _) = ctx.defs.get(&y).unwrap().clone();
                    let e1 = shift(ctx, e1, 0, l as isize);
                    cbn_step(ctx, Apply(e1.into(), e2), l, steps - 1)
                }
                Lambda(x, e) => {
                    let e = shift(ctx, subst(ctx, &e2, x, *e), l, -1);
                    cbn_step(ctx, e, l, steps - 1)
                }
                e1 @ _ => {
                    let (e1, steps) = cbn_step(ctx, e1, l, steps);
                    let (e2, steps) = cbn_step(ctx, *e2, l, steps);
                    (Apply(e1.into(), e2.into()), steps)
                }
            }
        }
        _ => (t, steps),
    }
}

/// Normal order reduction reduces the leftmost outermost redex first.
fn nor(ctx: &Context, t: Term, l: usize) -> Term {
    use Term::*;
    match t {
        Apply(e1, e2) => match cbn(ctx, *e1, l) {
            Var(y) => {
                let (e1, _) = ctx.defs.get(&y).unwrap().clone();
                let e1 = shift(ctx, e1, 0, l as isize);
                nor(ctx, Apply(nor(ctx, e1, l).into(), e2), l)
            }
            Lambda(x, e) => {
                let e = shift(ctx, subst(ctx, &e2, x, *e), l, -1);
                nor(ctx, e, l)
            }
            e1 @ _ => Apply(nor(ctx, e1, l).into(), nor(ctx, *e2, l).into()),
        },
        Lambda(x, e) => Lambda(x, nor(ctx, *e, l + 1).into()),
        _ => t,
    }
}

/// Stepped normal order reduction.
fn nor_step(ctx: &Context, t: Term, l: usize, steps: usize) -> (Term, usize) {
    use Term::*;
    if steps == 0 {
        return (t, 0);
    }

    match t {
        Apply(e1, e2) => {
            let (e1, steps) = cbn_step(ctx, *e1, l, steps);
            if steps == 0 {
                return (Apply(e1.into(), e2), 0);
            }

            match e1 {
                Var(y) => {
                    let (e1, _) = ctx.defs.get(&y).unwrap().clone();
                    let e1 = shift(ctx, e1, 0, l as isize);
                    nor_step(ctx, Apply(e1.into(), e2), l, steps - 1)
                }
                Lambda(x, e) => {
                    let e = shift(ctx, subst(ctx, &e2, x, *e), l, -1);
                    nor_step(ctx, e, l, steps - 1)
                }
                e1 @ _ => {
                    let (e1, steps) = nor_step(ctx, e1, l, steps);
                    let (e2, steps) = nor_step(ctx, *e2, l, steps);
                    (Apply(e1.into(), e2.into()), steps)
                }
            }
        }
        Lambda(x, e) => {
            let (e, steps) = nor_step(ctx, *e, l + 1, steps);
            (Lambda(x, e.into()), steps)
        }
        _ => (t, steps),
    }
}

/// Writes a formatted representation of a term to the given writer.
fn format(ctx: &Context, t: &Term, w: &mut impl std::io::Write) -> io::Result<()> {
    match t {
        Term::Const(x) => write!(w, "'{}", x),
        Term::Var(x) => write!(w, "{}", x),
        Term::Param(x) => write!(w, "${}", x),
        Term::Apply(e1, e2) => {
            write!(w, "(")?;
            format(ctx, e1, w)?;
            write!(w, " ")?;
            format(ctx, e2, w)?;
            write!(w, ")")
        }
        Term::Lambda(x, e) => {
            write!(w, "(λ{}.", x)?;
            format(ctx, e, w)?;
            write!(w, ")")
        }
    }
}
