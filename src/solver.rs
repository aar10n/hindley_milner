use crate::{context::intern, term, ty};
use crate::{Context, Term, Ty, P};

use std::collections::{BTreeMap, HashMap};

use internment::Intern;

pub fn solve(ctx: &Context, e: Term, t: Ty) -> Result<Ty, String> {
    let mut ctx = ctx.clone();
    let tinf = infer(&ctx, e)?;
    unify(&mut ctx, t, tinf)
}

pub fn infer(ctx: &Context, e: Term) -> Result<Ty, String> {
    println!("infer: {}", e.to_string(ctx));
    let mut ctx = ctx.clone();
    match algorithm_j(&mut ctx, e, 0, &mut BTreeMap::new()) {
        Ok(t) => {
            let t = ctx.uf.find(t);
            println!("success context:");
            println!("{}", ctx.uf.to_string(&ctx));
            Ok(t)
        }
        Err(err) => {
            println!("error context:");
            println!("{}", ctx.uf.to_string(&ctx));
            Err(err)
        }
    }
}

fn algorithm_j(
    ctx: &mut Context,
    e: Term,
    l: usize,
    ps: &mut BTreeMap<usize, Intern<String>>,
) -> Result<Ty, String> {
    use Term::*;
    match e {
        Const(x) if x == intern!("_") => Ok(Ty::Unit),
        Const(x) => {
            let v = ctx.new_monotype_var();
            Ok(Ty::Var(x))
            // Err(format!("could not determine type for {}", x))
        }
        Var(x) => {
            let (e, t) = ctx.defs.get(&x).unwrap().clone();
            if t.is_const() {
                return Ok(t);
            }

            let tinf = algorithm_j(ctx, e, l, ps)?;
            let t = ty::inst(ctx, t);
            let t = unify(ctx, t, tinf)?;
            println!("[var] {} : {}", x, t.to_string(ctx),);
            Ok(t)
        }
        Param(x) => {
            let t = Ty::Var(*ps.get(&x).unwrap());
            println!("[par] ${} : {}", x, t.to_string(ctx));
            Ok(t)
        }
        Apply(e1, e2) => {
            println!("[app] {} {}", e1.to_string(ctx), e2.to_string(ctx));
            let t1 = algorithm_j(ctx, *e1.clone(), l, ps)?;
            let t2 = algorithm_j(ctx, *e2.clone(), l, ps)?;
            let t1s = t1.to_string(ctx);

            let v = ctx.new_monotype_var();
            let t1 = unify(
                ctx,
                t1.into(),
                Ty::Func(t2.clone().into(), Ty::Var(v).into()),
            )?;
            println!(
                "      {} : {} | {} : {}",
                e1.to_string(ctx),
                t1s,
                e2.to_string(ctx),
                t2.to_string(ctx),
            );
            println!(
                "      {} : {} | {} : {} | {} : {}",
                e1.to_string(ctx),
                t1.to_string(ctx),
                e2.to_string(ctx),
                t2.to_string(ctx),
                v,
                Ty::Var(v).to_string(ctx)
            );
            Ok(Ty::Var(v))
        }
        Lambda(x, e) => {
            let v = ctx.new_monotype_var();
            println!("[lam] ${} : {} -> {}", x, v, e.to_string(ctx));
            ps.insert(x, v);
            let rt = algorithm_j(ctx, *e.clone(), l + 1, ps)?;
            ps.remove(&x);
            println!(
                "[lam] ${} : {} | {} : {}",
                x,
                v,
                e.to_string(ctx),
                rt.to_string(ctx)
            );

            let pt = ctx.uf.find(Ty::Var(v));
            Ok(Ty::Func(pt.into(), rt.into()))
        }
    }
}

fn unify(ctx: &mut Context, t1: Ty, t2: Ty) -> Result<Ty, String> {
    use Ty::*;
    // println!("-> unify({}, {})", t1.to_string(ctx), t2.to_string(ctx));
    match (t1.clone(), t2.clone()) {
        (Infer, t2) => Ok(t2),
        (t1, Infer) => Ok(t1),
        (Unit, Unit) => Ok(Unit),
        (Const(x), Const(y)) if x == y => Ok(Const(x)),
        (Param(x), Param(y)) if x == y => Ok(Param(x)),
        (Var(x), Var(y)) => {
            ctx.uf.union(Ty::Var(x), Ty::Var(y));
            Ok(Ty::Var(x))
        }
        (Var(x), t2) if ctx.is_monotype_var(x) => {
            let t2 = ctx.uf.find(t2);
            occurs_check(ctx, &Ty::Var(x), &t2)?;
            // println!(
            //     "====== union({}, {})",
            //     t2.to_string(&Context::new()),
            //     Ty::Var(x).to_string(&Context::new())
            // );
            ctx.uf.union(t2.clone(), Ty::Var(x));
            // print!("{}", ctx.uf.to_string(ctx));
            Ok(t2)
        }
        (t1, Var(y)) if ctx.is_monotype_var(y) => {
            let t1 = ctx.uf.find(t1);
            occurs_check(ctx, &Ty::Var(y), &t1)?;
            // println!(
            //     "====== union({}, {})",
            //     t1.to_string(&Context::new()),
            //     Ty::Var(y).to_string(&Context::new()),
            // );
            ctx.uf.union(t1.clone(), Ty::Var(y));
            // print!("{}", ctx.uf.to_string(ctx));
            Ok(t1)
        }
        (Apply(t1, t2), Apply(t3, t4)) => {
            let t1 = unify(ctx, *t1, *t3)?;
            let t2 = unify(ctx, *t2, *t4)?;
            Ok(Apply(t1.into(), t2.into()))
        }
        (Func(t1, t2), Func(t3, t4)) => {
            let t1 = unify(ctx, *t1, *t3)?;
            let t2 = unify(ctx, *t2, *t4)?;
            Ok(Func(t1.into(), t2.into()))
        }
        (Product(t1, t2), Product(t3, t4)) => {
            let t1 = unify(ctx, *t1, *t3)?;
            let t2 = unify(ctx, *t2, *t4)?;
            Ok(Product(t1.into(), t2.into()))
        }
        (Record(fields), Record(fields2)) => {
            let mut fields3 = BTreeMap::new();
            for (k, v) in fields {
                let v = fields2.get(&k).ok_or_else(|| {
                    format!(
                        "expected field `{}` in record type `{}`",
                        k,
                        t2.to_string(ctx)
                    )
                })?;
                fields3.insert(k, v.clone());
            }
            Ok(Record(fields3))
        }
        (Forall(x, t1), Forall(y, t2)) => {
            let t1 = unify(ctx, *t1, *t2)?;
            Ok(Forall(x, t1.into()))
        }
        (Exists(x, t1), Exists(y, t2)) => {
            let t1 = unify(ctx, *t1, *t2)?;
            Ok(Exists(x, t1.into()))
        }
        _ => Err(format!(
            "expected type `{}`, found `{}`",
            t1.to_string(ctx),
            t2.to_string(ctx)
        )),
    }
}

/// Check that `x` does not occur in `t` (to avoid recursive types).
fn occurs_check(ctx: &Context, x: &Ty, t: &Ty) -> Result<(), String> {
    use Ty::*;
    match t {
        Var(y) if x == &Var(*y) => Err(format!("recursive type `{}`", x.to_string(ctx))),
        Apply(t1, t2) => {
            occurs_check(ctx, x, t1)?;
            occurs_check(ctx, x, t2)
        }
        Func(t1, t2) => {
            occurs_check(ctx, x, t1)?;
            occurs_check(ctx, x, t2)
        }
        Product(t1, t2) => {
            occurs_check(ctx, x, t1)?;
            occurs_check(ctx, x, t2)
        }
        Record(fields) => {
            for (_, t) in fields {
                occurs_check(ctx, x, t)?;
            }
            Ok(())
        }
        Forall(_, t) => occurs_check(ctx, x, t),
        Exists(_, t) => occurs_check(ctx, x, t),
        _ => Ok(()),
    }
}
