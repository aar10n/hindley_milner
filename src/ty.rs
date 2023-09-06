use crate::{Context, Term, P};

use std::collections::BTreeMap;
use std::fmt;
use std::io;

use internment::Intern;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// Inferrable type
    Infer,
    /// Unit type
    Unit,
    /// Type constant (int)
    Const(Intern<String>),
    /// Free type name (X)
    Var(Intern<String>),
    /// Bound type parameter (a)
    Param(usize),
    /// Type application (A B)
    Apply(P<Ty>, P<Ty>),
    /// Function type (A -> B)
    Func(P<Ty>, P<Ty>),
    /// Product type (A * B)
    Product(P<Ty>, P<Ty>),
    /// Record type ({ a: A, b: B })
    Record(BTreeMap<Intern<String>, Ty>),
    /// Universal quantification (∀a.A)
    Forall(usize, P<Ty>),
    /// Existential quantification (∃a.A)
    Exists(usize, P<Ty>),
}

impl Ty {
    pub fn is_const(&self) -> bool {
        matches!(self, Ty::Const(_))
    }

    /// Returns `true` if the type has no quantifiers and is not a bound parameter.
    pub fn is_monotype(&self) -> bool {
        use Ty::*;
        match self {
            Param(_) => false,
            Apply(t1, t2) => t1.is_monotype() && t2.is_monotype(),
            Func(t1, t2) => t1.is_monotype() && t2.is_monotype(),
            Product(t1, t2) => t1.is_monotype() && t2.is_monotype(),
            Record(fields) => fields.values().all(|t| t.is_monotype()),
            Forall(_, _) => false,
            Exists(_, _) => false,
            _ => true,
        }
    }

    /// Returns `true` if the type contains any quantifiers.
    pub fn is_polytype(&self) -> bool {
        use Ty::*;
        match self {
            Apply(t1, t2) => t1.is_polytype() || t2.is_polytype(),
            Func(t1, t2) => t1.is_polytype() || t2.is_polytype(),
            Product(t1, t2) => t1.is_polytype() || t2.is_polytype(),
            Record(fields) => fields.values().any(|t| t.is_polytype()),
            Forall(_, _) => true,
            Exists(_, _) => true,
            _ => false,
        }
    }

    pub fn to_string(&self, ctx: &Context) -> String {
        let mut buf = Vec::new();
        format(ctx, self, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }
}

/// Instantiate all quantifiers in `t` with new monotype variables.
pub fn inst(ctx: &mut Context, t: Ty) -> Ty {
    let mut t = t;
    while t.is_polytype() {
        t = lift_qual(ctx, t);
        t = inst_qual(ctx, t);
    }
    t
}

/// Instantiates a quantifier in `t` with a new monotype variable.
fn inst_qual(ctx: &mut Context, t: Ty) -> Ty {
    use Ty::*;
    match t {
        Forall(x, t) => {
            let name = ctx.new_monotype_var();
            subst(ctx, &Var(name), x, *t)
        }
        Exists(x, t) => {
            let name = ctx.new_monotype_var();
            subst(ctx, &Var(name), x, *t)
        }
        _ => t,
    }
}

/// Lifts a possibly nested qualifier in `t` to the top of the type.
fn lift_qual(ctx: &Context, t: Ty) -> Ty {
    use Ty::*;
    match t {
        Apply(t1, t2) => match lift_qual(ctx, *t1) {
            Forall(x, t) => Forall(x, Apply(t.into(), t2).into()),
            Exists(x, t) => Exists(x, Apply(t.into(), t2).into()),
            t1 @ _ => Apply(t1.into(), t2),
        },
        Func(t1, t2) => match lift_qual(ctx, *t1) {
            Forall(x, t) => Forall(x, Func(t.into(), t2).into()),
            Exists(x, t) => Exists(x, Func(t.into(), t2).into()),
            t1 @ _ => Func(t1.into(), t2.into()),
        },
        Product(t1, t2) => match lift_qual(ctx, *t1) {
            Forall(x, t) => Forall(x, Product(t.into(), t2).into()),
            Exists(x, t) => Exists(x, Product(t.into(), t2).into()),
            t1 @ _ => Product(t1.into(), t2.into()),
        },
        Record(fields) => Record(
            fields
                .into_iter()
                .map(|(key, v)| (key, lift_qual(ctx, v).into()))
                .collect(),
        ),
        _ => t,
    }
}

/// Substitute `r` for `x` in `t` shifting other parameters down by 1.
fn subst(ctx: &Context, r: &Ty, x: usize, t: Ty) -> Ty {
    use Ty::*;
    match t {
        Param(y) if y == x => r.clone(),
        Param(y) => Param(y - 1),
        Apply(t1, t2) => Apply(subst(ctx, r, x, *t1).into(), subst(ctx, r, x, *t2).into()),
        Func(t1, t2) => Func(subst(ctx, r, x, *t1).into(), subst(ctx, r, x, *t2).into()),
        Product(t1, t2) => Product(subst(ctx, r, x, *t1).into(), subst(ctx, r, x, *t2).into()),
        Record(fields) => Record(
            fields
                .into_iter()
                .map(|(k, v)| (k, subst(ctx, r, x, v).into()))
                .collect(),
        ),
        Forall(y, t) => Forall(y - 1, subst(ctx, r, x, *t).into()),
        Exists(y, t) => Exists(y - 1, subst(ctx, r, x, *t).into()),
        _ => t,
    }
}

/// Writes a formatted representation of a type to the given writer.
fn format(ctx: &Context, t: &Ty, w: &mut impl io::Write) -> io::Result<()> {
    use Ty::*;
    match t {
        Infer => write!(w, "_"),
        Unit => write!(w, "()"),
        Const(x) => write!(w, "'{}", x),
        Param(x) => write!(w, "{}", index_to_ident(*x)),
        Var(x) => write!(w, "{}", x),
        Apply(t1, t2) => {
            write!(w, "(")?;
            if matches!(**t1, Func(_, _)) {
                write!(w, "(")?;
                format(ctx, t1, w)?;
                write!(w, ")")?;
            } else {
                format(ctx, t1, w)?;
            }
            write!(w, " ")?;
            format(ctx, t2, w)?;
            write!(w, ")")
        }
        Func(t1, t2) => {
            let b = matches!(**t2, Func(_, _));
            write!(w, "{}", if b { "(" } else { "" });
            format(ctx, t1, w)?;
            write!(w, "{}", if b { ")" } else { "" });
            write!(w, " -> ")?;
            format(ctx, t2, w)
        }
        Product(t1, t2) => {
            write!(w, "(")?;
            format(ctx, t1, w)?;
            write!(w, " * ")?;
            format(ctx, t2, w)?;
            write!(w, ")")
        }
        Record(fields) => {
            write!(w, "⟨")?;
            let mut first = true;
            for (k, v) in fields {
                if first {
                    first = false;
                } else {
                    write!(w, ", ")?;
                }
                write!(w, "{}: ", k)?;
                format(ctx, v, w)?;
            }
            write!(w, "⟩")
        }
        Forall(x, t) => {
            // write!(w, "(∀{}.", index_to_ident(*x))?;
            format(ctx, t, w)?;
            // write!(w, ")")
            Ok(())
        }
        Exists(x, t) => {
            // write!(w, "(∃{}.", index_to_ident(*x))?;
            format(ctx, t, w)?;
            // write!(w, ")")
            Ok(())
        }
    }
}

/// maps integer to a lowercase identifier `a`, `b`, `c`, ...
fn index_to_ident(i: usize) -> Intern<String> {
    Intern::new(((b'a' + (i % 26) as u8) as char).to_string())
}
