use crate::{term, ty, Term, Ty};

use std::collections::HashMap;
use std::io;

use internment::Intern;

macro_rules! intern {
    ($s:literal) => {
        Intern::new($s.to_string())
    };
    ($e:expr) => {
        Intern::new($e)
    };
}
pub(crate) use intern;

#[derive(Clone, Debug)]
pub struct Context {
    /// Map from names to definitions.
    pub defs: HashMap<Intern<String>, (Term, Ty)>,
    /// Map from type names to definitions.
    pub tydefs: HashMap<Intern<String>, Ty>,
    /// Map from term expressions to a list of names.
    pub names: HashMap<Term, Vec<Intern<String>>>,

    /// The current type context.
    pub typings: HashMap<Intern<String>, Ty>,
    /// Union-find structure used during type solving.
    pub uf: UnionFind,
    /// Next monotype variable to be allocated.
    next_mono: usize,
}

impl Context {
    pub fn new() -> Self {
        Self {
            defs: HashMap::new(),
            tydefs: HashMap::new(),
            names: HashMap::new(),
            typings: HashMap::new(),
            uf: UnionFind::new(),
            next_mono: 0,
        }
    }

    pub fn common_names<'a>(&self, t: &Term) -> Option<Vec<&str>> {
        Some(
            self.names
                .get(t)?
                .iter()
                .map(|x| x.as_str())
                .collect::<Vec<_>>(),
        )
    }

    /// Allocates a new unique type name for a monotype and registers it in the type context.
    pub fn new_monotype_var(&mut self) -> Intern<String> {
        let t = nth_monotype_var(self.next_mono);
        self.typings.insert(t.clone(), Ty::Infer);
        self.uf.insert(Ty::Var(t));
        self.next_mono += 1;
        t
    }

    /// Returns an iterator over all allocated monotype variable names.
    pub fn iter_monotype_vars(&self) -> impl Iterator<Item = Intern<String>> {
        (0..self.next_mono).into_iter().map(|n| nth_monotype_var(n))
    }

    /// Returns whether the given string is a monotype variable.
    pub fn is_monotype_var(&self, x: Intern<String>) -> bool {
        self.iter_monotype_vars().any(|y| x == y)
    }
}

#[derive(Clone, Debug)]
pub struct UnionFind {
    parent: Vec<usize>,
    size: Vec<usize>,
    ty_keys: HashMap<Ty, usize>,
    key_tys: HashMap<usize, Ty>,
}

impl UnionFind {
    pub fn new() -> Self {
        Self {
            parent: Vec::new(),
            size: Vec::new(),
            ty_keys: HashMap::new(),
            key_tys: HashMap::new(),
        }
    }

    pub fn insert(&mut self, t: Ty) {
        self.create_key(t);
    }

    pub fn find(&mut self, t: Ty) -> Ty {
        let (_, t) = self.find_or_create(t);
        t
    }

    pub fn union(&mut self, t1: Ty, t2: Ty) {
        let (k1, t1) = self.find_or_create(t1);
        let (k2, t2) = self.find_or_create(t2);
        if k1 == k2 {
            return;
        }

        self.parent[k2] = k1;
        self.size[k1] += self.size[k2];
    }

    pub fn iter_class(&self, p: &Ty) -> impl Iterator<Item = Ty> + '_ {
        let k = *self.ty_keys.get(p).unwrap();
        self.key_tys
            .iter()
            .filter(move |(_, t)| self.parent[self.ty_keys[*t]] == k)
            .map(|(_, t)| t.clone())
    }

    pub fn to_string(&self, ctx: &Context) -> String {
        let mut buf = Vec::new();
        self.write(&mut buf, ctx).unwrap();
        String::from_utf8(buf).unwrap()
    }

    fn find_or_create(&mut self, t: Ty) -> (usize, Ty) {
        let k = self.get_or_create_key(t);
        let p = self.parent[k];
        if p == k {
            (p, self.key_tys[&k].clone())
        } else {
            let t = self.find(self.key_tys[&p].clone());
            self.parent[k] = self.ty_keys[&t];
            (k, t)
        }
    }

    fn get_or_create_key(&mut self, t: Ty) -> usize {
        if let Some(k) = self.ty_keys.get(&t) {
            *k
        } else {
            self.create_key(t)
        }
    }

    fn create_key(&mut self, t: Ty) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        self.size.push(1);
        self.ty_keys.insert(t.clone(), id);
        self.key_tys.insert(id, t);
        id
    }

    fn write<W: io::Write>(&self, f: &mut W, ctx: &Context) -> io::Result<()> {
        writeln!(f, "------------------------------");
        for k in 0..self.parent.len() {
            if self.size[k] == 1 {
                continue;
            }
            // write the representative for the key, followed by all members of the equivalence class
            let parent = &self.key_tys[&k];
            let children = self
                .iter_class(&self.key_tys[&k])
                .filter_map(|t| {
                    if t != *parent {
                        Some(t.to_string(ctx))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            writeln!(
                f,
                "[{}] {}: {}",
                self.size[k],
                parent.to_string(ctx),
                children.join(" | ")
            );
        }
        writeln!(f, "------------------------------")?;
        Ok(())
    }
}

fn nth_monotype_var(mut n: usize) -> Intern<String> {
    let var = "t";
    let digits = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];
    // let var = "𝜏";
    // let digits = ["₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"];
    let mut s = String::new();
    while n > 0 {
        s.push_str(digits[n % 10]);
        n /= 10;
    }
    let s = s.chars().rev().collect::<String>();
    intern!(format!("{}{}", var, s))
}
