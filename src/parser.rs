use crate::ast::{Node, TermNode, TyNode};
use crate::context::Context;
use crate::term::Term;
use crate::ty::Ty;
use crate::P;

use internment::Intern;

peg::parser! {
    grammar parser() for str {
        rule whitespace() = quiet!{[' ' | '\t']}
        rule line_end() = quiet!{['\r' | '\n']}
        rule comment() = quiet!{"#" (!line_end() [_])*}
        rule eol() = quiet!{whitespace()* comment()? line_end()}

        rule _ = quiet!{whitespace()*}
        rule __ = quiet!{whitespace()+}

        rule number() -> usize = quiet!{x:$(['0'..='9']+) { usize::from_str_radix(x, 10).unwrap() }}

        rule subscript() -> char = ['₀'|'₁'|'₂'|'₃'|'₄'|'₅'|'₆'|'₇'|'₈'|'₉']

        rule ident() -> Intern<String> = quiet!{
            x:$((['a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '\''] / subscript())+) { Intern::new(x.to_string()) }
        }

        rule params<T>(r: rule<T>) -> Vec<T> =
            "[" ps:((_ p:r() _ {p}) ++ ",") "]." {ps} /
            p:r() "." { vec![p] }

        #[cache_left_rec]
        pub rule term_node() -> P<TermNode> = precedence!{
            s:position!() n:@ e:position!() { P::new(n) }
            --
            // application
            x:(@) _ y:@ { TermNode::Apply(x, y) }
            // abstraction
            ['λ'|'\\'] _ xs:params(<ident()>) _ t:term_node() {
                xs.into_iter().rev().fold(*t, |t, x| TermNode::Lambda(x, t.into()))
            }
            // name
            x:ident() { TermNode::Name(x) }
            // parentheses
            "(" _ n:term_node() _ ")" { *n }
        }

        #[cache_left_rec]
        pub rule ty_node() -> P<TyNode> = precedence!{
            s:position!() n:@ e:position!() { P::new(n) }
            --
            // type application
            a:(@) _ b:@ { TyNode::Apply(a, b) }
            --
            // universal quantification
            "∀" _ xs:params(<ident()>) _ t:ty_node() {
                xs.into_iter().rev().fold(*t, |t, x| TyNode::Forall(x, t.into()))
            }
            // existential quantification
            "∃" _ xs:params(<ident()>) _ t:ty_node() {
                xs.into_iter().rev().fold(*t, |t, x| TyNode::Exists(x, t.into()))
            }
            // product type
            a:(@) _ "*" _ b:@ { TyNode::Product(a, b) }
            // product type (n-tuple)
            "(" _ x:ty_node() _ "," _ xs:((_ x:ty_node() _ {x}) ++ ",") _ ")" {
                xs.into_iter().fold(*x, |x, y| TyNode::Product(x.into(), y))
            }
            --
            // function type
            a:(@) _ "->" _ b:@ { TyNode::Func(a, b) }
            // type name
            x:ident() { TyNode::Name(x) }
            // unit type
            "()" { TyNode::Unit }
            // infer type
            "_" { TyNode::Infer }
            // parentheses
            "(" _ n:ty_node() _ ")" { *n }
        }

        pub rule typed_term() -> (P<TermNode>, P<TyNode>) =
            e:term_node() __ t:(":" _ t:ty_node() {t})? {
                (e, t.unwrap_or_else(|| TyNode::Infer.into()))
            }

        pub rule node() -> Node =
            // definition
            "def" __ id:ident() _ "=" _ e:term_node() _ t:(":" _ t:ty_node() {t})? {
                Node::Def(id, e.into(), t.unwrap_or_else(|| TyNode::Infer.into()).into())
            } /
            // eager definition
            "edef" __ id:ident() _ "=" _ et:typed_term() {
                let (e, t) = et;
                Node::DefEager(id, e, t)
            } /
            // command
            ":" _ c:$(['a'..='z'|'_']+) __ rest:$((!eol() c:[_] {c})+) {
                Node::Command(c.to_owned(), rest.to_owned())
            } /
            // term or equality
            e:term_node() _ o:("==" _ t:term_node() {t})? {
                if let Some(t) = o {
                    Node::Eq(e.into(), t.into())
                } else {
                    Node::Term(e.into())
                }
            }

        pub rule nodes() -> Vec<Node> =
            ns:(_ n:node()? {n})** eol() { ns.into_iter().filter_map(|n| n).collect() }
    }
}

pub fn parse_typed_term(ctx: &Context, s: &str) -> Result<(Term, Ty), String> {
    match parser::typed_term(s) {
        Ok((node, ty)) => Ok(((*node).convert_with(ctx), (*ty).convert_with(ctx))),
        Err(err) => {
            let offset = err.location.offset;
            let expected: Vec<&str> = err.expected.tokens().collect();
            let expected = expected.join(" or ");
            Err(format!(
                "syntax error: invalid expression: expected {} at offset {}",
                expected, offset
            ))
        }
    }
}

pub fn parse_term(ctx: &Context, s: &str) -> Result<Term, String> {
    match parser::term_node(s) {
        Ok(node) => Ok((*node).convert_with(ctx)),
        Err(err) => {
            let offset = err.location.offset;
            let expected: Vec<&str> = err.expected.tokens().collect();
            let expected = expected.join(" or ");
            Err(format!(
                "syntax error: invalid term: expected {} at offset {}",
                expected, offset
            ))
        }
    }
}

pub fn parse_ty(ctx: &Context, s: &str) -> Result<Ty, String> {
    match parser::ty_node(s) {
        Ok(node) => Ok((*node).convert_with(ctx)),
        Err(err) => {
            let offset = err.location.offset;
            let expected: Vec<&str> = err.expected.tokens().collect();
            let expected = expected.join(" or ");
            Err(format!(
                "syntax error: invalid type: expected {} at offset {}",
                expected, offset
            ))
        }
    }
}

pub fn parse_nodes(s: &str) -> Result<Vec<Node>, String> {
    match parser::nodes(s) {
        Ok(nodes) => Ok(nodes),
        Err(err) => {
            let offset = err.location.offset;
            let expected: Vec<&str> = err.expected.tokens().collect();
            let expected = expected.join(" or ");
            Err(format!(
                "syntax error: expected {} at offset {}",
                expected, offset
            ))
        }
    }
}
