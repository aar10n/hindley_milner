#![feature(trait_alias)]
#![feature(try_trait_v2)]
#![allow(warnings)]
mod ast;
mod context;
mod parser;
mod reduce;
mod solver;
mod term;
mod ty;

use context::Context;
use term::Term;
use ty::Ty;

use std::collections::HashMap;
use std::fmt::format;
use std::io::Read;
use std::process;

use atty::Stream;
use clap::Parser;
use internment::Intern;
use rustyline::error::ReadlineError;
use rustyline::{Cmd, DefaultEditor, EventHandler, KeyCode, KeyEvent, Modifiers};

pub type P<T> = Box<T>;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, help = "Evaluate the given expression")]
    expr: Vec<String>,

    #[arg(short, long, help = "Evaluate the given files")]
    file: Vec<String>,

    #[arg(short, long, help = "Run in interactive mode")]
    interactive: bool,
}

fn main() {
    let args = Args::parse();

    // collect all sources
    let mut interactive = args.interactive;
    let mut sources = Vec::new();
    if atty::is(Stream::Stdin) {
        interactive = true;
    } else {
        sources.push(read_from_stdin());
    }
    if !args.file.is_empty() {
        for path in args.file {
            sources.push(read_from_file(&path));
        }
    }
    if !args.expr.is_empty() {
        sources.push(args.expr.join("\n"));
    }

    // evalulate static sources
    let mut ctx = Context::new();
    for source in sources.into_iter() {
        execute(&mut ctx, &source, true);
    }
    if interactive {
        repl_main(ctx, execute);
    }
}

fn execute(ctx: &mut Context, source: &str, exit: bool) {
    match parser::parse_nodes(&source) {
        Ok(nodes) => {
            for node in nodes.into_iter() {
                use ast::Node;
                match node {
                    Node::Term(e) => {
                        let e = e.convert_with(ctx);
                        let e = term::reduce(ctx, e);
                        println!("--> {}", e.to_string(ctx));
                        let names = match ctx.common_names(&e) {
                            Some(names) => names,
                            None => continue,
                        };
                        println!("also known as: {}", names.join(", "));
                    }
                    Node::Def(id, e, t) => {
                        let e = e.convert_with(ctx);
                        let t = match t.convert_with(ctx) {
                            Ty::Infer => match solver::infer(ctx, e.clone()) {
                                Ok(t) => t,
                                Err(err) => {
                                    println!("error: {:?}", err);
                                    continue;
                                }
                            },
                            t => t,
                        };

                        let e = term::reduce_all(ctx, e);
                        ctx.defs.insert(id, (e.clone(), t));
                        ctx.names.entry(e).or_default().push(id);
                    }
                    Node::DefEager(id, e, t) => {
                        let e = e.convert_with(ctx);
                        let e = term::reduce(ctx, e);
                        let t = match t.convert_with(ctx) {
                            Ty::Infer => match solver::infer(ctx, e.clone()) {
                                Ok(t) => t,
                                Err(err) => {
                                    println!("error: {:?}", err);
                                    continue;
                                }
                            },
                            t => t,
                        };
                        ctx.defs.insert(id, (e, t));
                    }
                    Node::Eq(e1, e2) => {
                        let e1 = e1.convert_with(ctx);
                        let e1 = term::reduce_all(ctx, e1);
                        let e2 = e2.convert_with(ctx);
                        let e2 = term::reduce_all(ctx, e2);
                        println!("--> {}", e1 == e2);
                    }
                    Node::Command(name, args_str) => {
                        if let Err(err) = eval_command(ctx, &name, &args_str) {
                            println!("error: {:?}", err);
                            if exit {
                                std::process::exit(1);
                            }
                        }
                    }
                    _ => continue,
                }
            }
        }
        Err(err) => {
            eprintln!("error: {:?}", err);
            if exit {
                std::process::exit(1);
            }
        }
    }
}

fn eval_command(ctx: &mut Context, name: &str, rest: &str) -> Result<(), String> {
    match name {
        "s" | "show" => {
            let e = parser::parse_term(ctx, rest)?;
            let e = term::reduce_all(ctx, e);
            println!("--> {}", e.to_string(ctx));
            println!("{:?}", e);
        }
        "d" | "showdef" => match parser::parse_term(ctx, rest)? {
            Term::Var(x) => {
                let (e, t) = ctx.defs.get(&x).unwrap().clone();
                println!("--> {}", e.to_string(ctx));
                if t != Ty::Unit {
                    println!(": {}", t.to_string(ctx));
                }
            }
            e @ _ => println!("--> {}", e.to_string(ctx)),
        },
        "t" | "typeof" => {
            let e = parser::parse_term(ctx, rest)?;
            match solver::infer(ctx, e) {
                Ok(t) => {
                    println!("--> {}", t.to_string(ctx));
                }
                Err(err) => {
                    println!("error: {:?}", err);
                }
            }
        }
        "st" | "steps" => {
            let e = parser::parse_term(ctx, rest)?;
            let e = reduce::each_step(ctx, e, term::reduce_step, |ctx, e| {
                println!("--> {}", e.to_string(ctx));
            });
            println!("--> {}", e.to_string(ctx));
        }
        "p" | "prove" => {
            let (e, t) = parser::parse_typed_term(ctx, rest)?;
            match solver::solve(ctx, e.clone(), t) {
                Ok(t) => {
                    println!("--> {} : {}", e.to_string(ctx), t.to_string(ctx));
                    println!("--> true");
                }
                Err(err) => println!("--> false ({})", err),
            }
        }
        "union" => match parser::parse_ty(ctx, rest)? {
            Ty::Apply(t1, t2) => {
                ctx.uf.union(*t1, *t2);
                println!("{}", ctx.uf.to_string(ctx));
            }
            _ => {
                println!("error: expected t1 t2");
            }
        },
        "find" => {
            let t = parser::parse_ty(ctx, rest)?;
            let t = ctx.uf.find(t);
            println!("--> {}", t.to_string(ctx));
        }
        _ => return Err(format!("unknown command: {}", name)),
    }
    Ok(())
}

fn repl_main<C>(ctx: C, mut execute: impl FnMut(&mut C, &str, bool)) {
    let mut rl = DefaultEditor::new().unwrap();
    _ = rl.load_history("target/history.txt");
    rl.bind_sequence(
        KeyEvent(KeyCode::Tab, Modifiers::NONE),
        EventHandler::Simple(Cmd::Insert(1, "  ".into())),
    );
    rl.bind_sequence(
        KeyEvent(KeyCode::Char('N'), Modifiers::CTRL),
        EventHandler::Simple(Cmd::Newline),
    );

    let mut ctx = ctx;
    loop {
        let readline = rl.readline(">> ");
        match readline {
            Ok(line) => {
                execute(&mut ctx, line.as_str(), false);
                rl.add_history_entry(line).unwrap();
            }
            Err(ReadlineError::Interrupted) => {
                println!("ctrl-c");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("ctrl-d");
                break;
            }
            Err(err) => {
                eprintln!("error: {:?}", err);
                break;
            }
        }
    }

    _ = rl.save_history("target/history.txt");
}

fn read_from_file(path: &str) -> String {
    match std::fs::read_to_string(path) {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error: {:?}", err);
            std::process::exit(1)
        }
    }
}

fn read_from_stdin() -> String {
    let mut code = String::new();
    match std::io::stdin().read_to_string(&mut code) {
        Ok(_) => code,
        Err(err) => {
            eprintln!("error: {:?}", err);
            process::exit(1);
        }
    }
}
