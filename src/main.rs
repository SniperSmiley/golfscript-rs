use crate::util::chunk;
use crate::util::every_nth;
use crate::util::index;
use crate::util::slice;
use crate::util::string_index;
use crate::value::join;
use crate::value::split;
use clap::Parser;
use num::BigInt;
use num::One;
use num::Signed;
use num::ToPrimitive;
use num::Zero;
use std::cmp::Ordering;

use std::collections::HashMap;
use std::str;

mod coerce;
mod parse;
mod util;
mod value;

use crate::coerce::{coerce, Coerced};
use crate::parse::Gtoken;
use crate::util::{repeat, set_and, set_or, set_subtract, set_xor};
use crate::value::Gval;

struct Gs {
    pub stack: Vec<Gval>,
    vars: HashMap<Vec<u8>, Gval>,
    lb: Vec<usize>,
    parse_cache: HashMap<Vec<u8>, Vec<Gtoken>>,
}

impl Gs {
    pub fn new() -> Gs {
        let mut vars = HashMap::new();
        vars.insert(b"n".to_vec(), Gval::Str(b"\n".to_vec()));
        Gs {
            stack: vec![],
            vars,
            lb: vec![],
        }
    }

    pub fn run(&mut self, code: &[u8]) {
        let (rest, tokens) = parse::parse_code(code).expect("parse error");
        if rest.len() > 0 {
            panic!("parse error: has remainder")
        }
        // println!("parse: {:?}", tokens);
        let mut tokens = tokens.into_iter();
        while let Some(token) = tokens.next() {
            match token {
                Gtoken::Symbol(b":") => {
                    let name = tokens.next().expect("parse error: assignment");
                    let t = self.top().clone();
                    self.vars.insert(name.lexeme().to_owned(), t);
                }
                t => {
                    self.run_builtin(t);
                }
            }
        }
    }

    fn push(&mut self, val: Gval) {
        self.stack.push(val)
    }

    fn top(&self) -> &Gval {
        self.stack.last().expect("stack underflow")
    }

    fn pop(&mut self) -> Gval {
        let mut i = self.lb.len();
        while i > 0 && self.lb[i - 1] < self.stack.len() {
            i -= 1;
            self.lb[i] -= 1;
        }
        self.stack.pop().expect("stack underflow")
    }

    fn tilde(&mut self) {
        match self.pop() {
            Gval::Int(n) => self.push(Gval::Int(!n)),
            Gval::Arr(vs) => self.stack.extend(vs),
            Gval::Str(bs) => self.run(&bs),
            Gval::Blk(bs) => self.run(&bs),
        }
    }

    fn backtick(&mut self) {
        let bs = self.pop().inspect();
        self.push(Gval::Str(bs))
    }

    fn bang(&mut self) {
        let f = self.pop().falsey();
        self.push(Gval::Int(if f { BigInt::one() } else { BigInt::zero() }));
    }

    fn at_sign(&mut self) {
        let c = self.pop();
        let b = self.pop();
        let a = self.pop();
        self.push(b);
        self.push(c);
        self.push(a);
    }

    fn dollar(&mut self) {
        match self.pop() {
            Gval::Int(n) => {
                let len: BigInt = self.stack.len().into();
                if n < (-1i32).into() {
                    if let Some(i) = (-n - 2i32).to_usize() {
                        if i < self.stack.len() {
                            self.push(self.stack[i].clone());
                        }
                    }
                } else if n >= 0i32.into() && n < len {
                    if let Some(i) = (len - 1i32 - n).to_usize() {
                        self.push(self.stack[i].clone());
                    }
                }
            }
            Gval::Arr(mut vs) => {
                vs.sort();
                self.push(Gval::Arr(vs));
            }
            Gval::Str(mut bs) => {
                bs.sort();
                self.push(Gval::Str(bs));
            }
            Gval::Blk(code) => match self.pop() {
                Gval::Int(_) => panic!("can't sort an integer"),
                Gval::Arr(vs) => {
                    let sorted = self.sort_by(code, vs);
                    self.push(Gval::Arr(sorted));
                }
                Gval::Str(vs) => {
                    let sorted = self.sort_by(code, vs);
                    self.push(Gval::Str(sorted));
                }
                Gval::Blk(vs) => {
                    let sorted = self.sort_by(code, vs);
                    self.push(Gval::Blk(sorted));
                }
            },
        }
    }

    fn sort_by<T: Ord + Clone + Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) -> Vec<T> {
        let mut results: Vec<(Gval, T)> = vec![];
        for v in vs {
            self.push(v.clone().into());
            self.run(&code);
            results.push((self.pop(), v));
        }
        results.sort_by(|a, b| a.0.cmp(&b.0));
        results.into_iter().map(|x| x.1).collect()
    }

    fn plus(&mut self) {
        let b = self.pop();
        let a = self.pop();
        self.push(a.plus(b));
    }

    fn minus(&mut self) {
        let b = self.pop();
        let a = self.pop();
        match coerce(a, b) {
            Coerced::Ints(x, y) => self.push(Gval::Int(x - y)),
            Coerced::Arrs(x, y) => self.push(Gval::Arr(set_subtract(x, y))),
            Coerced::Strs(x, y) => self.push(Gval::Str(set_subtract(x, y))),
            Coerced::Blks(x, y) => self.push(Gval::Blk(set_subtract(x, y))),
        }
    }

    fn asterisk(&mut self) {
        let b = self.pop();
        let a = self.pop();
        use Gval::*;
        match (a, b) {
            // multiply
            (Int(a), Int(b)) => self.push(Int(a * b)),
            // join
            (Arr(a), Arr(sep)) => self.push(join(a, Arr(sep))),
            (Str(a), Str(sep)) => {
                let a: Vec<Gval> = a.into_iter().map(|x| Gval::Str(vec![x.into()])).collect();
                self.push(join(a, Str(sep)));
            }
            (Arr(a), Str(sep)) | (Str(sep), Arr(a)) => {
                self.push(join(a, Str(sep)));
            }

            // fold
            (Blk(code), Blk(a)) | (Str(a), Blk(code)) | (Blk(code), Str(a)) => self.fold(code, a),
            (Arr(a), Blk(code)) | (Blk(code), Arr(a)) => self.fold(code, a),

            // repeat
            (Int(n), Arr(a)) | (Arr(a), Int(n)) => self.push(Arr(repeat(a, n))),
            (Int(n), Str(a)) | (Str(a), Int(n)) => self.push(Str(repeat(a, n))),

            // times
            (Int(mut n), Blk(f)) | (Blk(f), Int(mut n)) => {
                while n.is_positive() {
                    self.run(&f);
                    n -= BigInt::one();
                }
            }
        }
    }

    fn slash(&mut self) {
        let b = self.pop();
        let a = self.pop();
        use Gval::*;
        match (a, b) {
            // divide
            (Int(a), Int(b)) => self.push(Int(a / b)),
            // split
            (Arr(a), Arr(sep)) => {
                let s = split(a, sep, false);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }
            (Str(a), Str(sep)) => {
                let s = split(a, sep, false);
                self.push(Arr(s.into_iter().map(|x| Str(x)).collect()));
            }
            (Arr(a), Str(sep)) | (Str(sep), Arr(a)) => {
                let s = split(a, sep.into_iter().map(|x| x.into()).collect(), false);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }

            // each
            (Str(a), Blk(code)) | (Blk(code), Str(a)) => self.each(code, a),
            (Arr(a), Blk(code)) | (Blk(code), Arr(a)) => self.each(code, a),

            // chunk
            (Int(n), Arr(mut a)) | (Arr(mut a), Int(n)) => {
                let c = chunk(&mut a, n);
                self.push(Arr(c.into_iter().map(|x| Arr(x.to_owned())).collect()));
            }
            (Int(n), Str(mut a)) | (Str(mut a), Int(n)) => {
                let c = chunk(&mut a, n);
                self.push(Arr(c.into_iter().map(|x| Str(x.to_owned())).collect()));
            }

            // unfold
            (Blk(_), Blk(_)) => {
                todo!("unfold")
            }

            (Blk(_), Int(_)) | (Int(_), Blk(_)) => {
                panic!("int-block /")
            }
        }
    }

    fn percent(&mut self) {
        let b = self.pop();
        let a = self.pop();
        use Gval::*;
        match (a, b) {
            // modulo
            (Int(a), Int(b)) => self.push(Int(a % b)),
            // clean split
            (Arr(a), Arr(sep)) => {
                let s = split(a, sep, true);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }
            (Str(a), Str(sep)) => {
                let s = split(a, sep, true);
                self.push(Arr(s.into_iter().map(|x| Str(x)).collect()));
            }
            (Arr(a), Str(sep)) | (Str(sep), Arr(a)) => {
                let s = split(a, sep.into_iter().map(|x| x.into()).collect(), true);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }

            // map
            (Arr(a), Blk(code)) | (Blk(code), Arr(a)) => {
                let r = self.gs_map(code, a);
                self.push(r)
            }
            (Str(a), Blk(code)) | (Blk(code), Str(a)) => {
                let r = self.gs_map(code, a);
                self.push(Str(r.to_gs()));
            }

            // every nth
            (Int(n), Arr(a)) | (Arr(a), Int(n)) => self.push(Arr(every_nth(a, n))),
            (Int(n), Str(a)) | (Str(a), Int(n)) => self.push(Str(every_nth(a, n))),

            // unimplemented
            (Int(_), Blk(_)) | (Blk(_), Int(_)) | (Blk(_), Blk(_)) => panic!("%"),
        }
    }

    fn vertical_bar(&mut self) {
        let b = self.pop();
        let a = self.pop();
        self.push(match coerce(a, b) {
            Coerced::Ints(x, y) => Gval::Int(x | y),
            Coerced::Arrs(x, y) => Gval::Arr(set_or(x, y)),
            Coerced::Strs(x, y) => Gval::Str(set_or(x, y)),
            Coerced::Blks(x, y) => Gval::Blk(set_or(x, y)),
        })
    }

    fn ampersand(&mut self) {
        let b = self.pop();
        let a = self.pop();
        self.push(match coerce(a, b) {
            Coerced::Ints(x, y) => Gval::Int(x & y),
            Coerced::Arrs(x, y) => Gval::Arr(set_and(x, y)),
            Coerced::Strs(x, y) => Gval::Str(set_and(x, y)),
            Coerced::Blks(x, y) => Gval::Blk(set_and(x, y)),
        })
    }

    fn caret(&mut self) {
        let b = self.pop();
        let a = self.pop();
        self.push(match coerce(a, b) {
            Coerced::Ints(x, y) => Gval::Int(x ^ y),
            Coerced::Arrs(x, y) => Gval::Arr(set_xor(x, y)),
            Coerced::Strs(x, y) => Gval::Str(set_xor(x, y)),
            Coerced::Blks(x, y) => Gval::Blk(set_xor(x, y)),
        })
    }

    fn lteqgt(&mut self, ordering: Ordering) {
        let b = self.pop();
        let a = self.pop();
        use Gval::*;
        use Ordering::*;
        match (ordering, a, b) {
            (Equal, Int(i), Arr(a)) | (Equal, Arr(a), Int(i)) => {
                index(&a, i).map(|x| self.push(x.clone()));
            }
            (Equal, Int(i), Str(a))
            | (Equal, Str(a), Int(i))
            | (Equal, Int(i), Blk(a))
            | (Equal, Blk(a), Int(i)) => {
                index(&a, i).map(|x| self.push(x.clone().into()));
            }
            (o, Int(i), Arr(a)) | (o, Arr(a), Int(i)) => self.push(Arr(slice(o, a, i))),
            (o, Int(i), Str(a)) | (o, Str(a), Int(i)) => self.push(Str(slice(o, a, i))),
            (o, Int(i), Blk(a)) | (o, Blk(a), Int(i)) => self.push(Blk(slice(o, a, i))),
            (o, x, y) => self.push(Gval::bool(x.cmp(&y) == o)),
        }
    }

    fn comma(&mut self) {
        use Gval::*;
        match self.pop() {
            Int(n) => {
                let mut r = vec![];
                let mut i = BigInt::zero();
                while i < n {
                    r.push(Int(i.clone()));
                    i += 1i32;
                }
                self.push(Arr(r));
            }
            Arr(a) => self.push(a.len().into()),
            Str(a) => self.push(a.len().into()),
            Blk(code) => match self.pop() {
                Int(_) => panic!("select on integer"),
                Arr(a) => {
                    let r = self.select(code, a);
                    self.push(Arr(r))
                }
                Str(a) => {
                    let r = self.select(code, a);
                    self.push(Str(r))
                }
                Blk(a) => {
                    let r = self.select(code, a);
                    self.push(Blk(r))
                }
            },
        }
    }

    fn question(&mut self) {
        let b = self.pop();
        let a = self.pop();
        use Gval::*;
        match (a, b) {
            // power
            (Int(a), Int(b)) => self.push(Int(match b.to_u32() {
                Some(e) => a.pow(e),
                None => BigInt::zero(),
            })),

            // indexof
            (Arr(h), n @ Int(_))
            | (n @ Int(_), Arr(h))
            | (Arr(h), n @ Str(_))
            | (n @ Str(_), Arr(h))
            | (Arr(h), n @ Arr(_)) => self.push(Gval::Int(
                h.iter()
                    .position(|x| *x == n)
                    .map_or(-BigInt::one(), BigInt::from),
            )),
            (Str(h), Int(n)) | (Int(n), Str(h)) => self.push(Gval::Int(match n.to_u8() {
                None => -BigInt::one(),
                Some(b) => h
                    .iter()
                    .position(|x| *x == b)
                    .map_or(-BigInt::one(), BigInt::from),
            })),
            (Str(h), Str(n)) => self.push(Gval::Int(string_index(&h, &n))),

            // find
            (Int(_), Blk(_)) | (Blk(_), Int(_)) => panic!(),
            (Blk(code), Blk(a)) | (Blk(code), Str(a)) | (Str(a), Blk(code)) => self.find(code, a),
            (Blk(code), Arr(a)) | (Arr(a), Blk(code)) => self.find(code, a),
        }
    }

    fn left_paren(&mut self) {
        use Gval::*;
        match self.pop() {
            Int(n) => self.push(Int(n - 1i32)),
            Arr(a) => {
                self.push(Arr(a[1..].to_vec()));
                self.push(a[0].clone());
            }
            Str(a) => {
                self.push(Str(a[1..].to_vec()));
                self.push(a[0].into());
            }
            Blk(a) => {
                self.push(Blk(a[1..].to_vec()));
                self.push(a[0].into());
            }
        }
    }

    fn right_paren(&mut self) {
        use Gval::*;
        match self.pop() {
            Int(n) => self.push(Int(n + 1i32)),
            Arr(mut a) => {
                let l = a.pop().unwrap();
                self.push(Arr(a.to_vec()));
                self.push(l);
            }
            Str(mut a) => {
                let l = a.pop().unwrap();
                self.push(Str(a.to_vec()));
                self.push(l.into());
            }
            Blk(mut a) => {
                let l = a.pop().unwrap();
                self.push(Blk(a.to_vec()));
                self.push(l.into());
            }
        }
    }

    fn fold<T: Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) {
        for (i, v) in vs.into_iter().enumerate() {
            self.push(v.into());
            if i >= 1 {
                self.run(&code);
            }
        }
    }

    fn each<T: Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) {
        for v in vs {
            self.push(v.into());
            self.run(&code);
        }
    }

    fn gs_map<T: Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) -> Gval {
        let mut r: Vec<Gval> = vec![];
        for v in vs {
            let lb = self.stack.len();
            self.push(v.into());
            self.run(&code);
            r.extend(self.stack.drain(lb..));
        }
        Gval::Arr(r)
    }

    fn select<T: Clone + Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) -> Vec<T> {
        let mut r: Vec<T> = vec![];
        for v in vs {
            self.push(v.clone().into());
            self.run(&code);
            if !self.pop().falsey() {
                r.push(v)
            }
        }
        r
    }

    fn find<T: Clone + Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) {
        for v in vs {
            self.push(v.clone().into());
            self.run(&code);
            if !self.pop().falsey() {
                self.push(v.into());
                break;
            }
        }
    }

    fn go(&mut self, val: Gval) {
        match val {
            Gval::Blk(s) => self.run(&s),
            _ => self.push(val),
        }
    }

    fn run_builtin(&mut self, token: Gtoken) {
        if matches!(token, Gtoken::Symbol(_)) {
            if let Some(v) = self.vars.get(token.lexeme()) {
                let w = v.clone();
                self.go(w);
            }
        }
        match token {
            Gtoken::IntLiteral(bs) => {
                let n = BigInt::parse_bytes(bs, 10).unwrap();
                self.push(Gval::Int(n));
            }
            Gtoken::SingleQuotedString(bs) | Gtoken::DoubleQuotedString(bs) => {
                // TODO: string escapes
                self.push(Gval::Str(bs[1..bs.len() - 1].to_owned()))
            }
            Gtoken::Symbol(b"~") => self.tilde(),
            Gtoken::Symbol(b"`") => self.backtick(),
            Gtoken::Symbol(b"!") => self.bang(),
            Gtoken::Symbol(b"@") => self.at_sign(),
            Gtoken::Symbol(b"$") => self.dollar(),
            Gtoken::Symbol(b"+") => self.plus(),
            Gtoken::Symbol(b"-") => self.minus(),
            Gtoken::Symbol(b"*") => self.asterisk(),
            Gtoken::Symbol(b"/") => self.slash(),
            Gtoken::Symbol(b"%") => self.percent(),
            Gtoken::Symbol(b"|") => self.vertical_bar(),
            Gtoken::Symbol(b"&") => self.ampersand(),
            Gtoken::Symbol(b"^") => self.caret(),
            Gtoken::Symbol(b"[") => self.lb.push(self.stack.len()),
            Gtoken::Symbol(b"]") => {
                let vs = self.stack.drain(self.lb.pop().unwrap_or(0)..).collect();
                self.push(Gval::Arr(vs));
            }
            Gtoken::Symbol(b"\\") => {
                let b = self.pop();
                let a = self.pop();
                self.push(b);
                self.push(a);
            }
            Gtoken::Symbol(b";") => {
                let _ = self.pop();
            }
            Gtoken::Symbol(b"<") => self.lteqgt(Ordering::Less),
            Gtoken::Symbol(b"=") => self.lteqgt(Ordering::Equal),
            Gtoken::Symbol(b">") => self.lteqgt(Ordering::Greater),
            Gtoken::Symbol(b",") => self.comma(),
            Gtoken::Symbol(b".") => self.push(self.top().clone()),
            Gtoken::Symbol(b"?") => self.question(),
            Gtoken::Symbol(b"(") => self.left_paren(),
            Gtoken::Symbol(b")") => self.right_paren(),
            Gtoken::Symbol(b"or") => {
                let b = self.pop();
                let a = self.pop();
                self.push(if a.falsey() { b } else { a });
            }
            Gtoken::Block(_, src) => self.push(Gval::Blk(src.to_owned())),
            Gtoken::Symbol(_) => {}
            t => todo!("builtin {}", str::from_utf8(t.lexeme()).unwrap()),
        }
    }
}

#[derive(clap::Parser, Debug)]
struct Cli {
    code: String,
}

fn main() {
    let p = Cli::parse();
    let mut gs = Gs::new();
    gs.run(p.code.as_bytes());
    // for g in gs.stack {
    //     print!("{} ", str::from_utf8(&g.inspect()).unwrap());
    // }
    println!("{}", str::from_utf8(&Gval::Arr(gs.stack).to_gs()).unwrap());
    println!();
}
