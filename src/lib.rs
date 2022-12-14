use crate::coerce::flatten;
use crate::parse::parse_code;
use crate::util::chunk;
use crate::util::every_nth;
use crate::util::index;
use crate::util::slice;
use crate::util::split;
use crate::util::string_index;
use crate::value::join;
use clap::Parser;
use num::BigInt;
use num::Integer;
use num::One;
use num::Signed;
use num::ToPrimitive;
use num::Zero;
use std::cmp::Ordering;
use std::io::Read;
use std::io::Write;
use std::f64;

use std::collections::HashMap;

mod coerce;
mod parse;
mod unescape;
mod util;
mod value;

use crate::coerce::{coerce, Coerced};
use crate::parse::Gtoken;
use crate::unescape::unescape;
use crate::util::{repeat, set_and, set_or, set_subtract, set_xor};
use crate::value::Gval;

struct Gs {
    pub stack: Vec<Gval>,
    vars: HashMap<Vec<u8>, Gval>,
    lb: Vec<usize>,
    rng_state: u64,
    stable: bool,
    output: String,
    max_loops: u64,
}

impl Gs {
    pub fn new() -> Gs {
        Gs {
            stack: vec![],
            vars: HashMap::new(),
            lb: vec![],
            rng_state: 123456789u64,
            stable: true,
            output: String::new(),
            max_loops: u64::MAX,
        }
    }

    pub fn set_unstable(&mut self) {
        self.stable = false;
    }

    pub fn set_max_loops(&mut self,loops:u64) {
        self.max_loops = loops;
    }

    pub fn print(&mut self,bytes: &[u8]) {
        self.output += &String::from_utf8_lossy(bytes);
    }

    //run is still volitile
    pub fn run(&mut self, code: &[u8]) {
        let (rest, tokens) = parse_code(code).expect("parse error");
        if rest.len() > 0 {
            return;
        }
        // println!("parse: {:?}", tokens);
        let mut tokens = tokens.into_iter();
        while let Some(token) = tokens.next() {
            match token {
                Gtoken::Symbol(b":") => {
                    if let Some(name) = tokens.next() {
                        if let Some(t) = self.top() {
                            let a: Gval = t.clone().into();
                            self.vars.insert(name.lexeme().to_owned(), a);
                        }
                    }
                }
                t => {
                    self.run_token(t);
                }
            }
        }
    }

    fn push(&mut self, val: Gval) {
        self.stack.push(val)
    }

    fn top(&mut self) -> Option<&Gval> {
        self.stack.last()
    }

    fn dup(&mut self) {
        if let Some(a) = self.pop() {
            self.push(a.clone());
            self.push(a);
        } else {
            self.push(Gval::Arr(Vec::<Gval>::new()));
            self.push(Gval::Arr(Vec::<Gval>::new()));
        }
    }

    fn pop(&mut self) -> Option<Gval> {
        let mut i = self.lb.len();
        let mut loops = 0u64;
        while i > 0 && self.lb[i - 1] >= self.stack.len() && loops < self.max_loops {
            loops += 1;
            i -= 1;
            if self.lb[i] > 0 {
                self.lb[i] -= 1;
            }
        }
        let a = self.stack.pop();
        if a.is_some() {
            a
        } else {
            self.set_unstable();
            None
        }
    }

    fn tilde(&mut self) {
        match self.pop() {
            Some(Gval::Int(n)) => self.push(Gval::Int(!n)),
            Some(Gval::Arr(vs)) => self.stack.extend(vs),
            Some(Gval::Str(bs)) => self.run(&bs),
            Some(Gval::Blk(bs)) => self.run(&bs),
            None => self.push(Gval::Arr(Vec::<Gval>::new())),
        }
    }

    fn backtick(&mut self) {
        if let Some(bs) = self.pop() {
            self.push(Gval::Str(bs.inspect()));
        } else {
            self.push(Gval::Str(Vec::<u8>::new()));
        }
    }

    fn bang(&mut self) {
        if let Some(f) = self.pop() {
            self.push(Gval::bool(f.falsey()));
        } else {
            self.push(Gval::bool(true));
        }
    }

    fn at_sign(&mut self) {
        if let Some(c) = self.pop() {
            if let Some(b) = self.pop() {
                if let Some(a) = self.pop() {
                    self.push(b);
                    self.push(c);
                    self.push(a);
                    return;
                }
                self.push(b);
                self.push(c);
                self.push(Gval::Arr(Vec::<Gval>::new()));
                return;
            }
            self.push(Gval::Arr(Vec::<Gval>::new()));
            self.push(c);
            self.push(Gval::Arr(Vec::<Gval>::new()));
            return;
        }
        self.push(Gval::Arr(Vec::<Gval>::new()));
        self.push(Gval::Arr(Vec::<Gval>::new()));
        self.push(Gval::Arr(Vec::<Gval>::new()));
    }

    fn dollar(&mut self) {
        match self.pop() {
            Some(Gval::Int(n)) => {
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
            Some(Gval::Arr(mut vs)) => {
                vs.sort();
                self.push(Gval::Arr(vs));
            }
            Some(Gval::Str(mut bs)) => {
                bs.sort();
                self.push(Gval::Str(bs));
            }
            Some(Gval::Blk(code)) => match self.pop() {
                Some(Gval::Int(n)) => self.push(Gval::Int(n)),
                Some(Gval::Arr(vs)) => {
                    let sorted = self.sort_by(code, vs);
                    self.push(Gval::Arr(sorted));
                }
                Some(Gval::Str(vs)) => {
                    let sorted = self.sort_by(code, vs);
                    self.push(Gval::Str(sorted));
                }
                Some(Gval::Blk(vs)) => {
                    let sorted = self.sort_by(code, vs);
                    self.push(Gval::Blk(sorted));
                }
                None => self.push(Gval::Arr(Vec::<Gval>::new())),
            },
            None => self.push(Gval::Arr(Vec::<Gval>::new())),
        }
    }

    fn sort_by<T: Ord + Clone + Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) -> Vec<T> {
        let mut results: Vec<(Gval, T)> = vec![];
        for v in vs {
            self.push(v.clone().into());
            self.run(&code);
            let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
            results.push((a, v));
        }
        results.sort_by(|a, b| a.0.cmp(&b.0));
        results.into_iter().map(|x| x.1).collect()
    }

    fn plus(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        self.push(a.plus(b));
    }

    fn minus(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        match coerce(a, b) {
            Coerced::Ints(x, y) => self.push(Gval::Int(x - y)),
            Coerced::Arrs(x, y) => self.push(Gval::Arr(set_subtract(x, y))),
            Coerced::Strs(x, y) => self.push(Gval::Str(set_subtract(x, y))),
            Coerced::Blks(x, y) => self.push(Gval::Blk(set_subtract(x, y))),
        }
    }

    fn asterisk(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        use Gval::*;
        match (a, b) {
            // multiply
            (Int(a), Int(b)) => self.push(Int(a * b)),
            // join
            (Arr(a), Arr(sep)) => self.push(join(a, Arr(sep))),
            (Arr(a), Str(sep)) | (Str(sep), Arr(a)) => self.push(join(a, Str(sep))),
            (Str(a), Str(sep)) => {
                let a: Vec<Gval> = a.into_iter().map(|x| Gval::Str(vec![x.into()])).collect();
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
                let mut loops = 0u64;
                while n.is_positive() && loops < self.max_loops {
                    loops += 1;
                    self.run(&f);
                    n -= 1;
                }
            }
        }
    }

    fn slash(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        use Gval::*;
        match (a, b) {
            // divide
            (Int(a), Int(b)) => {
                if b == BigInt::zero() {
                    self.push(Int(BigInt::zero()));
                    return;
                }
                self.push(Int(a.div_floor(&b)))
            }
            // split
            (Arr(a), Arr(sep)) => {
                if sep.len() == 0 {
                    self.push(Arr(a));
                    return;
                }
                let s = split(a, sep, false);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }
            (Str(a), Str(sep)) => {
                if sep.len() == 0 {
                    self.push(Str(a));
                    return;
                }
                let s = split(a, sep, false);
                self.push(Arr(s.into_iter().map(|x| Str(x)).collect()));
            }
            (Arr(a), Str(sep)) | (Str(sep), Arr(a)) => {
                if sep.len() == 0 {
                    self.push(Arr(a));
                    return;
                }
                let s = split(a, sep.into_iter().map(|x| x.into()).collect(), false);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }

            // each
            (Str(a), Blk(code)) | (Blk(code), Str(a)) => self.each(code, a),
            (Arr(a), Blk(code)) | (Blk(code), Arr(a)) => self.each(code, a),

            // chunk
            (Int(n), Arr(mut a)) | (Arr(mut a), Int(n)) => {
                if n == BigInt::zero() {
                    self.push(Arr(a));
                    return;
                }
                let c = chunk(&mut a, n);
                self.push(Arr(c.into_iter().map(|x| Arr(x.to_owned())).collect()));
            }
            (Int(n), Str(mut a)) | (Str(mut a), Int(n)) => {
                if n == BigInt::zero() {
                    self.push(Str(a));
                    return;
                }
                let c = chunk(&mut a, n);
                self.push(Arr(c.into_iter().map(|x| Str(x.to_owned())).collect()));
            }

            // unfold
            (Blk(cond), Blk(step)) => {
                let mut r = vec![];
                let mut loops=0u64;
                loop {
                    if loops>=self.max_loops{break;}
                    loops+=1u64;
                    if let Some(t) = self.top() {
                        let a:Gval = t.clone().into();
                        self.push(a);
                    } else {
                        self.push(Gval::Arr(Vec::<Gval>::new()));
                    }
                    self.run(&cond);

                    if let Some(f) = self.pop() {
                        if  f.falsey() {
                            break;
                        }
                    } else {
                        break;
                    }

                    if let Some(a) = self.top() {
                        r.push(a.clone());
                    } else {
                        r.push(Gval::Arr(Vec::<Gval>::new()));
                    }

                    self.run(&step);
                }
                self.pop();
                self.push(Gval::Arr(r));
            }

            (Blk(code), Int(n)) | (Int(n), Blk(code)) => {
                let a = vec![Gval::Int(n)];
                self.each(code, a)
            }
        }
    }

    fn percent(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        use Gval::*;
        match (a, b) {
            // modulo
            (Int(a), Int(b)) => {
                if b == BigInt::zero() {
                    self.push(Int(BigInt::zero()));
                    return;
                }
                self.push(Int(a.mod_floor(&b)));
            }
            // clean split
            (Arr(a), Arr(sep)) => {
                if sep.len() == 0 {
                    self.push(Arr(a));
                    return;
                }
                let s = split(a, sep, true);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }
            (Str(a), Str(sep)) => {
                if sep.len() == 0 {
                    self.push(Str(a));
                    return;
                }
                let s = split(a, sep, true);
                self.push(Arr(s.into_iter().map(|x| Str(x)).collect()));
            }
            (Arr(a), Str(sep)) | (Str(sep), Arr(a)) => {
                if sep.len() == 0 {
                    self.push(Arr(a));
                    return;
                }
                let s = split(a, sep.into_iter().map(|x| x.into()).collect(), true);
                self.push(Arr(s.into_iter().map(|x| Arr(x)).collect()));
            }

            // map
            (Arr(a), Blk(code)) | (Blk(code), Arr(a)) => {
                let r = self.gs_map(code, a);
                self.push(Arr(r))
            }
            (Str(a), Blk(code)) | (Blk(code), Str(a)) => {
                let r = self.gs_map(code, a);
                self.push(Str(flatten(r)))
            }

            // every nth
            (Int(n), Arr(a)) | (Arr(a), Int(n)) => {
                if n == BigInt::zero() {
                    self.push(Arr(a));
                    return;
                }
                self.push(Arr(every_nth(a, n)));
            }
            (Int(n), Str(a)) | (Str(a), Int(n)) => {
                if n == BigInt::zero() {
                    self.push(Str(a));
                    return;
                }
                self.push(Str(every_nth(a, n)));
            }

            // unimplemented
            (Int(n), Blk(code)) | (Blk(code), Int(n)) => {
                let mut r = vec![Gval::Int(n)];
                r = self.gs_map(code, r);
                self.push(Arr(r));
            }
            (Blk(code_a), Blk(code_b)) => {
                let r = self.gs_map(code_b, vec![Gval::Blk(code_a)]);
                self.push(Arr(r));
            }
        }
    }

    fn vertical_bar(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        self.push(match coerce(a, b) {
            Coerced::Ints(x, y) => Gval::Int(x | y),
            Coerced::Arrs(x, y) => Gval::Arr(set_or(x, y)),
            Coerced::Strs(x, y) => Gval::Str(set_or(x, y)),
            Coerced::Blks(x, y) => Gval::Blk(set_or(x, y)),
        })
    }

    fn ampersand(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        self.push(match coerce(a, b) {
            Coerced::Ints(x, y) => Gval::Int(x & y),
            Coerced::Arrs(x, y) => Gval::Arr(set_and(x, y)),
            Coerced::Strs(x, y) => Gval::Str(set_and(x, y)),
            Coerced::Blks(x, y) => Gval::Blk(set_and(x, y)),
        })
    }

    fn caret(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        self.push(match coerce(a, b) {
            Coerced::Ints(x, y) => Gval::Int(x ^ y),
            Coerced::Arrs(x, y) => Gval::Arr(set_xor(x, y)),
            Coerced::Strs(x, y) => Gval::Str(set_xor(x, y)),
            Coerced::Blks(x, y) => Gval::Blk(set_xor(x, y)),
        })
    }

    fn lteqgt(&mut self, ordering: Ordering) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
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
            Some(Int(n)) => {
                let mut r = vec![];
                let mut i = BigInt::zero();
                let mut loops = 0u64;
                while i < n && loops < self.max_loops {
                    loops+=1;
                    r.push(Int(i.clone()));
                    i += 1i32;
                }
                self.push(Arr(r));
            }
            Some(Arr(a)) => self.push(a.len().into()),
            Some(Str(a)) => self.push(a.len().into()),
            Some(Blk(code)) => match self.pop() {
                Some(Int(n)) => {
                    let a = vec![Int(n)];
                    let r = self.select(code, a);
                    self.push(Arr(r));
                }
                Some(Arr(a)) => {
                    let r = self.select(code, a);
                    self.push(Arr(r))
                }
                Some(Str(a)) => {
                    let r = self.select(code, a);
                    self.push(Str(r))
                }
                Some(Blk(a)) => {
                    let r = self.select(code, a);
                    self.push(Blk(r))
                }
                None => self.push(Gval::Arr(Vec::<Gval>::new())),
            },
            None => self.push(Arr(Vec::<Gval>::new())),
        }
    }

    fn question(&mut self) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        use Gval::*;
        match (a, b) {
            // power
            (Int(a), Int(b)) => self.push(Int(match b.to_u32() {
                Some(e) => if f64::log(f64::from(a.to_i32().unwrap()),10.0)*f64::from(e)<100.0{a.pow(e)}else{a},
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
            (Int(n), Blk(code)) | (Blk(code), Int(n)) => self.find(code, vec![Gval::Int(n)]),
            (Blk(code), Blk(a)) | (Blk(code), Str(a)) | (Str(a), Blk(code)) => self.find(code, a),
            (Blk(code), Arr(a)) | (Arr(a), Blk(code)) => self.find(code, a),
        }
    }

    fn left_paren(&mut self) {
        use Gval::*;
        match self.pop() {
            Some(Int(n)) => self.push(Int(n - 1i32)),
            Some(Arr(a)) => {
                if a.len() > 0 {
                    self.push(Arr(a[1..].to_vec()));
                    self.push(a[0].clone());
                }
            }
            Some(Str(a)) => {
                if a.len() > 0 {
                    self.push(Str(a[1..].to_vec()));
                    self.push(a[0].into());
                }
            }
            Some(Blk(a)) => {
                if a.len() > 0 {
                    self.push(Blk(a[1..].to_vec()));
                    self.push(a[0].into());
                }
            }
            None => {
                let n:BigInt = BigInt::zero();
                self.push(Int(n - 1i32));
            }
        }
    }

    fn right_paren(&mut self) {
        use Gval::*;
        match self.pop() {
            Some(Int(n)) => self.push(Int(n + 1i32)),
            Some(Arr(mut a)) => {
                if a.len() > 0 {
                    let l = a.pop().unwrap();
                    self.push(Arr(a.to_vec()));
                    self.push(l);
                }
            }
            Some(Str(mut a)) => {
                if a.len() > 0 {
                    let l = a.pop().unwrap();
                    self.push(Str(a.to_vec()));
                    self.push(l.into());
                }
            }
            Some(Blk(mut a)) => {
                if a.len() > 0 {
                    let l = a.pop().unwrap();
                    self.push(Blk(a.to_vec()));
                    self.push(l.into());
                }
            }
            None => {
                let n:BigInt = BigInt::zero();
                self.push(Int(n + 1i32));
            }
        }
    }

    fn rng(&mut self) -> u64 {
        let (m, _) = self.rng_state.overflowing_mul(1664525);
        let (m, _) = m.overflowing_add(1013904223);
        self.rng_state = m;
        self.rng_state
    }

    fn rand(&mut self) {
        let r = match self.pop() {
            Some(Gval::Int(n)) if n.is_positive() => self.rng() % n,
            _ => BigInt::zero(),
        };
        self.push(Gval::Int(r));
    }

    fn do_loop(&mut self) {
        if let Some(a) = self.pop() {
            let mut loops = 0u64;
            loop {
                if loops>=self.max_loops{break;}
                loops+=1u64;
                self.go(a.clone());
                if let Some(f) = self.pop() {
                    if f.falsey() {
                        return;
                    }
                } else {
                    return;
                }
            }
        }
    }

    fn while_loop(&mut self, which: bool) {
        let b = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let a = self.pop().or(Some(Gval::Arr(Vec::<Gval>::new()))).unwrap();
        let mut loops = 0u64;
        loop {
            if loops>=self.max_loops{break;}
            loops+=1u64;
            self.go(a.clone());
            if let Some(f) = self.pop() {
                if  f.falsey() == which {
                    break;
                }
            } else {
                if !which {
                    break;
                }
            }
            self.go(b.clone());
        }
    }

    //could be volitile
    fn zip(&mut self) {
        let a = self.pop().unwrap().unwrap_arr();
        let mut r = vec![];
        let blank = a.first().map_or(Gval::Arr(vec![]), |x| x.factory());
        for row in a {
            for (y, elem) in row.as_arr().into_iter().enumerate() {
                let mut loops = 0u64;
                while r.len() < y + 1 && loops < self.max_loops {
                    loops+=1;
                    r.push(blank.clone())
                }
                r[y].push(elem.clone());
            }
        }
        self.push(Gval::Arr(r))
    }

    fn base(&mut self) {
        //Fix this so it doesn't crash on invalid input
        let b = self.pop().unwrap().unwrap_int();
        match self.pop() {
            Some(Gval::Int(n)) => {
                let mut digits = vec![];
                let mut i = n.abs();
                let mut loops = 0u64;
                while !i.is_zero() && loops < self.max_loops {
                    loops+=1;
                    let (j, k) = i.div_mod_floor(&b);
                    i = j;
                    digits.push(Gval::Int(k));
                }
                digits.reverse();
                self.push(Gval::Arr(digits))
            }
            Some(n) => {
                let mut total = BigInt::zero();
                for digit in n.as_arr() {
                    total = total * b.clone() + digit.unwrap_int();
                }
                self.push(Gval::Int(total))
            }
            _ => self.push(Gval::Int(BigInt::zero())),
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

    fn gs_map<T: Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) -> Vec<Gval> {
        let mut r: Vec<Gval> = vec![];
        for v in vs {
            let lb = self.stack.len();
            self.push(v.into());
            self.run(&code);
            r.extend(self.stack.drain(lb..));
        }
        r
    }

    fn select<T: Clone + Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) -> Vec<T> {
        let mut r: Vec<T> = vec![];
        for v in vs {
            self.push(v.clone().into());
            self.run(&code);
            if let Some(t) = self.pop() {
                if t.truthy() {
                    r.push(v);
                }
            }
        }
        r
    }

    fn find<T: Clone + Into<Gval>>(&mut self, code: Vec<u8>, vs: Vec<T>) {
        for v in vs {
            self.push(v.clone().into());
            self.run(&code);
            if let Some(t) = self.pop() {
                if t.truthy() {
                    self.push(v.into());
                    return;
                }
            }
        }
    }

    fn go(&mut self, val: Gval) {
        match val {
            Gval::Blk(s) => self.run(&s),
            _ => self.push(val),
        }
    }

    fn run_token(&mut self, token: Gtoken) {
        if let Some(v) = self.vars.get(token.lexeme()).cloned() {
            self.go(v);
            return;
        }
        match token {
            Gtoken::IntLiteral(bs) => {
                let n = BigInt::parse_bytes(bs, 10).unwrap();
                self.push(Gval::Int(n));
            }
            Gtoken::SingleQuotedString(bs) => self.push(Gval::Str(unescape(bs, true))),
            Gtoken::DoubleQuotedString(bs) => self.push(Gval::Str(unescape(bs, false))),
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
                if let Some(b) = self.pop() {
                    if let Some(a) = self.pop() {
                        self.push(b);
                        self.push(a);
                    } else {
                        self.push(b);
                    }
                }
            }
            Gtoken::Symbol(b";") => {
                let _ = self.pop();
            }
            Gtoken::Symbol(b"<") => self.lteqgt(Ordering::Less),
            Gtoken::Symbol(b"=") => self.lteqgt(Ordering::Equal),
            Gtoken::Symbol(b">") => self.lteqgt(Ordering::Greater),
            Gtoken::Symbol(b",") => self.comma(),
            Gtoken::Symbol(b".") => self.dup(),
            Gtoken::Symbol(b"?") => self.question(),
            Gtoken::Symbol(b"(") => self.left_paren(),
            Gtoken::Symbol(b")") => self.right_paren(),
            Gtoken::Symbol(b"and") => {
                if let Some(b) = self.pop() {
                    if let Some(a) = self.pop() {
                        self.go(if a.truthy() { b } else { a });
                    } else {
                        self.go(b);
                    }
                } else {
                    self.push(Gval::bool(false));
                }
            }
            Gtoken::Symbol(b"or") => {
                if let Some(b) = self.pop() {
                    if let Some(a) = self.pop() {
                        self.go(if a.truthy() { a } else { b });
                    } else {
                        self.go(b);
                    }
                } else { 
                    self.push(Gval::bool(false));
                }
            }
            Gtoken::Symbol(b"xor") => {
                let b = self.pop().or(Some(Gval::bool(false))).unwrap();
                let a = self.pop().or(Some(Gval::bool(false))).unwrap();
                // run a if a and not b run b if b and not a
                self.go(if a.truthy() && b.falsey() { a } else { if a.falsey() && b.truthy() { b } else { Gval::bool(false) } });
            }
            Gtoken::Symbol(b"n") => self.push(Gval::Str(b"\n".to_vec())),
            Gtoken::Symbol(b"print") => {
                if let Some(a) = self.pop() {
                    self.print(&a.to_gs());
                } else {
                    self.print(b"");
                }
            }
            Gtoken::Symbol(b"p") => {
                if let Some(a) = self.pop() {
                    self.print(&a.inspect());
                }
                self.print(b"\n");
            }
            Gtoken::Symbol(b"puts") => {
                if let Some(a) = self.pop() {
                    self.print(&a.to_gs());
                }
                self.print(b"\n");
            }
            Gtoken::Symbol(b"rand") => self.rand(),
            Gtoken::Symbol(b"do") => self.do_loop(),
            Gtoken::Symbol(b"while") => self.while_loop(true),
            Gtoken::Symbol(b"until") => self.while_loop(false),
            Gtoken::Symbol(b"if") => {
                let c = self.pop().or(Some(Gval::bool(false))).unwrap();
                let b = self.pop().or(Some(Gval::bool(false))).unwrap();
                let a = self.pop().or(Some(Gval::bool(false))).unwrap();
                if a.truthy() {
                    self.go(b);
                } else {
                    self.go(c);
                }
            }
            //Pushes popped value back on stack if not int
            Gtoken::Symbol(b"abs") => {
                let a = self.pop().or(Some(Gval::Int(BigInt::zero()))).unwrap();
                if let Gval::Int(n) = a {
                    self.push(Gval::Int(n.abs()));
                } else {
                    self.push(a);
                }
            }
            Gtoken::Symbol(b"zip") => self.zip(),
            Gtoken::Symbol(b"base") => self.base(),
            Gtoken::Block(_, src) => self.push(Gval::Blk(src.to_owned())),
            Gtoken::Symbol(_) => {}
            Gtoken::Comment(_) => {}
        }
    }

    pub fn stepped(&mut self, code: &[u8]) {
        let (rest, tokens) = parse_code(code).expect("parse error");
        if rest.len() > 0 {
            panic!("parse error: has remainder")
        }
        // println!("parse: {:?}", tokens);
        let mut tokens = tokens.into_iter();
        while let Some(token) = tokens.next() {
            match token {
                Gtoken::Symbol(b":") => {
                    let name = tokens.next().expect("parse error: assignment");
                    let t = self.top().unwrap().clone();
                    self.vars.insert(name.lexeme().to_owned(), t);
                }
                t => {
                    self.run_token(t);
                }
            }
        }
    }
}

pub fn golfscript(input:String,source:String) -> String {
    //convert input to vec of byte and pass to Gval::Str
    let input = Gval::Str(input.into_bytes());
    //convert source to vec of bytes
    let source = source.as_bytes().to_vec();
    let mut gs = Gs::new();
    gs.set_max_loops(2000);
    gs.stack.push(input);
    gs.run(&source);

    gs.stack = vec![Gval::Arr(gs.stack)];
    gs.run(b"puts");

    return gs.output;
}
struct Golfscript {
    gs: Gs,
    input: String,
    source: Vec<u8>,
    selected_start: usize,
    selected_end: usize,
}

impl Golfscript {
    fn new(input: String, source: String) -> Self {
        let source = source.as_bytes().to_vec();
        let mut gs = Gs::new();
        gs.stack.push(Gval::Str(input.as_bytes().to_vec()));
        gs.run(&source);
        Self {
            gs,
            input,
            source,
            selected_start: 0,
            selected_end: 0,
        }
    }
    /*fn step(&mut self) {
        self.gs.step(&self.source);
        self.selected += 1;
    }
    fn step_back(&mut self) {
        self.gs.step_back(&self.source);
        self.selected -= 1;
    }
    fn reset(&mut self) {
        self.gs = Gs::new();
        self.gs.stack.push(Gval::Str(self.input.as_bytes().to_vec()));
        self.selected = 0;
    }
    fn run(&mut self) {
        self.gs.run(&self.source);
        self.selected = self.gs.stack.len() - 1;
    }*/
}