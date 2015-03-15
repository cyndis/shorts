#![feature(plugin)]
#![plugin(peg_syntax_ext)]

use std::collections::HashSet;
use std::fmt;
use std::num::SignedInt;

mod dimacs;

#[derive(Debug)]
pub struct Clause {
    pub t: HashSet<u32>,
    pub f: HashSet<u32>
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let mut cs = vec![];
        for &var in &self.t {
            cs.push(var as i32);
        }
        for &var in &self.f {
            cs.push(-(var as i32));
        }
        cs.sort_by(|a,b| a.abs().cmp(&b.abs()));

        for (i, &v) in cs.iter().enumerate() {
            if i > 0 {
                try!(write!(f, " ∨ "));
            }
            if v < 0 {
                try!(write!(f, "¬"));
            }
            try!(write!(f, "{}", v.abs()));
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct Problem {
    pub clauses: Vec<Clause>
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for (i, clause) in self.clauses.iter().enumerate() {
            if i > 0 {
                try!(write!(f, " ∧ "));
            }
            try!(write!(f, "({})", clause));
        }

        Ok(())
    }
}

fn main() {
    let mut args = std::env::args();

    let path = args.nth(1).unwrap();

    match dimacs::load_problem(&path) {
        Ok(p) => println!("Ok!\n{}", p),
        Err(e) => println!("{}", e)
    }
}
