#![feature(plugin, core, collections, std_misc)]
#![plugin(peg_syntax_ext)]

use std::collections::HashSet;
use std::fmt;
use std::num::SignedInt;

mod dimacs;
mod naive;

#[derive(Debug)]
/// Disjunctive clause.
pub struct Clause {
    pub t: HashSet<u32>,
    pub f: HashSet<u32>
}

impl Clause {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        for &var in &self.t {
            if assignment.is_set(var) { return true }
        }
        for &var in &self.f {
            if !assignment.is_set(var) { return true }
        }

        false
    }
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
/// Conjunction of disjunctive clauses.
pub struct Problem {
    pub variables: u32,
    pub clauses: Vec<Clause>
}

impl Problem {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        self.clauses.iter().all(|c| c.evaluate(assignment))
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(write!(f, "vars 1..{}: ", self.variables));
        for (i, clause) in self.clauses.iter().enumerate() {
            if i > 0 {
                try!(write!(f, " ∧ "));
            }
            try!(write!(f, "({})", clause));
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Assignment(u32, HashSet<u32>);

impl Assignment {
    pub fn new(vars: u32) -> Assignment {
        Assignment(vars, HashSet::new())
    }

    pub fn set(&mut self, var: u32) {
        assert!(var > 0 && var <= self.0);

        self.1.insert(var);
    }

    pub fn is_set(&self, var: u32) -> bool {
        assert!(var > 0 && var <= self.0);

        self.1.contains(&var)
    }
}

impl fmt::Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for i in 0..self.0 {
            let var = i+1;

            if i > 0 { try!(write!(f, " ")) }
            if self.1.contains(&var) {
                try!(write!(f, "{}", var));
            } else {
                try!(write!(f, "¬{}", var));
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum SolverResult {
    Satisfiable(Assignment),
    Unsatisfiable
}

pub trait Solver {
    fn solve(&self, problem: &Problem) -> SolverResult;
}

enum OutputFormat {
    Shorts,
    Dimacs
}

fn main() {
    let args = std::env::args();

    let mut output_format = OutputFormat::Shorts;
    let mut path = None;

    for arg in args {
        if arg == "--dimacs" {
            output_format = OutputFormat::Dimacs;
        } else {
            path = Some(arg);
        }
    }

    let path = match path {
        Some(path) => path,
        None => {
            println!("Usage: shorts [--dimacs] <problem.dimacs>");
            println!("Options:");
            println!("  -dimacs    Print result in DIMACS format");
            return;
        }
    };

    let problem = match dimacs::load_problem(&path) {
        Ok(p) => p,
        Err(e) => { println!("{}", e); return }
    };

    let solver = naive::NaiveSolver;
    let result = solver.solve(&problem);

    match output_format {
        OutputFormat::Dimacs => {
            println!("c shorts - a rust sat solver");
            println!("c strategy: exhaustive search");

            match result {
                SolverResult::Unsatisfiable => println!("s cnf 0"),
                SolverResult::Satisfiable(assn) => {
                    print!("s cnf 1 {} {}\nv", problem.variables, problem.clauses.len());
                    for var in 0..problem.variables {
                        let var = var+1;
                        if assn.is_set(var) {
                            print!(" {}", var);
                        } else {
                            print!(" -{}", var);
                        }
                    }
                    print!("\n");
                }
            }
        },
        OutputFormat::Shorts => {
            println!("shorts - A Rust SAT solver\n");
            println!("Problem:");
            println!("  {}", problem);

            match result {
                SolverResult::Unsatisfiable => println!("Verdict: unsatisfiable"),
                SolverResult::Satisfiable(assn) => {
                    println!("Verdict: satisfiable\nAssignment: {}", assn);
                }
            }
        }
    }
}
