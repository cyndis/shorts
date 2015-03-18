#![feature(plugin, core, collections, std_misc)]
#![plugin(peg_syntax_ext)]

extern crate time;

use std::collections::{HashSet, HashMap};
use std::fmt;
use std::num::SignedInt;

mod dimacs;
mod naive;
mod dpll;

#[derive(Debug, Clone)]
/// Disjunctive clause.
pub struct Clause {
    pub t: HashSet<u32>,
    pub f: HashSet<u32>
}

impl Clause {
    fn new(trues: &[u32], falses: &[u32]) -> Clause {
        let mut t = HashSet::new();
        for &var in trues {
            t.insert(var);
        }

        let mut f = HashSet::new();
        for &var in falses {
            f.insert(var);
        }

        Clause { t: t, f: f }
    }

    fn evaluate(&self, assignment: &Assignment) -> bool {
        for &var in &self.t {
            if assignment.is_set(var) { return true }
        }
        for &var in &self.f {
            if !assignment.is_set(var) { return true }
        }

        false
    }

    fn unit_evaluate(&self, var: u32, is_true: bool) -> bool {
        (is_true  && self.t.contains(&var)) ||
        (!is_true && self.f.contains(&var))
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

#[derive(Debug, Clone)]
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
pub struct PartialAssignment(u32, HashMap<u32, bool>);
impl PartialAssignment {
    pub fn new(vars: u32) -> PartialAssignment {
        PartialAssignment(vars, HashMap::new())
    }

    pub fn assign(&mut self, var: u32, value: bool) {
        assert!(var > 0 && var <= self.0);
        assert!(!self.is_assigned(var));

        self.1.insert(var, value);
    }

    pub fn is_assigned(&self, var: u32) -> bool {
        assert!(var > 0 && var <= self.0);

        self.1.contains_key(&var)
    }

    pub fn assignment(&self, var: u32) -> Option<bool> {
        self.1.get(&var).cloned()
    }

    pub fn complete(self) -> Assignment {
        let mut assn = HashSet::new();

        for (var, value) in self.1 {
            if value {
                assn.insert(var);
            }
        }

        Assignment(self.0, assn)
    }

    pub fn unconstrained(&self) -> HashSet<u32> {
        let mut r = HashSet::new();

        for i in 0..self.0 {
            let var = i+1;

            if !self.1.contains_key(&var) {
                r.insert(var);
            }
        }

        r
    }
}

#[derive(Debug, Clone)]
pub struct Assignment(u32, HashSet<u32>);

impl Assignment {
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
    fn name(&self) -> &str;
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

    match output_format {
        OutputFormat::Dimacs => {
            println!("c shorts - a cnf boolean satisfiability solver");
        },
        OutputFormat::Shorts => {
            println!("shorts - A CNF boolean satisfiability solver\n");
            println!("Problem:");
            println!("  {}", problem);
        }
    }

    for solver in &[&dpll::DpllSolver as &Solver, &naive::NaiveSolver as &Solver] {
        println!("");

        let pre = time::precise_time_ns();
        let result = solver.solve(&problem);
        let post = time::precise_time_ns();
        let elapsed = std::time::Duration::nanoseconds(post as i64 - pre as i64);

        match output_format {
            OutputFormat::Dimacs => {
                println!("c strategy: {}", solver.name());

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
                println!("Strategy: {}", solver.name());
                match result {
                    SolverResult::Unsatisfiable => println!("Verdict: unsatisfiable"),
                    SolverResult::Satisfiable(assn) => {
                        println!("Verdict: satisfiable\nAssignment: {}", assn);
                        println!("Sanity: {}",
                                 if problem.evaluate(&assn) { "OK" } else { "Failed" });

                        let secs = elapsed.num_milliseconds() as f32 / 1000.0;
                        println!("Computation took {:.3} seconds", secs);
                    }
                }
            }
        }
    }
}
