#![feature(plugin, core, collections, std_misc, str_char)]
#![plugin(peg_syntax_ext)]

extern crate time;

use std::collections::{HashSet, VecMap};
use std::fmt;

mod dimacs;
mod naive;
mod dpll;
mod backtrack;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Disjunctive clause.
pub struct Clause {
    literals: VecMap<bool>
}

pub enum Unitness {
    Unit(u32, bool),
    Nonunit,
    Determined(bool)
}

impl Clause {
    fn empty() -> Clause {
        Clause { literals: VecMap::new() }
    }

    fn add_literal(&mut self, var: u32, value: bool) {
        self.literals.insert(var as usize, value);
    }

    fn literal(&self, var: u32) -> Option<bool> {
        self.literals.get(&(var as usize)).cloned()
    }

    fn unit_literal(&self, assignment: &PartialAssignment) -> Unitness {
        let mut ret = None;

        if let Some(x) = self.evaluate_partial(assignment) {
            return Unitness::Determined(x)
        }

        for (var, &value) in &self.literals {
            let var = var as u32;
            match (assignment.is_assigned(var), ret) {
                (false, None) => ret = Some((var, value)),
                (false, _   ) => return Unitness::Nonunit,
                _             => ()
            }
        }

        match ret {
            Some((var, value)) => return Unitness::Unit(var, value),
            _ => unreachable!()
        }
    }

    fn evaluate(&self, assignment: &Assignment) -> bool {
        for (var, &value) in &self.literals {
            if assignment.is_set(var as u32) == value {
                return true
            }
        }

        false
    }

    fn evaluate_partial(&self, assignment: &PartialAssignment) -> Option<bool> {
        let mut indeterminate = false;

        for (var, &value) in &self.literals {
            match assignment.assignment(var as u32) {
                Some(a) if a == value => { return Some(true) },
                None => { indeterminate = true }
                _ => ()
            }
        }

        if indeterminate {
            None
        } else {
            Some(false)
        }
    }

    fn first_unassigned_variable(&self, assignment: &PartialAssignment) -> Option<u32> {
        for (var, _) in &self.literals {
            if !assignment.is_assigned(var as u32) {
                return Some(var as u32);
            }
        }

        None
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for (i, (var, &value)) in self.literals.iter().enumerate() {
            if i > 0 {
                try!(write!(f, " ∨ "));
            }
            if !value {
                try!(write!(f, "¬"));
            }
            try!(write!(f, "{}", var));
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct VariableSet(u32);
impl VariableSet {
    pub fn new(num: u32) -> VariableSet {
        VariableSet(num)
    }

    pub fn count(&self) -> u32 {
        self.0
    }
}

impl<'a> std::iter::IntoIterator for &'a VariableSet {
    type Item = u32;
    type IntoIter = std::iter::RangeInclusive<u32>;

    fn into_iter(self) -> std::iter::RangeInclusive<u32> {
        std::iter::range_inclusive(1, self.0)
    }
}

#[derive(Debug, Clone)]
/// Conjunction of disjunctive clauses.
pub struct Problem {
    pub variables: VariableSet,
    pub clauses: Vec<Clause>
}

impl Problem {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        self.clauses.iter().all(|c| c.evaluate(assignment))
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(write!(f, "vars 1..{}: ", self.variables.count()));
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
pub struct PartialAssignment(u32, VecMap<bool>);
impl PartialAssignment {
    pub fn new(vars: u32) -> PartialAssignment {
        PartialAssignment(vars, VecMap::new())
    }

    pub fn assign(&mut self, var: u32, value: bool) {
        assert!(var > 0 && var <= self.0);
        assert!(!self.is_assigned(var));

        self.1.insert(var as usize, value);
    }

    pub fn is_assigned(&self, var: u32) -> bool {
        assert!(var > 0 && var <= self.0);

        self.1.contains_key(&(var as usize))
    }

    pub fn assignment(&self, var: u32) -> Option<bool> {
        self.1.get(&(var as usize)).cloned()
    }

    pub fn complete(self) -> Assignment {
        let mut assn = HashSet::new();

        for (var, value) in self.1 {
            if value {
                assn.insert(var as u32);
            }
        }

        Assignment(self.0, assn)
    }
/*
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
*/
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

    let solvers: &[&Solver] = &[
        &backtrack::BacktrackSolver
    ];

    for solver in solvers {
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
                        print!("s cnf 1 {} {}\nv", problem.variables.count(), problem.clauses.len());
                        for var in &problem.variables {
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
                    }
                }
                let secs = elapsed.num_milliseconds() as f32 / 1000.0;
                println!("Computation took {:.3} seconds", secs);
            }
        }
    }
}
