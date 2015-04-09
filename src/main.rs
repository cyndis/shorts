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

trait Assignment {
    fn assignment(&self, var: u32) -> Option<bool>;

    fn is_assigned(&self, var: u32) -> bool {
        self.assignment(var).is_some()
    }
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

    fn unit_literal<A: Assignment>(&self, assignment: &A) -> Unitness {
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

    fn evaluate(&self, assignment: &TotalAssignment) -> bool {
        for (var, &value) in &self.literals {
            if assignment.is_set(var as u32) == value {
                return true
            }
        }

        false
    }

    fn evaluate_partial<A: Assignment>(&self, assignment: &A) -> Option<bool> {
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

    fn first_unassigned_variable<A: Assignment>(&self, assignment: &A) -> Option<u32> {
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
    fn evaluate(&self, assignment: &TotalAssignment) -> bool {
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

    pub fn complete(self) -> TotalAssignment {
        let mut assn = HashSet::new();

        for (var, value) in self.1 {
            if value {
                assn.insert(var as u32);
            }
        }

        TotalAssignment(self.0, assn)
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

impl Assignment for PartialAssignment {
    fn is_assigned(&self, var: u32) -> bool {
        assert!(var > 0 && var <= self.0);

        self.1.contains_key(&(var as usize))
    }

    fn assignment(&self, var: u32) -> Option<bool> {
        self.1.get(&(var as usize)).cloned()
    }
}

#[derive(Debug, Clone)]
pub struct TotalAssignment(u32, HashSet<u32>);

impl TotalAssignment {
    pub fn is_set(&self, var: u32) -> bool {
        assert!(var > 0 && var <= self.0);

        self.1.contains(&var)
    }
}

impl Assignment for TotalAssignment {
    fn is_assigned(&self, var: u32) -> bool {
        assert!(var > 0 && var <= self.0);

        true
    }

    fn assignment(&self, var: u32) -> Option<bool> {
        Some(self.1.contains(&var))
    }
}

impl fmt::Display for TotalAssignment {
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
    Satisfiable(TotalAssignment),
    Unsatisfiable
}

pub trait Solver: Sync {
    fn solve(&self, problem: &Problem) -> SolverResult;
    fn name(&self) -> &str;
}

#[derive(PartialEq, Eq)]
enum OutputFormat {
    Shorts,
    Dimacs,
    Course
}

const SOLVERS: &'static [&'static Solver] = &[
    &dpll::DpllSolver,
    &backtrack::BacktrackSolver,
    &naive::NaiveSolver
];
static DEFAULT_SOLVER: &'static Solver = SOLVERS[0];

fn print_usage() {
    println!("Usage: shorts [options] <problem.dimacs>");
    println!("Options:");
    println!("  -d            Print result in DIMACS format");
    println!("  -c            Print result in course test suite format");
    println!("  -s strategy   Solving strategy to use (default = {})", DEFAULT_SOLVER.name());
    println!("\nAvailable strategies:");
    for solver in SOLVERS {
        println!("  {}", solver.name());
    }
}

fn main() {
    let mut args = std::env::args().skip(1);

    let mut output_format = OutputFormat::Shorts;
    let mut path = None;
    let mut solver: &'static Solver = SOLVERS[0];

    while let Some(arg) = args.next() {
        if arg == "-d" {
            output_format = OutputFormat::Dimacs;
        } else if arg == "-c" {
            output_format = OutputFormat::Course;
        } else if arg == "-s" {
            let name = match args.next() {
                Some(n) => n,
                None    => { println!("Error: parameter required for '-s'"); print_usage(); return }
            };
            solver = match SOLVERS.iter().find(|s| s.name() == name) {
                Some(&s) => s,
                None    => {
                    println!("Error: unknown strategy '{}'", name); print_usage(); return;
                }
            };
        } else if arg.starts_with("-") {
            print_usage();
            return;
        } else {
            path = Some(arg);
        }
    }

    let path = match path {
        Some(path) => path,
        None => {
            print_usage();
            return;
        }
    };

    let problem = match dimacs::load_problem(&path) {
        Ok(p) => p,
        Err(ref e) if output_format != OutputFormat::Course => { println!("{}", e); return }
        Err(e) => { println!("error {}", e); return }
    };

    match output_format {
        OutputFormat::Dimacs => {
            println!("c shorts - a cnf boolean satisfiability solver");
        },
        OutputFormat::Shorts => {
            println!("shorts - A CNF boolean satisfiability solver\n");
            println!("Problem:");
            println!("  {}", problem);
            println!("");
        },
        OutputFormat::Course => ()
    }

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
        },
        OutputFormat::Course => {
            match result {
                SolverResult::Unsatisfiable => println!("unsat"),
                SolverResult::Satisfiable(assn) => {
                    print!("sat");
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
        }
    }
}
