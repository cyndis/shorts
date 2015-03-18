use {Solver, Problem, SolverResult, PartialAssignment, Assignment, Clause, Unitness};
use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::iter::IntoIterator;

pub struct DpllSolver;

#[derive(Debug, Clone)]
struct State<'problem> {
    clauses: Vec<&'problem Clause>,
    assignment: PartialAssignment
}

impl<'problem> State<'problem> {
    fn purity(&self, var: u32) -> Option<bool> {
        let mut vs = self.clauses.iter().filter_map(|c| c.literal(var));
        let mut so_far = None;
        for value in vs {
            match (so_far, value) {
                (None, x) => so_far = Some(x),
                (Some(a), b) if a != b => return None,
                _ => ()
            }
        }
        so_far
    }
}

/// Find clauses with only one literal, add the literals to the assignment and delete the clauses
/// from the active clauses list.
fn propagate_unit_clauses(problem: &Problem, state: &mut State)
    -> Option<SolverResult>
{
    let mut unsat = false;

    let (clauses, assignment) = (&mut state.clauses, &mut state.assignment);

    loop {
        let mut changed = false;

        clauses.retain(|clause| {
            print!("{:?} {:?} ", assignment, clause);
            match clause.unit_literal(&assignment) {
                Unitness::Nonunit => { println!("nonunit"); true },
                Unitness::Unit(var, value) => {
                    println!("up: {} <- {}", var, value);
                    println!("c {:?} a {:?}", clause, assignment);
                    assignment.assign(var, value);
                    changed = true;
                    true
                },/*
                    match assignment.assignment(var) {
                        Some(assn) if assn != value => {
                            println!(" conflict on var {}", var);
                            result = Some(SolverResult::Unsatisfiable);
                        },
                        None => {
                            println!(" propagating var {} = {}", var, value);
                            assignment.assign(var, value);
                        },
                        _ => ()
                    }

                    false
                },*/
                Unitness::Determined(truth) => {
                    println!("determined {}", truth);
                    if !truth {
                        unsat = true;
                    }

                    false
                }
            }
        });

        if unsat || !changed { break }
    }

    println!("{} clauses left after propagation", clauses.len());

    if unsat {
        return Some(SolverResult::Unsatisfiable)
    } else {
        return None
    }
}
/*
fn fixup_assignment(problem: &mut Problem, var: u32, value: bool) -> Option<SolverResult> {
    problem.clauses.retain(|clause| !clause.unit_evaluate(var, value));
    for clause in &mut problem.clauses {
        clause.t.remove(&var);
        clause.f.remove(&var);

        if clause.t.len() + clause.f.len() == 0 {
            return Some(SolverResult::Unsatisfiable);
        }
    }

    None
}

#[test]
fn test_propagate_unit_clauses() {
    let mut p = Problem {
        variables: 1,
        clauses: vec![
            Clause::new(&[1], &[])
        ]
    };

    let mut a = PartialAssignment::new(p.variables);

    propagate_unit_clauses(&mut p, &mut a);

    assert!(p.clauses.is_empty());
    assert!(a.assignment(1) == Some(true));
}
*/
/*
fn get_purity(var: u32, problem: &Problem) -> Option<bool> {
    let mut seen = None;

    for clause in &problem.clauses {
        let here =
            if clause.t.contains(&var) { Some(true) }
            else if clause.f.contains(&var) { Some(false) }
            else { None };

        match (seen, here) {
            (None, x) => seen = x,
            (Some(p), Some(n)) if p != n => return None,
            _ => ()
        }
    }

    seen
}

#[test]
fn test_get_purity() {
    let mut p = Problem {
        variables: 3,
        clauses: vec![
            Clause::new(&[1, 2], &[3]),
            Clause::new(&[1], &[2, 3])
        ]
    };

    assert_eq!(get_purity(1, &p), Some(true));
    assert_eq!(get_purity(2, &p), None);
    assert_eq!(get_purity(3, &p), Some(false));
}
*/
fn eliminate_pure(problem: &Problem, state: &mut State) -> Option<SolverResult> {
    for var in &problem.variables {
        match (state.purity(var), state.assignment.assignment(var)) {
            (Some(value), Some(assn)) if value == assn => {
                // Variable is purely of assigned polarity, can remove all clauses
                // that contain it.

                state.clauses.retain(|clause| clause.literal(var).is_none());
            },
            (Some(value), Some(assn)) if value != assn => {
                // Variable is purely of opposite polarity, can never be satisfied
            },
            (Some(value), None) => {
                // Variable is pure but no assignment has been made yet

                state.assignment.assign(var, value);

                state.clauses.retain(|clause| clause.literal(var).is_none());
            },
            (None, _) => {
                // Variable is impure. Nothing to be done.
            },
            _ => unreachable!()
        }
    }

    None
}

fn solve<'problem>(problem: &'problem Problem, mut state: State<'problem>) -> SolverResult {
    if state.clauses.is_empty() {
        return SolverResult::Satisfiable(state.assignment.complete());
    }

    if let Some(result) = propagate_unit_clauses(problem, &mut state) {
        return result;
    }

    //if let Some(result) = eliminate_pure(problem, &mut state) {
    //    return result;
    //}

    if state.clauses.is_empty() {
        return SolverResult::Satisfiable(state.assignment.complete());
    }

    let next_var = problem.variables.into_iter().find(|&var| !state.assignment.is_assigned(var));
    if let Some(next_var) = next_var {
        let mut left_state = state.clone();
        let mut right_state = state.clone();

        //let mut a = String::new();
        //::std::io::stdin().read_line(&mut a);

        left_state.assignment.assign(next_var, false);
        right_state.assignment.assign(next_var, true);

        let left_result = solve(problem, left_state);
        if let SolverResult::Satisfiable(_) = left_result {
            return left_result;
        }

        let right_result = solve(problem, right_state);
        if let SolverResult::Satisfiable(_) = right_result {
            return right_result;
        }

        return SolverResult::Unsatisfiable;
    } else {
        println!("UNREACHABLE");
        println!("assn = {:?}", state.assignment);
        println!("clauses = {:?}", state.clauses);
        unreachable!();
    }
}

impl Solver for DpllSolver {
    fn solve(&self, problem: &Problem) -> SolverResult {
        let all_clauses = problem.clauses.iter().collect::<Vec<_>>();

        println!("Clauses:\n{:?}", all_clauses);
        let root_state = State {
            clauses: all_clauses,
            assignment: PartialAssignment::new(problem.variables.count())
        };

        solve(problem, root_state)
    }
    fn name(&self) -> &str {
        "dpll"
    }
}
