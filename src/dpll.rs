use {Solver, Problem, SolverResult, PartialAssignment, Assignment, Clause};
use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;

pub struct DpllSolver;

/// Find clauses with only one literal, add the literals to the assignment and delete the clauses.
/// This requires that literal selection during branching removes assigned literals from clauses.
fn propagate_unit_clauses(problem: &mut Problem, assn: &mut PartialAssignment)
    -> Option<SolverResult>
{
    let units = problem.clauses.iter().filter_map(|clause| {
        if clause.t.len() + clause.f.len() != 1 { return None }

        if let Some(&var) = clause.t.iter().next() {
            Some((var, true))
        } else if let Some(&var) = clause.f.iter().next() {
            Some((var, false))
        } else {
            unreachable!()
        }
    }).collect::<Vec<_>>();

    for &(var, is_true) in &units {
        match assn.assignment(var) {
            Some(a) if a != is_true => { return Some(SolverResult::Unsatisfiable) },
            None => { assn.assign(var, is_true) },
            _ => ()
        }

        if let Some(result) = fixup_assignment(problem, var, is_true) {
            return Some(result);
        }
    }

    None
}

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

fn eliminate_pure(problem: &mut Problem, assn: &mut PartialAssignment) -> Option<SolverResult> {
    for i in 0..problem.variables {
        let var = i+1;

        match get_purity(var, &problem) {
            Some(polarity) => {
                match assn.assignment(var) {
                    None => { assn.assign(var, polarity) }
                    _ => ()
                }

                if let Some(result) = fixup_assignment(problem, var, polarity) {
                    return Some(result);
                }
            },
            None => ()
        }
    }

    None
}

fn solve(mut p: Problem, mut assn: PartialAssignment) -> SolverResult {
    //println!("{}\n", p);

    if let Some(result) = propagate_unit_clauses(&mut p, &mut assn) {
        return result;
    }

    if let Some(result) = eliminate_pure(&mut p, &mut assn) {
        return result;
    }

    if p.clauses.is_empty() {
        return SolverResult::Satisfiable(assn.complete());
    }

    let next_var = (0..p.variables).map(|x| x+1).find(|&var| !assn.is_assigned(var));
    match next_var {
        Some(var) => {
            let mut left = assn.clone();
            let mut right = assn.clone();

            let mut leftp = p.clone();
            let mut rightp = p;

            let mut run_l = true;
            let mut run_r = true;

            for clause in &mut leftp.clauses {
                clause.t.remove(&var);

                if clause.t.len() + clause.f.len() == 0 {
                    run_l = false;
                    break;
                }
            }

            for clause in &mut rightp.clauses {
                clause.f.remove(&var);

                if clause.t.len() + clause.f.len() == 0 {
                    run_r = false;
                    break;
                }
            }

            left.assign(var, false);

            if let Some(SolverResult::Unsatisfiable) = fixup_assignment(&mut leftp, var, false) {
                run_l = false;
            }

            right.assign(var, true);

            if let Some(SolverResult::Unsatisfiable) = fixup_assignment(&mut rightp, var, true) {
                run_l = false;
            }

            let left_r = if run_l {
                solve(leftp, left)
            } else {
                SolverResult::Unsatisfiable
            };

            let right_r = if run_r {
                solve(rightp, right)
            } else {
                SolverResult::Unsatisfiable
            };

            match (left_r, right_r) {
                (SolverResult::Satisfiable(s), _) |
                (_, SolverResult::Satisfiable(s)) => return SolverResult::Satisfiable(s),
                _                                 => return SolverResult::Unsatisfiable
            }
        },
        None => return SolverResult::Unsatisfiable
    }
}

impl Solver for DpllSolver {
    fn solve(&self, problem: &Problem) -> SolverResult {
        solve(problem.clone(), PartialAssignment::new(problem.variables))
    }
    fn name(&self) -> &str {
        "dpll"
    }
}
