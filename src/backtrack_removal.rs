use {Solver, Problem, SolverResult, PartialAssignment, Assignment, Clause, Unitness};
use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::iter::IntoIterator;

pub struct BacktrackRemovalSolver;

#[derive(Debug, Clone)]
struct State {
    clauses: Vec<Clause>,
    assignment: PartialAssignment
}

impl State {
    fn assign_var(&mut self, var: u32, value: bool) {
        let (clauses, assignment) = (&mut self.clauses, &mut self.assignment);

        assignment.assign(var, value);
        clauses.retain(|clause| clause.evaluate_partial(assignment) != Some(true));
        for clause in clauses {
            if clause.literal(var).is_some() {
                clause.remove_literal(var);
            }
        }
    }
}

fn solve<'problem>(problem: &'problem Problem, mut initial: State) -> SolverResult {
    let mut state_stack = vec![initial];

    while !state_stack.is_empty() {
        let mut state = state_stack.pop().unwrap();

        if state.clauses.is_empty() {
            return SolverResult::Satisfiable(state.assignment.complete());
        }

        let mut unsat = false;
        for clause in &state.clauses {
            if clause.evaluate_partial(&state.assignment) == Some(false) {
                unsat = true;
                break;
            }
        }
        if unsat { continue }

        let next_var = problem.variables.into_iter().find(|&var| !state.assignment.is_assigned(var));
        if let Some(next_var) = next_var {
            let mut left_state = state.clone();
            let mut right_state = state;

            left_state.assign_var(next_var, false);
            right_state.assign_var(next_var, true);

            state_stack.push(left_state);
            state_stack.push(right_state);
        } else {
            println!("UNREACHABLE");
            println!("assn = {:?}", state.assignment);
            println!("clauses = {:?}", state.clauses);
            unreachable!();
        }
    }

    SolverResult::Unsatisfiable
}

impl Solver for BacktrackRemovalSolver {
    fn solve(&self, problem: &Problem) -> SolverResult {
        let all_clauses = problem.clauses.iter().cloned().collect::<Vec<_>>();

        let root_state = State {
            clauses: all_clauses,
            assignment: PartialAssignment::new(problem.variables.count())
        };

        solve(problem, root_state)
    }
    fn name(&self) -> &str {
        "backtrack_removal"
    }
}
