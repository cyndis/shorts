use {Solver, Problem, SolverResult, PartialAssignment, Clause, Unitness, Assignment};

pub struct DpllSolver;

#[derive(Debug, Clone)]
struct State<'problem> {
    clauses: Vec<&'problem Clause>,
    assignment: PartialAssignment
}

impl<'problem> State<'problem> {
    fn purity(&self, var: u32) -> Option<bool> {
        let vs = self.clauses.iter().filter_map(|c| c.literal(var));
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
fn propagate_unit_clauses(state: &mut State)
    -> Option<SolverResult>
{
    let mut unsat = false;

    let (clauses, assignment) = (&mut state.clauses, &mut state.assignment);

    loop {
        let mut changed = false;

        clauses.retain(|clause| {
            match clause.unit_literal(assignment) {
                Unitness::Nonunit => true,
                Unitness::Unit(var, value) => {
                    assignment.assign(var, value);
                    changed = true;
                    true
                },
                Unitness::Determined(truth) => {
                    if !truth {
                        unsat = true;
                    }

                    false
                }
            }
        });

        if unsat || !changed { break }
    }

    if unsat {
        return Some(SolverResult::Unsatisfiable)
    } else {
        return None
    }
}

fn eliminate_pure(problem: &Problem, state: &mut State) {
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
}

fn solve<'problem>(problem: &'problem Problem, initial: State<'problem>) -> SolverResult {
    let mut state_stack = vec![initial];

    while let Some(state) = state_stack.pop() {
        let mut state = state;

        if let Some(_) = propagate_unit_clauses(&mut state) {
            continue;
        }

        eliminate_pure(problem, &mut state);

        if state.clauses.is_empty() {
            return SolverResult::Satisfiable(state.assignment.complete());
        }

        let next_var = state.clauses[0].first_unassigned_variable(&state.assignment);
        if let Some(next_var) = next_var {
            let mut left_state = state.clone();
            let mut right_state = state;

            left_state.assignment.assign(next_var, false);
            right_state.assignment.assign(next_var, true);

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

impl Solver for DpllSolver {
    fn solve(&self, problem: &Problem) -> SolverResult {
        let all_clauses = problem.clauses.iter().collect::<Vec<_>>();

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
