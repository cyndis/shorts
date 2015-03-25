use {Solver, Problem, SolverResult, PartialAssignment, Clause};

pub struct BacktrackSolver;

#[derive(Debug, Clone)]
struct State<'problem> {
    clauses: Vec<&'problem Clause>,
    assignment: PartialAssignment
}

impl<'a> State<'a> {
    fn assign_var(&mut self, var: u32, value: bool) {
        let (clauses, assignment) = (&mut self.clauses, &mut self.assignment);

        assignment.assign(var, value);
        clauses.retain(|clause| clause.evaluate_partial(assignment) != Some(true));
    }
}

fn solve<'problem>(initial: State<'problem>) -> SolverResult {
    let mut state_stack = vec![initial];

    while let Some(state) = state_stack.pop() {
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

        let next_var = state.clauses[0].first_unassigned_variable(&state.assignment);
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

impl Solver for BacktrackSolver {
    fn solve(&self, problem: &Problem) -> SolverResult {
        let all_clauses = problem.clauses.iter().collect::<Vec<_>>();

        let root_state = State {
            clauses: all_clauses,
            assignment: PartialAssignment::new(problem.variables.count())
        };

        solve(root_state)
    }
    fn name(&self) -> &str {
        "backtrack"
    }
}
