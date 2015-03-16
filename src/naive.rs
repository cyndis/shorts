use {Solver, Problem, SolverResult, Assignment};

fn each_combination<F: FnMut(Assignment) -> bool>(n: u32, mut f: F) {
    fn inner<F: FnMut(Assignment) -> bool>(i: u32, n: u32, h: Assignment, f: &mut F) -> bool {
        if i == n {
            return f(h)
        }

        if !inner(i+1, n, h.clone(), f) { return false }

        let mut r = h.clone();
        r.set(i);

        inner(i+1, n, r, f)
    }

    inner(1, n+1, Assignment::new(n), &mut f);
}

pub struct NaiveSolver;

impl Solver for NaiveSolver {
    fn solve(&self, problem: &Problem) -> SolverResult {
        let mut result = SolverResult::Unsatisfiable;

        each_combination(problem.variables, |assignment| {
            if problem.evaluate(&assignment) {
                result = SolverResult::Satisfiable(assignment);
                false
            } else {
                true
            }
        });

        result
    }
}
