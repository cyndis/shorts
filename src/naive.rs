use {Solver, Problem, SolverResult, TotalAssignment, PartialAssignment};

fn each_combination<F: FnMut(TotalAssignment) -> bool>(n: u32, mut f: F) {
    fn inner<F: FnMut(TotalAssignment) -> bool>(i: u32, n: u32, h: PartialAssignment, f: &mut F)
        -> bool
    {
        if i == n {
            return f(h.complete())
        }

        let mut r = h.clone();
        r.assign(i, false);
        if !inner(i+1, n, r, f) { return false }

        let mut r = h.clone();
        r.assign(i, true);
        inner(i+1, n, r, f)
    }

    inner(1, n+1, PartialAssignment::new(n), &mut f);
}

pub struct NaiveSolver;

impl Solver for NaiveSolver {
    fn solve(&self, problem: &Problem) -> SolverResult {
        let mut result = SolverResult::Unsatisfiable;

        each_combination(problem.variables.count(), |assignment| {
            if problem.evaluate(&assignment) {
                result = SolverResult::Satisfiable(assignment);
                false
            } else {
                true
            }
        });

        result
    }

    fn name(&self) -> &str {
        "bruteforce"
    }
}
