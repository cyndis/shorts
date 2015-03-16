use std::{io, fs, fmt, error};
use std::path::AsPath;
use std::io::prelude::*;
use std::collections::HashSet;
use std::num::SignedInt;
use Problem;
use Clause;

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Parse(dimacs_peg::ParseError),
    Invalid(&'static str)
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::Error::*;

        match *self {
            Io(ref e) => write!(f, "I/O error: {}", e),
            Parse(ref e) => write!(f, "Parse error: {}", e),
            Invalid(ref e) => write!(f, "Invalid contents: {}", e)
        }
    }
}

impl error::FromError<io::Error> for Error {
    fn from_error(err: io::Error) -> Error {
        Error::Io(err)
    }
}

impl error::FromError<dimacs_peg::ParseError> for Error {
    fn from_error(err: dimacs_peg::ParseError) -> Error {
        Error::Parse(err)
    }
}

pub fn load_problem<P: AsPath + ?Sized>(path: &P) -> Result<Problem, Error> {
    let mut data = String::new();
    let mut fp = try!(fs::File::open(path));

    try!(fp.read_to_string(&mut data));

    let (preamble, clauses) = try!(dimacs_peg::root(&data));

    if preamble.0 != "cnf" { return Err(Error::Invalid("Clause format is not cnf")) }
    if preamble.2 != clauses.len() as u32 {
        return Err(Error::Invalid("Number of clauses does not match preamble"))
    }

    let mut problem = Problem { variables: preamble.1, clauses: vec![] };

    for clause in &clauses {
        let mut c = Clause { t: HashSet::new(), f: HashSet::new() };

        for &var in clause {
            let abs = var.abs() as u32;
            if abs < 1 || abs > preamble.1 {
                return Err(Error::Invalid("Used variable with index not in range"))
            }

            if var > 0 {
                if c.t.contains(&abs) {
                    return Err(Error::Invalid("Duplicate positive constraint"))
                }
                if c.f.contains(&abs) {
                    return Err(Error::Invalid("Contradictory constraints in clause"))
                }

                c.t.insert(abs);
            } else {
                if c.f.contains(&abs) {
                    return Err(Error::Invalid("Duplicate negative constraint"))
                }
                if c.t.contains(&abs) {
                    return Err(Error::Invalid("Contradictory constraints in clause"))
                }

                c.f.insert(abs);
            }
        }

        problem.clauses.push(c);
    }

    return Ok(problem);
}

peg! dimacs_peg(r#"
use std::borrow::ToOwned;

#[pub]
root -> ((String, u32, u32), Vec<Vec<i32>>)
    = preamble:preamble wsq clauses:clauses { (preamble, clauses) }

ws = [\n\t ]+ { () }
wsq = ws? { () }

preamble -> (String, u32, u32)
    = (comment "\n")* problem:problem "\n" { problem }

comment
    = "c" [^\n]*

problem -> (String, u32, u32)
    = "p" ws format:ident ws vars:number ws clauses:number [\t ]* { (format, vars, clauses) }

clauses -> Vec<Vec<i32>>
    = d:(clause ** ws) ws { d }

clause -> Vec<i32>
    = ns:(inumber ** ws) wsq "0" { ns }

ident -> String
    = [a-z]+ { match_str.to_owned() }

number -> u32
    = [0-9]+ { match_str.parse().unwrap() }

inumber -> i32
    = "-"? [1-9]+ { match_str.parse().unwrap() }
"#);

#[test]
fn test_parser() {
    assert_eq!(dimacs_peg::root("c foo\np cnf 0 0\n"), Ok((("cnf".to_owned(), 0, 0), vec!())));
    assert_eq!(dimacs_peg::root("p cnf 1 1\n1 0"), Ok((("cnf".to_owned(), 1, 1), vec!(vec!(1)))));
    assert_eq!(dimacs_peg::root("p cnf 2 2\n1 -2 0\n-1 0"), Ok((("cnf".to_owned(), 2, 2), vec!(vec!(1, -2), vec!(-1)))));
}
