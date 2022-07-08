mod infer;

use crate::infer::{ppc, State, Term, TypingEnvironment};

fn main() {
    ppc(Term::Int(0), &TypingEnvironment::new());
    println!("Hello, world!");
}
