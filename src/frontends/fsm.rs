/*! Generates programs from finite state machines (FSMs).
 * The generated programs allow automated checking of state-set invariants for FSMs.
 * By generating FSMs of increasing complexity, this also lays the groundwork for a scalable
 * performance testing framework.
 * 
 * The translation targets NFAs with empty transitions, as this is not substantially harder
 * than DFAs.
 * 
 * The outline of the translation is as follows.
 * Let (Q, Sigma, delta, q0, F) be an NFA. The name 'final" is reserved and cannot be 
 * used as a state or character. Then generate the following program.
 * 
 * q -> final   [for all q in F]
 * q1 -> q2     [for all (q1, empty, q2) in delta]
 * q1 -> [a]q2  [for all (q1, a, q2) in delta]
 * 
 * Queries have the format:
 *   "When input follows a certain regular expression r*, does the DFA satisfy invariant state set J?"
 *    We assume r does not contain additional *s.
 * Regular expressions translate directly to PDL programs:
 * T(c) = c    [for character c]
 * T(r1;r2) = T(r2);T(r2)
 * T(r*) =  T(r)*@inv(\/J)
 * T(r1 U r2) = T(r1) U T(r2)
 * 
 * In general, a query translates to the query formula:
 * q0 -> [T(r*)]\/J
 * If we specifically wish to show that all words in the regular language lead to accepting states
 * (i.e., the NFA accepts a superset of the regular expression's language)
 * This is not as strong as showing that the NFA decides the language. 
 * We suspect proving that will require the diamond modality.
*/
use std::collections::{HashSet,HashMap};

/** A transition represents one element of an NFA's transition relation.
 * Transition NonEmpty(q1, c, q2) moves from state q1 to q2 while consuming character c.
 * Transition Empty(q1, q2) moves from state q1 to q2 without consuming any character.
 * Assume q1, q2 in q and c in sigma are valid identifiers.
 */
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub enum Transition {
    Empty(String, String),
    NonEmpty(String, String, String),
}

/** A nondeterministic automaton (NDA) is a finite state machine whose transition relation
 * is nondeterministic, i.e., a given character might have zero, one, or multiple target
 * states for the same source state. 
 */
#[derive(Debug,PartialEq,Eq,Clone)]
pub struct NFA {
    /** The set of states. Assumed to be non-empty, with all elements valid identifiers. */
    pub q: HashSet<String>,
    /** The character set of the NFA. Assumed to be non-empty, with all elements valid identifiers.
     * It is conventional for each c in sigma to be a single character, but not required. */
    pub sigma: HashSet<String>,
    /** The transition relation delta characterizes which states transition to each other 
     * and what character, if any, is consumed. The empty set is a valid, but boring, relation. */
    pub delta: HashSet<Transition>,
    /** The state where execution starts */
    pub q0: String,
    /** The set of final states, i.e., finishing in these states causes the NFA to accept  */
    pub f: HashSet<String>,
}

impl NFA {
    /** Produces a query in the following format, as a string:
     *  ?- q0 -> [r*@inv(J)]J
     * where J is the invariant and r is the program interpretation of a regular expression.
     */
    pub fn query(&self, r: &Regex,  inv: &HashSet<String>) -> String {
        let mut code = "?- ".to_string();
        code.push_str(&self.q0.clone());
        code.push_str(" -> [");
        code.push_str(&r.to_source(inv));
        code.push_str("]");
        code.push_str(&Regex::inv_formula(inv));
        code.push_str(".");
        code
    }

    /** Produces the program source of an NFA as a string. This program captures the
     * transition relation and final state set in the following format:
     *  q -> final.  (for every final state q in f)
     *  q1 -> q2.    (for every empty transition Empty(q1, q2) in delta)
     *  q1 -> [c]q2. (for every nonempty transition NonEmpty(q1, c, q2) in delta)
     */
    pub fn to_source(&self) -> String {
        // Map from program a to sequence of (p,q) such that (p,a,q) is a transition.
        let mut nonempty_trans: HashMap<String,Vec<(String, String)>> = HashMap::new();
        // Map from q to sequence of p such that (p, empty, q) is a transition
        let mut empty_trans: HashMap<String,Vec<String>> = HashMap::new();
        for tr in &self.delta {
            match tr {
                Transition::Empty(p,q) => {
                    match empty_trans.get_mut(q) {
                        Some(val) => val.push(p.clone()),
                        None => {empty_trans.insert(q.clone(), vec![p.clone()]);}
                    }
                },
                Transition::NonEmpty(p,a,q) => {
                    match nonempty_trans.get_mut(a) {
                        Some(val) => val.push((p.clone(), q.clone())),
                        None => {nonempty_trans.insert(a.clone(), vec![(p.clone(), q.clone())]);}
                    }
                },
            }
        }
        let mut code = "".to_string();
        let mut empty_keys: Vec<String> = empty_trans.keys().cloned().collect();
        empty_keys.sort();
        for dst in &empty_keys {
            let mut srcs = empty_trans.get(&dst.clone()).unwrap().clone();
            srcs.sort();
            for src in srcs {
                code.push_str(&src);
                code.push_str(" -> ");
                code.push_str(dst);
                code.push_str(".\n");
            }
        }
        let mut nonempty_keys: Vec<String> = nonempty_trans.keys().cloned().collect();
        nonempty_keys.sort();
        for prg in &nonempty_keys {
            let mut sds = nonempty_trans.get(&prg.clone()).unwrap().clone();
            sds.sort();
            for (src, dst) in sds {
                code.push_str(&src);
                code.push_str(" -> [");
                code.push_str(prg);
                code.push_str("]");
                code.push_str(&dst);
                code.push_str(".\n");
            }
        }
        for q in &self.f {
            code.push_str(q);
            code.push_str(" -> final.\n");
        }
        code
    }
}

/** A minimal language of regular expressions usable as correctness specifications for NFAs. */
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub enum Regex {
    Char(String),
    Choice(Box<Regex>, Box<Regex>),
    Sequence(Box<Regex>, Box<Regex>),
    Star(Box<Regex>),
}

impl Regex {
    /** Given an invariant state set, produce the invariant formula as a string. */
    pub fn inv_formula(inv: &HashSet<String>) -> String {
        let mut is_first = true;
        let mut fml = "".to_string();
        for str in inv {
            if is_first {
                is_first = false;
                fml.push_str(&str.clone());
            } else {
                fml.push_str("|");
                fml.push_str(&str.clone());
            }
        }
        return fml;
    }

    /** Recursively accumulate the string representation of the code for
     * a given regular expression into a given string. */
    fn to_source_rec(&self, inv: &HashSet<String>, acc: &mut String) {
        match self {
            Regex::Char(s) => {
                acc.push_str("(");
                acc.push_str(&s.clone());
                acc.push_str(")");
            },
            Regex::Choice(r1, r2) => {
                acc.push_str("(");
                r1.to_source_rec(inv, acc); 
                acc.push_str("U");
                r2.to_source_rec(inv, acc);
                acc.push_str(")");
            },
            Regex::Sequence(r1, r2) => {
                acc.push_str("(");
                r1.to_source_rec(inv, acc);
                acc.push_str(";");
                r2.to_source_rec(inv, acc);
                acc.push_str(")");
            },
            Regex::Star(r) => {
                acc.push_str("(");
                r.to_source_rec(inv, acc);
                acc.push_str(")*@inv(");
                acc.push_str(&Self::inv_formula(inv));
                acc.push_str(")");
            },
        }
    }

    /** Produce the string representing the code of the regular expression subject to a given invariant set */
    pub fn to_source(&self, inv: &HashSet<String>) -> String {
        let mut code = "".to_string();
        self.to_source_rec(inv, &mut code);
        code
    }
}