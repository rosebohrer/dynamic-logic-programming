/*! Abstract syntax tree data structures for propositional dynamic logic programming.

Abstract syntax trees are the primary data structure of the language implementation.
The Formula and Program types represent the standard syntactic classes of formulas 
and programs in propositional dynamic logic. In addition, the Defn type provides a way
to introduce new definitions, essential for developing propositional dynamic logic into
a programming language. The LogicProgram type represents a complete program including
a query. The REPLCommand type represents the syntax of commands issued by users in
interactive mode. 

The abstract syntax does not include every feature of propositional dynamic logic because
not all features have straightforward logic programming implementations. In particular,
we omit negation to avoid the challenge of negation-as-failure.

Our data structures are (mutually) recursive and use the Box<> type to provide the necessary
indirection. For consistency, recursive appearances are made recursive throughout the data
structures, even if Rust would accept the omission of some indirections.

For convenience, several traits are derived, including Debug. However, the Debug trait should
only be used for debugging functionality; user-facing code should use [printer] for printing
*/

use std::hash::Hash;
use std::hash::Hasher;

/** A Span represents a region of a string, specifically a string containing source code. 
 
  Every AST node is equipped with a span to indicate where in the code that node appears.
  This information is essential for producing readable error messages for error checks that
  occur after parsing is complete. Unknown positions and lengths are represented using
  sentinel values of -1. Unknown values primarily occur for AST nodes generated directly 
  from code without a source file, such as in unit tests. 
  
  During execution, spans are preserved as much as possible, but will necessarily lose 
  meaning as expressions arise which are not present in the source file. 32-bit integers
  are used so the structure fits in a 64-bit word. start and start + len are indices into
  the file as determined by the underying position!() command in the PEG crate.
*/
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /** Offset where span starts, -1 for unknown start. */
    pub start: i32,
    /** Difference between end and start offsets, -1 for unknown length. */
    pub len: i32, 
}            

impl Span {
    /** Default span has unknown size and location, for use in code-generated ASTs. */
    pub const DEFAULT: Self =  Span { start: -1, len: -1 };
}

/** A spanned type T is equipped with a span to track its corresponding source location.
  
  The equality function on Spanned<T> considers values equivalent up to equality at type T,
  i.e., it ignores differences in source locations. This is essential for correctness of the
  interpreter: when the goal matches an assumption in the context, they must be considered 
  the same regardless of their locations. Hashing ignores spans as well for consistency.

  The value of type T is located before the span, for efficiency. Accessing the first 
  element is generally faster, and the value of type T is generally accessed more often
  as a rule, because spans are primarily used for error reporting.
 */
#[derive(Clone, Debug, Copy)]
pub struct Spanned<T> {
    /** The underlying AST node to which the span is associated. */
    pub node: T,
    /** The node's corresponding location.  */
    pub span: Span,
}

/** Ignore span when hashing spanned values. */
impl<T: Hash> Hash for Spanned<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node.hash(state);
    }
}

/** Ignore span when comparing spanned values. */
impl<T: PartialEq> PartialEq for Spanned<T> {
  fn eq(&self, other: &Self) -> bool {
    self.node.eq(&other.node)
  }
}

/** Spanned values satisfy equality axioms. */
impl<T: Eq> Eq for Spanned<T> {}

/** Package value with its span.
 
 This name is inspired by a corresponding function in the Rust compiler.
 */
pub fn respan<T>(sp: Span, t: T) -> Spanned<T> {
    Spanned { node: t, span: sp }
}

/** A compile error is a message equipped with location information. */
pub type CompileError = Spanned<String>;
/** A compile result is a result whose error is a compile error. */
pub type CompileResult<T> = Result<T, CompileError>;

/** Terms of PDLP. 
 Terms have values drawn from enumerations. The possible enumeration values are defined at 
 the variable declaration site.

 Though not a standard part of PDL syntax, enumeration terms are a conservative extension of PDL, 
 as they result in finitely many states which can be encoded as finitely many predicates.

 VarTerm(x): takes its value from the state. Potential values vs are determined by VarDefn(x,vs)
 ValTerm(v): value is v regardless of state
*/
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub enum TermNode {
  VarTerm(String),
  ValTerm(String),
}
pub type Term = Spanned<TermNode>;

/** Formulas of PDL.

Formulas have true-false values, which depend on the current state. Each case corresponds
to one case of the PDL formula syntax:

True(): formula true, which is true in all states
Pred(s): nullary predicate s, whose true is directly determined by the state. Predicates
  are universal and ground. They cannot be redefined by unification.
Equal(e1, e2): equality formula e1 = e2 holds if terms e1 and e2 have same values in current state.
  Equality formulas are only available in PDLP, not DDLP.
Imply(p, q): implication formula p -> q holds if q is true or p is false

And(p, q): conjunction p & q holds if both p,q do
Or(p, q): disjunction p | q holds if either p,q do
MBox(a, p): box modality [a]p holds if, for all the possible behaviors of nondeterministic 
  program a, postcondition p holds.
MDiamond(a, p): diamond modality <a>p holds if, for some possible behavior of nondeterministic
  program a, postcondition p holds.
*/
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub enum FormulaNode {
    True(),
    Pred(String),
    Equal(Box<Term>, Box<Term>),
    Imply(Box<Formula>, Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    MBox(Box<Program>, Box<Formula>),
    MDiamond(Box<Program>, Box<Formula>)
}
pub type Formula = Spanned<FormulaNode>;

/** Programs of PDL.

Programs are nondeterministic. Their job is to change the state. The meaning of a program
is typically understood by giving all the possible (start_state, end_state) pairs. For
a given state, there could be one end state (deterministic program), multiple end states
(nondeterministic behavior), or zero end states (representing failure). Each case of the
type corresponds to one case of the PDL program syntax:

Symbol(c): Program symbol c represents a fixed but arbitrary program.
Test(p): test ?p does nothing if p holds, fails if p is false
Seq(a, b): sequential program a;b runs a first, then b in the resulting state.
Choice(a, b): choice a U b runs either a or b, but not both
Loop(a, J): loop a* runs program a repeatedly, any finite number of times including zero.
  Formally, invariant J is not part of the program, but rather guidance to the proof search
  algorithm. The proof search algorithm will only try to prove properties [a*]P by proving
  that J holds as an invariant and J implies P. The (disjuncts of) formula [J] must belong to
  a class of formulas called invariant formulas, defined in [statics]. Invariants with many
  disjuncts will increase the complexity of proof search.

  Invariant annotations are not used for diamond loops <a*>. To streamline the data structure
  in this case, we use a default invariant of True for all diamond loops.
*/
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub enum ProgramNode {
    Symbol(String),
    Test(Box<Formula>),
    Seq(Box<Program>, Box<Program>),
    Choice(Box<Program>, Box<Program>),
    Loop(Box<Program>, Box<Formula>),
}
pub type Program = Spanned<ProgramNode>;

/** Definitions of programs and predicates.

A definition introduces a new state variable, program symbol or predicate. VarDefn(x, vs) defines variable x 
to be an enumeration of values vs. Definition ProgDefn(c, p) explicitly defines
symbol c to mean program p. The definition must not be recursive. PredDefn(fmls) defines a predicate
by a set of formulas. A PredDefn can either define a single nullary predicate (atomic predicate definition)
or provide an _implicit definition_ of a single program symbol (box predicate or diamond predicate definition).

In both cases, every formula must be a simple clause of form a1 -> .. -> aN where every a1 is 
either:
 - an atomic predicate p, or
 - a box [c]p of a symbol and predicate, or
 - a diamond <c>p of a symbol and predicate. 
In the case of an atomic predicate definition, the same atomic predicate p must be the head of every clause. In the case of
a box predicate definition, every clause must end in a box of form [c]p and each clause must share the
same c, but the postcondition p may (and usually does) vary. Diamond predicates are likewise for <c>p.

Variable definitions are introduced in PDLP, not DDLP.
*/
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub enum DefnNode {
    ProgDefn(String, Box<Program>),
    PredDefn(Vec<Formula>),
    VarDefn(String, Vec<String>),
}
pub type Defn = Spanned<DefnNode>;

/** A complete logic program

A complete logic program consists of a series of program and predicate definitions (its body)
and a query with respect to that body. A program is executed by backward-chaining search starting
from the query, which proceeds by appealing to the definitions.
*/
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct LogicProgram {
    pub body: Vec<Defn>,
    pub query: Box<Formula>,
}

/** A command provided by the user in interactive mode

The interactive mode of the language allows the programmer to give commands one at a time. 
These commands go beyond the basic syntax of logic programs because a user may wish to
inspect the state of the program so far or to inspect program documentation. This type
represents all commands that the user can enter in interactive mode.

The DoNothing() command is never meant to be entered explicitly by the user. It is an
implementation detail, used when a value of type REPLCommand is needed but no meaningful
command is available from the user, such as in the case where retrieving user input fails.
*/
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub enum REPLCommand {
    DoNothing(),
    Help(),
    Quit(),
    Print(),
    Define(Vec<Defn>),
    Query(Box<Formula>),
}