/** Provides a macro for writing code inside of Rust programs as an EDSL.
 * 
 * The macro performs minimal work at compile-time. It accepts Rust expressions for the body
 * and query of a program, then converts them to a string which is parsed at runtime.
 * The macro returns a boolean indicating whether the query was proved successfully.
 * 
 * Because it is implemented as a macro-by-example, the code must follow valid Rust syntax.
 * The implementation itself is simple, but major notation changes are made to fit Rust syntax.
 * The following table describes the syntax changes:
 * 
 * DDLP Concrete Syntax  |  Rust EDSL Syntax
 * ----------------------------------------
 * p&q                   |   p?q
 * p|q                   |   p|q
 * p->q                  |   p >= q
 * p<-q                  |   p <= q
 * [a]p                  |   p[a]
 * <a>p                  |   p <<= a
 * 
 * a U b                 |   a || b
 * a ; b                 |   a / b
 * ?p                    |   p?
 * a@inv(p)              |   a * p 
 * 
 * c ::= a               |   c <= a
 * 
 * p <- q1, q2           |   q1 & q2 >> p
 * clause1. clause2.     |   clause1, clause2
 * body ?- query.        |   body; ?- query
 * 
 * Example:
 *  glp::lp![
 *       s >> fin,
 *       s >> a[b], a >> s[b], d >> d[b],
 *       a >> d[a], s >> d[a], d >> d[a];
 *       ?- s >> fin[(b / b) * s]];  
 */
#[macro_export] macro_rules! lp {
    ( $( $e:expr ),* ; ?- $q:expr) => {
        {
            let mut src = "".to_string();
            $( src.push_str(stringify!{ $e });
               src.push_str(";\n"); )*
            let qsrc = format!("\n {}", stringify!{ $q }).to_string();
            src.push_str(&qsrc);
            let lp = glp::parser::pdlp::edsl_logic_program(&src).unwrap();
            let lpn = glp::statics_common::normalize(*lp).unwrap();
            let mut sm = glp::ddlp::dynamics::StaticMachine::new();
            let mut m = glp::ddlp::dynamics::Machine::of_lp(&mut sm, &lpn);
            m.run();
            m.is_proved()
        }
    };
}