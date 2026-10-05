/** Test the EDSL implementation of DDLP by reproducing and running example programs in EDSL syntax. */
#[cfg(test)]
mod tests {
    /** Run the (bb)* example */
    #[test]
    fn nfa_2b() {
      let is_finished = 
        glp::lp![
          s >= fin,
          s >= a[b], a >= s[b], d >= d[b],
          a >= d[a], s >= d[a], d >= d[a];
        ?- s >= fin[(b / b) * s]];
      assert!(is_finished);
    }   

    /** Run the (a U b)* example */
    #[test]
    fn nfa_abs() {
      let is_finished =
        glp::lp![
          s >= fin,
          s >= s[a], d >= d[a],
          s >= s[b], d >= d[b],
          s >= d[c], d >= d[c];
        ?- s >= fin[(a || b) * s]];
      assert!(is_finished);
    }

    /** Run the FLOPS 2026 PEG example */
    #[test]
    fn paper_peg() {
      let is_finished = 
        glp::lp![
          ac >= ab[l], bd >= bc[l], ca >= cd[l], db >= da[l],
          ac >= ad[r], bd >= ba[r], ca >= cb[r], db >= dc[r],
          demon_turn <= l || r,
          ab >= db[la], bc >= ac[la], cd >= bd[la], da >= ca[la],
          ad >= bd[ra], ba >= ca[ra], cb >= db[ra], dc >= ac[ra],
          angel_turn <= (ab? / la || bc? / la || cd? / la || da? / la) 
                     || (ad? / ra || ba? / ra || cb? / ra || dc? / ra);
          ?- ac >= ((ac | bd | ca | db)[(demon_turn / angel_turn)*(ac | bd | ca | db)])
          ];
      assert!(is_finished);
    }
}