/** Generate Nim games for benchmarking.
 * The full correctness property is a GL property, so instead we prove just the invariant.
 * 
 * @TODO: Consider introducing compositional mechanism for creating exponentially large games.
 */
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct Nim {
    pub piles : i64,
    pub size : i64,
}

impl Nim {
    /** Generate pi : enum {d0, .., dj} for i in 1..piles, j in 0..size. */
    fn to_var_defns(&self) -> String {
        let mut s = "".to_string();
        for i in 1..=self.piles {
            s.push_str(&format!("p{} : enum {{",i));
            for j in 0..self.size {
                s.push_str(&format!("d{}, ", j));
            }
            s.push_str(&format!("d{}",self.size));
            s.push_str("}.\n");
        }
        s
    }

    /** Generate pi=j -> <takei> pi=k for i in 1..piles, j in 1..size, k in 0..j-1 */
    fn to_take_each_defns(&self) -> String {
        let mut s = "".to_string();
        for pile in 1..self.piles {
            for init in 1..=self.size {
                for post in 0..init {
                    s.push_str(&format!("p{}=d{} -> <take{}>p{}=d{}\n",pile,init,pile,pile,post));
                }
            }
        }
        s
    }

    /* Generate take ::= take1 U ... U takek. for k=piles */
    fn to_take_defn(&self) -> String {
        let mut s = "".to_string();
        s.push_str("take ::= ");
        for pile in 1..=self.piles {
            let conj = if pile == self.piles { ".\n" } else { "U "};
            s.push_str(&format!("take{} {}", pile, conj));
        }
        s
    }

    /** Compute whether the given state has nimber 0 or not */
    fn has_nimber_zero(state: &Vec<i64>) -> bool {
        let mut acc : i64 = 0;
        for v in state {
            acc = acc ^ v;
        }
        acc == 0
    }

    /** Compute whether the given state has nimber 0 or not */
    fn is_zero_state(state: &Vec<i64>) -> bool {
        for v in state {
            if *v != 0 {
                return false;
            }
        }
        true
    }
    
    /** Generate the collection of all states of the given Nim game whose nimber is 0 */
    fn nimber_zero_states(&self) -> Vec<Vec<i64>> {
        let mut all_states : Vec<Vec<Vec<i64>>> = vec![];
        all_states.push(vec![]); 
        while all_states.last().expect("Initialized to nonempty vector").len() 
          < self.piles.try_into().unwrap() {
            let mut acc : Vec<Vec<i64>> = vec![];
            let prev = all_states.last().expect("Initialized to nonempty vector");
            for base in prev {
                for next in 0..=self.size {
                    let mut state : Vec<i64> = base.clone();
                    state.push(next);
                    if Self::has_nimber_zero(&state) {
                        acc.push(state)
                    }
                }
            }
            all_states.push(acc);
        }
        all_states.into_iter().flatten().collect()
    }

    /** Generate the collection of all states of the given Nim game whose nimber is 0 */
    fn nonzero_nimber_zero_states(&self) -> Vec<Vec<i64>> {
        let mut nzs = self.nimber_zero_states();
        nzs.retain(|x| !Self::is_zero_state(&x));
        nzs
    }
    
    /** Generate p0=d0 & ... & pk=dk for state = [d0,...,dk] */
    fn state_to_str(v : &Vec<i64>) -> String {
        let mut s = "".to_string();
        for i in 0..v.len()-1 {
            s.push_str(&format!("p{}=d{} &", i, v[i]));
        }
        s.push_str(&format!("p{}=d{} &", v.len()-1, v[v.len()-1]));
        s
    }

    /** Generate  state -> inv for all 0-nimber states */
    fn to_inv_defn(&self) -> String {
      let mut s = "".to_string();
      let states = self.nimber_zero_states();
      for state in states {
        for i in 1..=state.len() {
            let n = state[i-1];
            let conj = if i == state.len() { "-> inv." } else {"& "};
            s.push_str(&format!("p{}=d{} {}", i, n, conj));
        }
      }
      s        
    }

    /** Generate query ?- state0 -> [take]<take>inv & ... & stateN -> [take]<take>inv.
     * for all 0-nimber states.  */
    fn to_query(&self) -> String {
        let mut s = "".to_string();
        let states = self.nonzero_nimber_zero_states();
        for i in 0..states.len() {
            let conj = if i == 0 { "?- " } else { "\n&" };
            s.push_str(&format!("{}({} -> [take]<take>inv)", conj, Self::state_to_str(&states[i])));
        }
        s.push_str(".");
        s
    }

    /** Generate complete Nim source */
    pub fn to_source(&self) -> String {
        let mut s = "".to_string();
        s.push_str(&self.to_var_defns());
        s.push_str(&self.to_take_each_defns());
        s.push_str(&self.to_take_defn());
        s.push_str(&self.to_inv_defn());
        s.push_str(&self.to_query());  
        s  
    }
}