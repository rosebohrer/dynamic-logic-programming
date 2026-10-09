/** One-player guessing game where Angel has to perfectly guess a secret word.
 * Intended to test the speedup associated with compositional synthesis, for
 * which it is expected to show near-optimal speedup.
 */

 /** Instance of a guessing game */
#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct Guesser {
    /** The secret to be guessed */
    pub secret: Vec<bool>, 
}

impl Guesser {
    const ID_SECRET : &str = "secret";
    /** Construct from given secret  */
    pub fn new(secret : Vec<bool>) -> Self {
        Guesser { secret }
    }

    /** Construct at given size using default pattern (alternating) */
    pub fn of_size(n: usize) -> Self {
        let mut secret : Vec<bool> = vec![];
        let mut v = false;
        for _ in 0..n {
            v = !v;
            secret.push(v);
        }
        Guesser { secret }
    }

    /** Generate variable defns */
    fn var_defn(&self) -> String {
        let mut s = "".to_string();
        for i in 0..self.secret.len() {
            s.push_str(&format!("g{} : enum {{b0, b1}}\n", i));
        }
        s
    }

    /** Generate definition of secret predicate */
    fn secret_defn(&self) -> String {
        let mut s = format!("{} <- ", Self::ID_SECRET).to_string();
        for i in 0..self.secret.len() {
            let bit = if self.secret[i] { "b1" } else { "b0" };
            let delim = if i+1 == self.secret.len() { ".\n" } else { " & " };
            s.push_str(&format!("g{}={} {}", i, bit, delim));
        }
        s
    }

    /** Generate definitions of setter symbols. */
    fn setter_defn(&self) -> String {
        let mut s = "".to_string();
        for i in 0..self.secret.len() {
            s.push_str(&format!("<set{}>g{}=b0. <set{}>g{}=b1.\n", i, i, i, i,));
        }
        s
    }

    /** Generate main query, same for one-shot and multi-shot implementations. */
    fn main_query(&self) -> String {
        let mut s = "?- ".to_string();
        for i in 0..self.secret.len() {
            s.push_str(&format!("<set{}>", i));
        }
        s.push_str(&"secret.");
        s
    }

    /** Generate complete source of single-shot implementation.  */
    pub fn to_source_single(&self) -> String {
        let mut s = "".to_string();
        s.push_str(&self.var_defn());
        s.push_str(&self.secret_defn());
        s.push_str(&self.setter_defn());
        s.push_str(&self.main_query());
        s
    }

    /** Generate string for conjunction of formulas encoding one state. */
    fn state_fml(bits: &Vec<bool>) -> String {
        if bits.len() == 0 { 
            return "true".to_string(); 
        }
        let mut s = "".to_string();
        for i in bits.len()-1..bits.len() {
            let delim = ""; //if i == 0 { "" } else { " & " };
            let bit = if bits[i] { "1" } else { "0" };
            s.push_str(&format!("{}g{}=b{}", delim, i, bit));
        }
        s
    }

    /* Like state_fml but for one bit */
    fn bit_fml(i: usize, bit_b: bool) -> String {
        let bit = if bit_b { "1" } else { "0" };
        format!("g{}=b{}", i, bit)
    }

    /** Generate query for lemma file of multi-shot implementation. */
    fn lemma_query(&self) -> String {
        let mut s = "".to_string();
        for i in 0..self.secret.len() {
            let before = if i == 0 { "?- " } else {"& "};
            let after = if i+1 == self.secret.len() { "." } else { "\n "};
            let after_state = Self::bit_fml(i, self.secret[i]);
            //s.push_str(&format!("{}({} -> <set{}>({})){}",before,pre_state,i,after_state,after));
            s.push_str(&format!("{}(<set{}>({})){}",before,i,after_state,after));
        }
        s
    }

    /** Generate multi-shot implementation source, lemma file. */
    pub fn to_source_lemmas(&self) -> String {
        let mut s = "".to_string();
        s.push_str(&self.var_defn());
        s.push_str(&self.setter_defn());
        s.push_str(&self.lemma_query());
        s
    }

    /** Generate definitions for lemma used in combiner file of multi-shot implementation. */
    fn lemma_defn(&self) -> String {
        let mut s = "".to_string();
        let mut acc : Vec<bool> = vec![];
        for i in 0..self.secret.len() {
            //let pre_state = Self::state_fml(&acc);
            acc.push(self.secret[i]);
            let after_state = Self::state_fml(&acc);
            //s.push_str(&format!("{} -> <set{}>({}).\n",pre_state,i,after_state));
            s.push_str(&format!("<set{}>({}).\n",i,after_state));
        }
        s
    }

    /** Generate multi-shot implementation source, combiner file. */
    pub fn to_source_combiner(&self) -> String {
        let mut s = "".to_string();
        s.push_str(&self.var_defn());
        s.push_str(&self.secret_defn());
        s.push_str(&self.lemma_defn());
        s.push_str(&self.main_query());
        s
    }
}