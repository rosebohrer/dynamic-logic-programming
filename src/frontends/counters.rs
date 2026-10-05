/*! From the literature on finite LTL and finite linear DL, games about counters */

#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct DoubleCounter {
    pub bits: i32,
    pub init: i32,
}

impl DoubleCounter {
    pub fn to_source(&self) -> String {
        let mut s = "".to_string();
        for i in 1..=self.bits {
            s.push_str(&format!("b{} : enum {{z, o}}.\n", i));
            s.push_str(&format!("e{} : enum {{z, o}}.\n", i));
        }

        // Increment number b, non-overflow cases
        for i in 1..self.bits {
            for j in 1..i {
                s.push_str(&format!("b{}=o & ", j));
            }
            s.push_str(&format!("b{}=z -> <inc>(", i));
            for j in 1..i {
                s.push_str(&format!("b{}=z & ", j));
            }
            s.push_str(&format!("b{}=o).\n", i));   
        }

        // Increment number b, overflow case
        for j in 1..self.bits {
            s.push_str(&format!("b{}=o & ", j));
        }
        s.push_str(&format!("b{}=o -> <binc>(", self.bits));
        for j in 1..self.bits {
            s.push_str(&format!("b{}=z & ", j));
        }
        s.push_str(&format!("b{}=z).\n", self.bits));   

        // Increment number e, overflow case
        for i in 1..self.bits {
            for j in 1..i {
                s.push_str(&format!("e{}=o & ", j));
            }
            s.push_str(&format!("e{}=z -> <inc>(", i));
            for j in 1..i {
                s.push_str(&format!("e{}=z & ", j));
            }
            s.push_str(&format!("e{}=o).\n", i));   
        }

        // Increment number e, overflow case.
        for j in 1..self.bits {
            s.push_str(&format!("e{}=o & ", j));
        }
        s.push_str(&format!("e{}=o -> <inc>(", self.bits));
        for j in 1..self.bits {
            s.push_str(&format!("e{}=z & ", j));
        }
        s.push_str(&format!("e{}=z).\n", self.bits));
        s.push_str(&format!("steps ::= (binc U ?true) ; (inc ; inc U inc)\n"));
        
        // query
        s.push_str("?- ");
        let mut acc = self.init;
        for i in 1..=self.bits {
            s.push_str(&format!("e{}=z & ", i));
            let b = if acc & 0x1 == 0x1 { "o" } else { "z" };
            acc = acc << 1;
            let conj = if i == self.bits { "-> " } else { "& "};
            s.push_str(&format!("b{}={} {}",i,b,conj));
        }
        s.push_str("<steps*>(");
        for i in 1..=self.bits {
            let conj = if i == self.bits { ").\n" } else { "& "};
            s.push_str(&format!("b{}=e{} {}",i,i,conj));
        }
        s
    }
}

#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct SingleCounter {
    pub bits: i32,
    pub init: i32, 
}

impl SingleCounter {
    pub fn to_source(&self) -> String {
        let mut s = "".to_string();

        for i in 1..=self.bits {
            s.push_str(&format!("b{} : enum {{z, o}}.\n", i));
        }

        for i in 1..self.bits {
            for j in 1..i {
                s.push_str(&format!("b{}=o & ", j));
            }
            s.push_str(&format!("b{}=z -> <inc>(", i));
            for j in 1..i {
                s.push_str(&format!("b{}=z & ", j));
            }
            s.push_str(&format!("b{}=o).\n", i));   
        }

        for j in 1..self.bits {
            s.push_str(&format!("b{}=o & ", j));
        }
        s.push_str(&format!("b{}=o -> <inc>(", self.bits));
        for j in 1..self.bits {
            s.push_str(&format!("b{}=z & ", j));
        }
        s.push_str(&format!("b{}=z).\n", self.bits));   

        s.push_str("steps ::= inc U (inc; inc).\n\n?- ");
        let mut acc = self.init;
        for i in 1..=self.bits {
            let b = if acc & 0x1 == 0x1 { "o" } else { "z" };
            acc = acc << 1;
            let conj = if i == self.bits { "-> " } else { "& "};
            s.push_str(&format!("b{}={} {}",i,b,conj));
        }
        s.push_str("<steps*>(");
        for i in 1..=self.bits {
            let conj = if i == self.bits { ")." } else { "& "};
            s.push_str(&format!("b{}=z {}",i,conj));
        }
        return s;
    }
}