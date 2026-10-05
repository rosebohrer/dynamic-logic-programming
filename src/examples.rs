/*! Example programs written in DDLP and PDLP.

The example applications include pursuit-evasion games and state machines.
These same examples are also provided as separate files in the examples folder.
Though the duplication is unfortunate, it is preferable to provide these
tests in a Rust source file so that they can be used efficiently in test
cases without introducing a dependency on the filesystem in testing.
*/

/** Example pursuit-evasion game from FLOPS2026 paper */
pub const FLOPS_PEG : &str = 
"[l]ab <- ac. [l]bc <- bd. [l]cd <- ca. [l]da <- db.
 [r]ad <- ac. [r]ba <- bd. [r]cb <- ca. [r]dc <- db.

 demon-turn ::= l U r.

 [la]db <- ab. [la]ac <- bc. [la]bd <- cd. [la]ca <- da.
 [ra]bd <- ad. [ra]ca <- ba. [ra]db <- cb. [ra]ac <- dc.

 angel-turn ::= (?ab;la U ?bc;la U ?cd;la U ?da;la) U (?ad;ra U ?ba;ra U ?cb;ra U ?dc;ra).
 
 ?- ac -> [(demon-turn;angel-turn)*@inv(ac|bd|ca|db)] (ac|bd|ca|db).
";

/** Implements the DFA {bb}* over alphabet Sigma = {a, b}; */
pub const DFA_2B : &str =
"final <- s.

[b]a <- s. [b]s <- a. [b]d <- d.
[a]d <- a. [a]d <- s. [a]d <- d.

?- s -> [(b;b)*@inv(s)] final.
";

/**  Implements the DFA (a U b)* over alphabet Sigma = {a, b, c}; */
pub const DFA_ABS : &str =
"final <- s.

[a]s <- s. [a]d <- d.
[b]s <- s. [b]d <- d.
[c]d <- s. [c]d <- d.

?- s -> [(a U b)*@inv(s)] final.
";

// Alternating a's and b's, 2 or more 
pub const AB_ALT_NDFA : &str = 
"<a>true. <b>true.
q : enum {q0,q1,q2,q3}
q=q0 -> start.
q=q0 -> [a]q=q1.  q=q0 -> [b]q=q2.
q=q1 -> <b>q=q2.  q=q1 -> <b>q=q3.  q=q2 -> <a>q=q1.  q=q2 -> <a>q=q3.
q=q3 -> accept.";

pub const AB_ALT_DFA : &str = 
"<a>true. <b>true.

q : enum {q0,q1,q2,q3,q4,q5}.

q=q0 -> start.
q=q0 -> [a]q=q1. q=q0 ->[b]q=q2
q=q1 -> [a]q=q5. q=q1 ->[b]q=q3.
q=q2 -> [a]q=q4. q=q2 ->[b]q=q5.
q=q3 -> [a]q=q4. q=q3 ->[b]q=q5.
q=q4 -> [a]q=q5. q=q4 ->[b]q=q3.
q=q5 -> [a U b]q=q5.

q=q3 -> accept. q=q4 -> accept.";

pub const POPL_PEG_SIMP : &str =
"
pa : enum {a, b, c, d}
pd : enum {a, b, c, d}

pa='a-><accw>pa='d. pa='a-><acw>pa='b.
pd='c->[dccw]pd='b.   

ta ::= (accw U acw). 
td ::= dccw.

?-  pa = 'a & pd = 'c -> [td]<ta> ((pa='b&pd='d)|(pa='d&pd='b)).
";

pub const POPL_PEG : &str = 
"pa : enum {a, b, c, d}
pd : enum {a, b, c, d}

pa='a-><accw>pa='d. pa='b-><accw>pa='a. pa='c-><accw>pa='b. pa='d-><accw>pa='c.
pa='a-><acw>pa='b.  pa='b-><acw>pa='c.  ap='c-><acw>pa='d.  pa='d-><acw>pa='a.

pd='a->[dccw]pd='d. pd='b->[dccw]pd='a. pd='c->[dccw]pd='b. pd='d->[dccw]pd='c.
pd='a->[dcw]pd='b.  pd='b->[dcw]pd='c.  pd='c->[dcw]pd='d.  pd='d->[dcw]pd='a.

ta ::= 
( ?(pa = 'a & pd = 'b) U ?(pa = 'a & pd = 'c) U ?(pa = 'a & pd = 'd) 
U ?(pa = 'b & pd = 'a) U ?(pa = 'b & pd = 'c) U ?(pa = 'b & pd = 'd) 
U ?(pa = 'c & pd = 'a) U ?(pa = 'c & pd = 'b) U ?(pa = 'c & pd = 'd) 
U ?(pa = 'd & pd = 'a) U ?(pa = 'd & pd = 'b) U ?(pa = 'd & pd = 'c))
; (accw U acw).
td ::= dccw U dcw.

?-  pa = 'a & pd = 'c -> [td]<ta> (pa='a&pd='c|pa='b&pd='d|pa='c&pd='a|pa='d&pd='b).
";
 
pub const NFA_CHAR : &str =
"
q : enum {q0,q1}
q=q0 -> <a>q=q0.
q=q0 -> <b>q=q1.
q=q1 -> accept.

?- q=q0 -> <a U b>accept.
";

pub const POPL_NFA_SIMP : &str = 
"
q : enum {q0,q1,q2,q3}
q=q0 -> start.
q=q0 -> <a>q=q1. q=q0 -> <b>q=q2.
q=q1 -> <b>q=q2. q=q1 -> <b>q=q3. 
q=q2 -> <a>q=q1. q=q2 -> <a>q=q3.
q=q3 -> accept.

?- q=q0 -> <(a U b); (a U b); (a U b)>accept.
";


pub const POPL_NFA : &str = 
"
q : enum {q0,q1,q2,q3}
<a>true. <b>true.
q=q0 -> start.
q=q0 -> [a]q=q1. q=q0 -> [b]q=q2.
q=q1 -> <b>q=q2. q=q1 -> <b>q=q3. 
q=q2 -> <a>q=q1. q=q2 -> <a>q=q3.
q=q3 -> accept.

?- q=q0 -> <(a U b); (a U b); (a U b)>accept.
";

pub const POPL_DFA : &str =
"
<a>true. <b>true.
q : enum {q0,q1,q2,q3}
q=q0 -> start.
q=q0 -> [a]q=q1. q=q0 -> [b]q=q2.
q=q1 -> [a]q=q5. q=q1 -> [b]q=q3.
q=q2 -> [a]q=q4. q=q2 -> [b]q=q5.
q=q3 -> [a]q=q4. q=q3 -> [b]q=q5.
q=q4 -> [a]q=q5. q=q4 -> [b]q=q3.
q=q5 -> [a]q=q5. q=q5 -> [b]q=q5.

q=q3 -> accept. q=q4 -> accept.

?- q=q0 -> <a>[(b;a)*@inv(q=q1 | q=q4)]<b>accept.
";

pub const ONE_COUNTER_CURRY : &str =
"
b1 : enum {z, o}
b2 : enum {z, o}
b1='z -> <inc>b1='o.
b1='o -> b2='z -> <inc>(b1='z & b2='o).
b1='o -> b2='o -> <inc>(b1='z & b2='z).
steps ::= inc U (inc; inc).

?- b1='o & b2='z -> <steps*>(b1='z & b2='z).
";

pub const ONE_COUNTER_CONJ : &str =
"
b1 : enum {z, o}
b2 : enum {z, o}
b1='z -> <inc>b1='o.
b1='o & b2='z -> <inc>(b1='z & b2='o).
b1='o & b2='o -> <inc>(b1='z & b2='z).
steps ::= inc U (inc; inc).

?- b1='o & b2='z -> <steps*>(b1='z & b2='z).
";

pub const TWO_COUNTERS : &str = 
"# Prove that our counter catches up with the other counter. Not a perfect encoding of the LTL property
b1 : enum {z, o}
b2 : enum {z, o}
e1 : enum {z, o}
e2 : enum {z, o}

b1='z -> <binc>b1='o.
b1='o & b2='z -> <binc>(b1='z & b2='o).
b1='o & b2='o -> <binc>(b1='z & b2='z).

e1='z -> <inc>e1='o.
e1='o & e2='z -> <inc>(e1='z & e2='o).
e1='o & e2='o -> <inc>(e1='z & e2='z).

steps ::= (binc U ?true) ; ((inc ; inc) U inc).

?- b1='o & b2='z & e0='z & e1='z -> <steps*>(b1='e1 & b2='e2).
";

pub const NIM_THREE_THREE : &str = "
p1 : enum {z, o, t, th}
p2 : enum {z, o, t, th}
p3 : enum {z, o, t, th}

p1='o -> <take1> p1='z.
p1='t -> <take1> p1='z.
p1='t -> <take1> p1='o.
p1='th -> <take1> p1='z.
p1='th -> <take1> p1='o.
p1='th -> <take1> p1='t.

p2='o -> <take2> p2='z.
p2='t -> <take2> p2='z.
p2='t -> <take2> p2='o.
p2='th -> <take2> p2='z.
p2='th -> <take2> p2='o.
p2='th -> <take2> p2='t.

p3='o -> <take3> p3='z.
p3='t -> <take3> p3='z.
p3='t -> <take3> p3='o.
p3='th -> <take3> p3='z.
p3='th -> <take3> p3='o.
p3='th -> <take3> p3='t.

take ::= take1 U take2 U take3.

p1='z & p2='z & p3='z -> inv.
p1='o & p2='o & p3='z -> inv.
p1='t & p2='t & p3='z -> inv.
p1='th & p2='th & p3='z -> inv.
p1='t & p2='o & p3='th -> inv.
p1='o & p2='t & p3='th -> inv.
p1='t & p2='th & p3='o -> inv.
p1='o & p2='th & p3='t -> inv.
p1='th & p2='t & p3='o -> inv.
p1='th & p2='o & p3='t -> inv.
p1='z & p2='o & p3='o -> inv.
p1='z & p2='t & p3='t -> inv.
p1='z & p2='th & p3='th -> inv.
p1='o & p2='z & p3='o -> inv.
p1='t & p2='z & p3='t -> inv.
p1='th & p2='z & p3='th -> inv.

?- (p1='o & p2='o & p3='z -> [take]<take>inv)
&(p1='t & p2='t & p3='z -> [take]<take>inv)
&(p1='th & p2='th & p3='z -> [take]<take>inv)
&(p1='t & p2='o & p3='th -> [take]<take>inv)
&(p1='o & p2='t & p3='th -> [take]<take>inv)
&(p1='t & p2='th & p3='o -> [take]<take>inv)
&(p1=o & p2='th & p3='t -> [take]<take>inv)
&(p1='th & p2='t & p3='o -> [take]<take>inv)
&(p1='th & p2='o & p3='t -> [take]<take>inv)
&(p1='z & p2='o & p3='o -> [take]<take>inv)
&(p1='z & p2='t & p3='t -> [take]<take>inv)
&(p1='z & p2='th & p3='th -> [take]<take>inv)
&(p1='o & p2='z & p3='o -> [take]<take>inv)
&(p1='t & p2='z & p3='t -> [take]<take>inv)
&(p1='th & p2='z & p3='th -> [take]<take>inv).
";

pub const NIM_THREE_THREE_SIMP : &str = "
p1 : enum {z, o, t, th}
p2 : enum {z, o, t, th}
p3 : enum {z, o, t, th}

p1='o -> <take1> p1='z.
p1='t -> <take1> p1='z.
p1='t -> <take1> p1='o.
p1='th -> <take1> p1='z.
p1='th -> <take1> p1='o.
p1='th -> <take1> p1='t.

p2='o -> <take2> p2='z.
p2='t -> <take2> p2='z.
p2='t -> <take2> p2='o.
p2='th -> <take2> p2='z.
p2='th -> <take2> p2='o.
p2='th -> <take2> p2='t.

p3='o -> <take3> p3='z.
p3='t -> <take3> p3='z.
p3='t -> <take3> p3='o.
p3='th -> <take3> p3='z.
p3='th -> <take3> p3='o.
p3='th -> <take3> p3='t.

take ::= take1 U take2 U take3.

p1='z & p2='z & p3='z -> inv.
p1='o & p2='o & p3='z -> inv.
p1='t & p2='t & p3='z -> inv.
p1='th & p2='th & p3='z -> inv.
p1='t & p2='o & p3='th -> inv.
p1='o & p2='t & p3='th -> inv.
p1='t & p2='th & p3='o -> inv.
p1='o & p2='th & p3='t -> inv.
p1='th & p2='t & p3='o -> inv.
p1='th & p2='o & p3='t -> inv.
p1='z & p2='o & p3='o -> inv.
p1='z & p2='t & p3='t -> inv.
p1='z & p2='th & p3='th -> inv.
p1='o & p2='z & p3='o -> inv.
p1='t & p2='z & p3='t -> inv.
p1='th & p2='z & p3='th -> inv.

?- (p1='th & p2='z & p3='th -> [take]<take>inv).
";

pub const GUESSER_SINGLE : &str =
"# Guessing game with a single-step query that is likely slow as length increases
# Example with a four-bit guess 
g0 : enum {b0, b1}
g1 : enum {b0, b1}
g2 : enum {b0, b1}
g3 : enum {b0, b1}

# encode the correct answer, e.g., <0,1,0,1>
secret <- g0=b1 & g1=b0 & g2=b1 & g3=b0.

# set each bit of the guess individually
<set0>g0=b0. <set0>g0=b1.
<set1>g1=b0. <set1>g1=b1.
<set2>g2=b0. <set2>g2=b1.
<set3>g3=b0. <set3>g3=b1.

# Search for an execution that finds the secret.
?- <set0><set1><set2><set3>secret.";

pub const GUESSER_MULTIA : &str =
"# Guessing game implemented across two files and two queries that is likely to 
# become more optimal as size increases.

# Example with a four-bit guess 
g0 : enum {b0, b1}
g1 : enum {b0, b1}
g2 : enum {b0, b1}
g3 : enum {b0, b1}

# set each bit of the guess individually
<set0>g0=b0. <set0>g0=b1.
<set1>g1=b0. <set1>g1=b1.
<set2>g2=b0. <set2>g2=b1.
<set3>g3=b0. <set3>g3=b1.

# Search for an execution that finds the secret.
?-  (<set0>g0=b1)
   &(g0=b1 -> <set1>(g0=b1&g1=b0))
   &(g0=b1&g1=b0 -> <set2>(g0=b1&g1=b0&g2=b1))
   &(g0=b1&g1=b0&g2=b1 -> <set3>(g0=b1&g1=b0&g2=b1&g3=b0)).";

pub const GUESSER_MULTIB : &str =
"# Guessing game implemented across two files and two queries that is likely to 
# become more optimal as size increases.

# Declare four bits of guess
g0 : enum {b0, b1} 
g1 : enum {b0, b1}
g2 : enum {b0, b1}
g3 : enum {b0, b1}

# encode the correct answer, e.g., <0,1,0,1>
secret <- g0=b1 & g1=b0 & g2=b1 & g3=b0.

# declare as assumptions the lemmas already proved in guesser_multiA.glp
<set0>g0=b1.
g0=b1 -> <set1>(g0=b1&g1=b0).
g0=b1&g1=b0 -> <set2>(g0=b1&g1=b0&g2=b1).
g0=b1&g1=b0&g2=b1 -> <set3>(g0=b1&g1=b0&g2=b1&g3=b0).

# Final query proves more quickly as result of lemmas
?- <set0><set1><set2><set3>secret.";