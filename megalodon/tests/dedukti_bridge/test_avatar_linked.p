% AVATAR-style splits with linked shared literals across splits
cnf(c1, axiom, (p | q)).
cnf(c2, axiom, (r | s)).
cnf(c3, axiom, (~p | a)).
cnf(c4, axiom, (~q | a)).
cnf(c5, axiom, (~r | ~a)).
cnf(c6, axiom, (~s | ~a)).
cnf(c7, axiom, (~a)).
