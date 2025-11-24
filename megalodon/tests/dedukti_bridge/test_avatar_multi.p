% Multiple AVATAR splits: (p v q v r), (~p v s), (~q v t), (~r v u), ~s, ~t, ~u
cnf(c1, axiom, (p | q | r)).
cnf(c2, axiom, (~p | s)).
cnf(c3, axiom, (~q | t)).
cnf(c4, axiom, (~r | u)).
cnf(c5, axiom, (~s)).
cnf(c6, axiom, (~t)).
cnf(c7, axiom, (~u)).
