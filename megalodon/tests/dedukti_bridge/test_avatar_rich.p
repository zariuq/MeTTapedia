% Richer AVATAR split: chain of choices forcing contradiction
% Clauses introduce multiple independent splits on p/q/r/s, plus linked literals.
cnf(c1, axiom, (p | q | r | s)).
cnf(c2, axiom, (~p | a | b)).
cnf(c3, axiom, (~q | b | c)).
cnf(c4, axiom, (~r | c | d)).
cnf(c5, axiom, (~s | d | e)).
cnf(c6, axiom, (~a)).
cnf(c7, axiom, (~c)).
cnf(c8, axiom, (~e)).
cnf(c9, axiom, (~b | ~d)).  % link branches
