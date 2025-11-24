cnf(rsym,axiom,(~r(X,Y) | r(Y,X))).
cnf(rn3cl,axiom,(X = Y | X = Z | Y = Z | ~r(X,Y) | ~r(X,Z) | ~r(Y,Z))).
cnf(rn3acl,axiom,(X = Y | X = Z | Y = Z | r(X,Y) | r(X,Z) | r(Y,Z))).
cnf(f6ck,axiom,(f(f(f(f(f(f(c)))))) != f(c))).
cnf(f62ck,axiom,(f(f(f(f(f(f(c)))))) != f(f(c)))).
cnf(f63ck,axiom,(f(f(f(f(f(f(c)))))) != f(f(f(c))))).
cnf(f64ck,axiom,(f(f(f(f(f(f(c)))))) != f(f(f(f(c)))))).
