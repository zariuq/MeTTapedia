cnf(rsym,axiom,(~r(X,Y) | r(Y,X))).
cnf(rn3cl,axiom,(X = Y | X = Z | Y = Z | ~r(X,Y) | ~r(X,Z) | ~r(Y,Z))).
cnf(rn3acl,axiom,(X = Y | X = Z | Y = Z | r(X,Y) | r(X,Z) | r(Y,Z))).
cnf(pfnc,axiom,(f(X) != c)).
cnf(pfinj,axiom,((f(X) != f(Y)) | (X = Y))).

