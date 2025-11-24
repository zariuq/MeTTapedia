cnf(rsym,axiom,(~r(X,Y) | r(Y,X))).
cnf(rno3cl,axiom,(X = Y | X = Z | Y = Z | ~r(X,Y) | ~r(X,Z) | ~r(Y,Z))).
cnf(rno5acl,axiom,(X = Y | X = Z | Y = Z | X = W | Y = W | Z = W | X = U | Y = U | Z = U | W = U | r(X,Y) | r(X,Z) | r(Y,Z) | r(X,W) | r(Y,W) | r(Z,W) | r(X,U) | r(Y,U) | r(Z,U) | r(W,U))).
cnf(pfnc,axiom,(f(X) != c)).
cnf(pfinj,axiom,((f(X) != f(Y)) | (X = Y))).
