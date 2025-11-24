cnf(rsym,axiom,(~r(X,Y) | r(Y,X))).
cnf(rno3cl,axiom,(X = Y | X = Z | Y = Z | ~r(X,Y) | ~r(X,Z) | ~r(Y,Z))).
cnf(rno3acl,axiom,(X = Y | X = Z | Y = Z | r(X,Y) | r(X,Z) | r(Y,Z))).
cnf(v0nv1,axiom,(v0 != v1)).
cnf(v0nv2,axiom,(v0 != v2)).
cnf(v1nv2,axiom,(v1 != v2)).
cnf(v0nv3,axiom,(v0 != v3)).
cnf(v1nv3,axiom,(v1 != v3)).
cnf(v2nv3,axiom,(v2 != v3)).
cnf(v0nv4,axiom,(v0 != v4)).
cnf(v1nv4,axiom,(v1 != v4)).
cnf(v2nv4,axiom,(v2 != v4)).
cnf(v3nv4,axiom,(v3 != v4)).
cnf(v0nv5,axiom,(v0 != v5)).
cnf(v1nv5,axiom,(v1 != v5)).
cnf(v2nv5,axiom,(v2 != v5)).
cnf(v3nv5,axiom,(v3 != v5)).
cnf(v4nv5,axiom,(v4 != v5)).
