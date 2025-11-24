thf(rtp,type,(r : ($i > ($i > $o)))).
thf(v0tp,type,(v0 : $i)).
thf(v1tp,type,(v1 : $i)).
thf(v2tp,type,(v2 : $i)).
thf(v3tp,type,(v3 : $i)).
thf(v4tp,type,(v4 : $i)).
thf(v5tp,type,(v5 : $i)).
thf(rsym,axiom,(! [X:$i] : (! [Y:$i] : (~(r @ X @ Y) | (r @ Y @ X))))).
thf(rno3cl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | ~(r @ X @ Y) | ~(r @ X @ Z) | ~(r @ Y @ Z)))))).
thf(rno3acl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | (r @ X @ Y) | (r @ X @ Z) | (r @ Y @ Z)))))).
thf(v0nv1,axiom,(v0 != v1)).
thf(v0nv2,axiom,(v0 != v2)).
thf(v1nv2,axiom,(v1 != v2)).
thf(v0nv3,axiom,(v0 != v3)).
thf(v1nv3,axiom,(v1 != v3)).
thf(v2nv3,axiom,(v2 != v3)).
thf(v0nv4,axiom,(v0 != v4)).
thf(v1nv4,axiom,(v1 != v4)).
thf(v2nv4,axiom,(v2 != v4)).
thf(v3nv4,axiom,(v3 != v4)).
thf(v0nv5,axiom,(v0 != v5)).
thf(v1nv5,axiom,(v1 != v5)).
thf(v2nv5,axiom,(v2 != v5)).
thf(v3nv5,axiom,(v3 != v5)).
thf(v4nv5,axiom,(v4 != v5)).
