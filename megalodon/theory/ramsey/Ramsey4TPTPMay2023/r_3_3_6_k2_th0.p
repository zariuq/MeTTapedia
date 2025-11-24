thf(rtp,type,(r : ($i > $i > $o))).
thf(rsym,axiom,(! [X:$i] : (! [Y:$i] : ((r @ X @ Y) => (r @ Y @ X))))).
thf(rn3cl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | (~(r @ X @ Y)) | (~(r @ X @ Z)) | (~(r @ Y @ Z))))))).
thf(rn3acl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | (r @ X @ Y) | (r @ X @ Z) | (r @ Y @ Z)))))).
thf(ftp,type,(f : ($i > $i))).
thf(ctp,type,(c : $i)).
thf(f6ck,axiom,((f @ (f @ (f @ (f @ (f @ (f @ c)))))) != (f @ c))).
thf(f62ck,axiom,((f @ (f @ (f @ (f @ (f @ (f @ c)))))) != (f @ (f @ c)))).
thf(f63ck,axiom,((f @ (f @ (f @ (f @ (f @ (f @ c)))))) != (f @ (f @ (f @ c))))).
thf(f64ck,axiom,((f @ (f @ (f @ (f @ (f @ (f @ c)))))) != (f @ (f @ (f @ (f @ c)))))).

