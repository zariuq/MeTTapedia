thf(rtp,type,(r : ($i > ($i > $o)))).
thf(rsym,axiom,(! [X:$i] : (! [Y:$i] : (~(r @ X @ Y) | (r @ Y @ X))))).
thf(rno3cl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | ~(r @ X @ Y) | ~(r @ X @ Z) | ~(r @ Y @ Z)))))).
thf(rno4acl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : (! [W:$i] : ((X = Y) | (X = Z) | (X = W) | (Y = Z) | (Y = W) | (Z = W) | (r @ X @ Y) | (r @ X @ Z) | (r @ X @ W) | (r @ Y @ Z) | (r @ Y @ W) | (r @ Z @ W))))))).
thf(ctp,type,(c :$i)).
thf(ftp,type,(f :($i > $i))).
thf(pfnc,axiom,(! [X:$i] : ((f @ X) != c))).
thf(pfinj,axiom,(! [X:$i] : (! [Y:$i] : (((f @ X) = (f @ Y)) => (X = Y))))).
