thf(rtp,type,(r : ($i > ($i > $o)))).
thf(rsym,axiom,(! [X:$i] : (! [Y:$i] : (~(r @ X @ Y) | (r @ Y @ X))))).
thf(rno3cl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | ~(r @ X @ Y) | ~(r @ X @ Z) | ~(r @ Y @ Z)))))).
thf(rno5acl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : (! [W:$i] : (! [U:$i] : ((X = Y) | (X = Z) | (Y = Z) | (X = W) | (Y = W) | (Z = W) | (X = U) | (Y = U) | (Z = U) | (W = U) | (r @ X @ Y) | (r @ X @ Z) | (r @ Y @ Z) | (r @ X @ W) | (r @ Y @ W) | (r @ Z @ W) | (r @ X @ U) | (r @ Y @ U) | (r @ Z @ U) | (r @ W @ U)))))))).
thf(ctp,type,(c :$i)).
thf(ftp,type,(f :($i > $i))).
thf(pfnc,axiom,(! [X:$i] : ((f @ X) != c))).
thf(pfinj,axiom,(! [X:$i] : (! [Y:$i] : (((f @ X) = (f @ Y)) => (X = Y))))).
