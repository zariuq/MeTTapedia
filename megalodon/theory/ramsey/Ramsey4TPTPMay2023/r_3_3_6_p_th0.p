thf(rtp,type,(r : ($i > ($i > $o)))).
thf(rsym,axiom,(! [X:$i] : (! [Y:$i] : (~(r @ X @ Y) | (r @ Y @ X))))).
thf(rno3cl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | ~(r @ X @ Y) | ~(r @ X @ Z) | ~(r @ Y @ Z)))))).
thf(rno3acl,axiom,(! [X:$i] : (! [Y:$i] : (! [Z:$i] : ((X = Y) | (X = Z) | (Y = Z) | (r @ X @ Y) | (r @ X @ Z) | (r @ Y @ Z)))))).
thf(ctp,type,(c :$i)).
thf(ftp,type,(f :($i > $i))).
thf(pfnc,axiom,(! [X:$i] : ((f @ X) != c))).
thf(pfinj,axiom,(! [X:$i] : (! [Y:$i] : (((f @ X) = (f @ Y)) => (X = Y))))).
