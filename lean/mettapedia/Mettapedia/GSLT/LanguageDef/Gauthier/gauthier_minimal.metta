; # Gauthier `minimal` languageDef — the MeTTa/MIK evaluator (R side)
;
; The MeTTa-kernel twin of `Minimal.lean`: same six-operator scalar-triple language, same operational
; semantics, run inside a MeTTa runtime instead of Lean.  Together they are the "a la metta and lean"
; GSLT languageDef of Gauthier's `minimal` OEIS signature.
;
; Grounded in `repos/oeis-synthesis/src/{kernel,exec}.sml`:
;   minimal_operl = [zero, x, y, suc(1), pred(1), loop(3)];  state = triple (x,y,z);
;   suc = (.+1), pred = (.-1);  loop f n x0 iterates n times x1:=f(x1,counter,x0), counter from 1,
;   input x0 held in the third register;  OEIS term a(n) = eval at seed (n,0,0).
;
; Term grammar T (QSynt `Ins (id,args)`), written as S-expressions:
;   zero | xreg | yreg | (suc P) | (pred P) | (loop Body N X0)
;
; (`eval` is a CeTTa builtin, so the interpreter is named `mev`.)  No fuel: a `minimal` program is a
; finite tree and every loop is bounded by its concrete count, so the rewrite terminates structurally;
; the Lean side carries `fuel` only to satisfy the totality checker.

; ---- mev PROG XV YV ZV : run PROG on register triple (XV,YV,ZV), returning a scalar ----
(= (mev zero      $x $y $z) 0)
(= (mev xreg      $x $y $z) $x)
(= (mev yreg      $x $y $z) $y)
(= (mev (suc  $p) $x $y $z) (+ (mev $p $x $y $z) 1))
(= (mev (pred $p) $x $y $z) (- (mev $p $x $y $z) 1))
(= (mev (loop $body $n $x0) $x $y $z)
   (mloop $body
          (mev $n  $x $y $z)                 ; iteration count
          (mev $x0 $x $y $z)                 ; x1 := accumulator (starts at x0)
          1                                  ; x2 := counter (starts at 1)
          (mev $x0 $x $y $z)))               ; x3 := input (held constant)

; ---- mloop Body K X1 X2 X3 : iterate K times, x1:=Body(x1,counter,input), counter+1 ----
(= (mloop $body $k $x1 $x2 $x3)
   (if (<= $k 0)
       $x1
       (mloop $body (- $k 1) (mev $body $x1 $x2 $x3) (+ $x2 1) $x3)))

; ---- mterm PROG K : the OEIS term a(K) = mev at seed (K,0,0) ----
(= (mterm $p $k) (mev $p $k 0 0))

; =====================================================================================
; Validation: the same programs as Minimal.lean must print the same sequences.
; =====================================================================================

; A001477 identity  `xreg`  -> 0 1 2 3 4 5 6 7
!(println! (mterm xreg 0)) !(println! (mterm xreg 1)) !(println! (mterm xreg 2)) !(println! (mterm xreg 3))
!(println! (mterm xreg 4)) !(println! (mterm xreg 5)) !(println! (mterm xreg 6)) !(println! (mterm xreg 7))

; successor  `(suc xreg)`  -> 1 4 8
!(println! (mterm (suc xreg) 0)) !(println! (mterm (suc xreg) 3)) !(println! (mterm (suc xreg) 7))

; predecessor  `(pred xreg)`  -> -1 2 6
!(println! (mterm (pred xreg) 0)) !(println! (mterm (pred xreg) 3)) !(println! (mterm (pred xreg) 7))

; A005843 doubling  `(loop (suc xreg) xreg xreg)` = 2n  -> 0 6 14
!(println! (mterm (loop (suc xreg) xreg xreg) 0))
!(println! (mterm (loop (suc xreg) xreg xreg) 3))
!(println! (mterm (loop (suc xreg) xreg xreg) 7))

; A008585 tripling  `(loop (suc (suc xreg)) xreg xreg)` = 3n  -> 0 9 21
!(println! (mterm (loop (suc (suc xreg)) xreg xreg) 0))
!(println! (mterm (loop (suc (suc xreg)) xreg xreg) 3))
!(println! (mterm (loop (suc (suc xreg)) xreg xreg) 7))

; Machine-checked assertions (must all succeed):
!(assertEqual (mterm xreg 5) 5)
!(assertEqual (mterm (suc xreg) 7) 8)
!(assertEqual (mterm (pred xreg) 0) -1)
!(assertEqual (mterm (loop (suc xreg) xreg xreg) 7) 14)
!(assertEqual (mterm (loop (suc (suc xreg)) xreg xreg) 7) 21)
