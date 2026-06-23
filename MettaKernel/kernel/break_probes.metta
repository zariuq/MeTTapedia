; =============================================================================
;  break_probes.metta  --  breaking the lambda-Pi-modulo kernel on the axis that
;  matters for OUR work: the kernel checks proof TERMS but never checks the
;  DECLARATIONS (axioms + definitions) they are built over.  Distinct from
;  Codex's breaks (malformed-type sig / confluence / termination / type-wf-in-check).
;
;  Each !(assertEqual ... True) below documents a CURRENTLY-ACCEPTED unsoundness.
;  Run:  /home/aimama/aihub/hyperon/CeTTa/cetta break_probes.metta
; =============================================================================

; ----------------------------- kernel core (the proven safe one) -------------
(= (shift $d $c (Var $k)) (if (< $k $c) (Var $k) (Var (+ $k $d))))
(= (shift $d $c (Srt $s)) (Srt $s))
(= (shift $d $c (Con $x)) (Con $x))
(= (shift $d $c (Def $x)) (Def $x))
(= (shift $d $c (App $f $a)) (App (shift $d $c $f) (shift $d $c $a)))
(= (shift $d $c (Pi  $A $B)) (Pi  (shift $d $c $A) (shift $d (+ $c 1) $B)))
(= (shift $d $c (Lam $A $b)) (Lam (shift $d $c $A) (shift $d (+ $c 1) $b)))
(= (shift $d $c (Bad $e)) (Bad $e))
(= (subst $j $s (Var $k)) (if (== $k $j) $s (if (> $k $j) (Var (- $k 1)) (Var $k))))
(= (subst $j $s (Srt $x)) (Srt $x))
(= (subst $j $s (Con $x)) (Con $x))
(= (subst $j $s (Def $x)) (Def $x))
(= (subst $j $s (App $f $a)) (App (subst $j $s $f) (subst $j $s $a)))
(= (subst $j $s (Pi  $A $B)) (Pi  (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $B)))
(= (subst $j $s (Lam $A $b)) (Lam (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $b)))
(= (subst $j $s (Bad $e)) (Bad $e))
(= (nf (Var $k)) (Var $k))
(= (nf (Srt $s)) (Srt $s))
(= (nf (Con $x)) (Con $x))
(= (nf (Def $x)) (nf (defBody $x)))
(= (nf (Pi  $A $B)) (Pi  (nf $A) (nf $B)))
(= (nf (Lam $A $b)) (Lam (nf $A) (nf $b)))
(= (nf (Bad $e)) (Bad $e))
(= (nf (App $f $a)) (nf-app (nf $f) (nf $a)))
(= (nf-app $f $a) (unify $f (Lam $A $b) (nf (subst 0 $a $b)) (App $f $a)))
(= (is-bad $x) (unify $x (Bad $e) True False))
(= (conv $x $y) (if (is-bad (nf $x)) False (if (is-bad (nf $y)) False (== (nf $x) (nf $y)))))
(= (ctx-nth $i CtxNil) (Bad var-out-of-range))
(= (ctx-nth $i (CtxCons $h $t)) (if (== $i 0) $h (ctx-nth (- $i 1) $t)))
(= (ctx-type $i $ctx) (shift (+ $i 1) 0 (ctx-nth $i $ctx)))
(= (pts-rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi-bad-codomain)))
     (Bad pi-domain-not-type)))
(= (infer $ctx (Srt type)) (Srt kind))
(= (infer $ctx (Srt kind)) (Bad kind-is-topsort))
(= (infer $ctx (Var $i))  (ctx-type $i $ctx))
(= (infer $ctx (Con $c))  (sigT $c))
(= (infer $ctx (Def $c))  (sigT $c))
(= (infer $ctx (Pi $A $B))
   (let $sA (nf (infer $ctx $A))
     (let $sB (nf (infer (CtxCons $A $ctx) $B)) (pts-rule $sA $sB))))
(= (infer-lam $ctx $A $b)
   (let $sA (nf (infer $ctx $A))
     (unify $sA (Srt type)
        (let $tb (infer (CtxCons $A $ctx) $b)
          (if (is-bad (nf $tb)) (Bad lam-body-bad-type) (Pi $A $tb)))
        (Bad lam-domain-not-a-type))))
(= (infer $ctx (Lam $A $b)) (infer-lam $ctx $A $b))
(= (infer-app $ctx $f $a)
   (let $tf (nf (infer $ctx $f))
     (unify $tf (Pi $A $B)
        (if (conv (infer $ctx $a) $A) (subst 0 $a $B) (Bad arg-type-mismatch))
        (Bad applied-a-non-function))))
(= (infer $ctx (App $f $a)) (infer-app $ctx $f $a))
(= (check $ctx $t $ty) (conv (infer $ctx $t) $ty))

; -------------------------- a perfectly WELL-FORMED signature ----------------
; (no malformed types here -- every declared type below is legal LF; the
;  unsoundness is purely about declarations the kernel never validates)
(= (sigT o)      (Srt type))
(= (sigT prf)    (Pi (Con o) (Srt type)))
(= (sigT A)      (Con o))
(= (sigT B)      (Con o))
(= (sigT falseP) (Con o))
(= (sigT falseE)                                            ; ex falso : prf falseP -> Pc:o. prf c  (a LEGIT rule)
   (Pi (App (Con prf) (Con falseP)) (Pi (Con o) (App (Con prf) (Var 0)))))

; ============================================================================
;  BREAK A -- one inconsistent LEDGER entry explodes the whole logic, invisibly
;  (the kernel checks proofs RELATIVE to the signature; it gives ZERO guarantee
;   the signature's postulates are jointly consistent -- a model-theoretic
;   obligation no type-checker can discharge.  This is exactly HOTG's risk:
;   one mis-stated Megalodon axiom and everything is "provable".)
; ============================================================================
(= (sigT boom) (App (Con prf) (Con falseP)))   ; a postulate of  prf falseP  (a typo'd/contradictory axiom)
; ...and now ex falso proves an ARBITRARY proposition B:
!(assertEqual
   (check CtxNil (App (App (Con falseE) (Con boom)) (Con B)) (App (Con prf) (Con B)))
   True)                                        ; <-- a "proof" of any B, from one bad ledger entry

; ============================================================================
;  BREAK B -- DEFINITIONS are never checked against their declared types
;  (the kernel never verifies  defBody c : sigT c.  A "lemma" is accepted at
;   whatever type you declare, regardless of what its body actually proves.
;   Real developments are mostly definitions+lemmas -- this is load-bearing.)
; ============================================================================
; the SAME body  (Con A : o)  declared under two INCOMPATIBLE types:
(= (sigT def_as_o)   (Con o))                         ; declared :  o
(= (sigT def_as_prf) (App (Con prf) (Con falseP)))    ; declared :  prf falseP
(= (defBody def_as_o)   (Con A))
(= (defBody def_as_prf) (Con A))                      ; identical body A : o
; the body's REAL type is o:
!(assertEqual (infer CtxNil (Con A)) (Con o))
; yet the kernel accepts that one body at BOTH declared types -- so it never
; checked the body at all (A : o cannot also be a proof of falseP):
!(assertEqual (check CtxNil (Def def_as_o)   (Con o)) True)
!(assertEqual (check CtxNil (Def def_as_prf) (App (Con prf) (Con falseP))) True)   ; <-- unsound: A is no proof of falseP
