; =============================================================================
; kernel_signature_lf_eq_v0.metta
;
; Extends kernel_signature_lf_natrec_v0.metta with the next forced DTT feature:
; an EQUALITY ELIMINATOR (transport / Eq.subst), enough for real induction proofs.
;
;   * NatRec P z s n : P n, with iota at z and s n         (inherited)
;   * Transp P a b (p : eqn a b) (x : P a) : P b           (NEW: identity eliminator)
;       iota:  Transp P a a (rfl a) x  -->  x
;   * cong-s : Pi a b. eqn a b -> eqn (s a) (s b)          DERIVED from Transp (not ad hoc)
;   * forall n. plus n z = n                               proven by NatRec induction + cong-s
;
; (Full J -- proof-dependent motives -- is the generalization of Transp, not yet
;  forced by the curriculum.)  Same finite-admitted-signature + provenance discipline.
;
; The checker does NOT trust ambient sigT / defBody equations.  Constants,
; definitions, and axioms live in an explicit finite signature.  Definitions are
; admitted only when their body checks against their declared type.  Axioms are
; permitted only as explicit ledger entries, and proof terms are reported with
; the axioms they use.
;
; Run:
;   /home/aimama/aihub/hyperon/CeTTa/cetta kernel_signature_lf_v0.metta
; =============================================================================

; ---------- list helpers -----------------------------------------------------
(= (is-bad $x) (unify $x (Bad $e) True False))

(= (decl-name (DConst $n $T)) $n)
(= (decl-name (DDef $n $T $body)) $n)
(= (decl-name (DAxiom $n $T)) $n)

(= (sig-has-name $n SNil) False)
(= (sig-has-name $n (SCons $d $rest))
   (if (== $n (decl-name $d)) True (sig-has-name $n $rest)))

(= (unique-sig SNil) True)
(= (unique-sig (SCons $d $rest))
   (let $hit (sig-has-name (decl-name $d) $rest)
     (if $hit False (unique-sig $rest))))

(= (ax-union ANil $ys) $ys)
(= (ax-union (ACons $x $xs) $ys) (ACons $x (ax-union $xs $ys)))

; ---------- finite signature lookup -----------------------------------------
; Declarations:
;   DConst name type    -- checked constant/constructor
;   DDef   name type body -- checked definition, unfolds during normalization
;   DAxiom name type    -- unchecked postulate, visible in theorem provenance

(= (decl-type-of SNil $c) (Bad unknown-declaration))
(= (decl-type-of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DAxiom $c $T) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))

(= (def-body-of SNil $c) (Bad unknown-definition))
(= (def-body-of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $body (def-body-of $rest $x)))
(= (def-body-of (SCons (DConst $c $T) $rest) $x) (def-body-of $rest $x))
(= (def-body-of (SCons (DAxiom $c $T) $rest) $x) (def-body-of $rest $x))

(= (is-axiom-name SNil $x) False)
(= (is-axiom-name (SCons (DAxiom $a $T) $rest) $x)
   (if (== $x $a) True (is-axiom-name $rest $x)))
(= (is-axiom-name (SCons (DConst $c $T) $rest) $x) (is-axiom-name $rest $x))
(= (is-axiom-name (SCons (DDef $c $T $body) $rest) $x) (is-axiom-name $rest $x))

; ---------- lambda-Pi term machinery ----------------------------------------
(= (shift $d $c (Var $k)) (if (< $k $c) (Var $k) (Var (+ $k $d))))
(= (shift $d $c (Srt $s)) (Srt $s))
(= (shift $d $c (Con $x)) (Con $x))
(= (shift $d $c (Def $x)) (Def $x))
(= (shift $d $c (App $f $a)) (App (shift $d $c $f) (shift $d $c $a)))
(= (shift $d $c (Pi  $A $B)) (Pi  (shift $d $c $A) (shift $d (+ $c 1) $B)))
(= (shift $d $c (Lam $A $b)) (Lam (shift $d $c $A) (shift $d (+ $c 1) $b)))
(= (shift $d $c (NatRec $P $zcase $scase $n))
   (NatRec (shift $d $c $P) (shift $d $c $zcase) (shift $d $c $scase) (shift $d $c $n)))
(= (shift $d $c (GEq $A $a $b))
   (GEq (shift $d $c $A) (shift $d $c $a) (shift $d $c $b)))
(= (shift $d $c (GRfl $A $a))
   (GRfl (shift $d $c $A) (shift $d $c $a)))
(= (shift $d $c (Transp $P $a $b $p $x))
   (Transp (shift $d $c $P) (shift $d $c $a) (shift $d $c $b) (shift $d $c $p) (shift $d $c $x)))
(= (shift $d $c (GTransp $A $P $a $b $p $x))
   (GTransp (shift $d $c $A) (shift $d $c $P) (shift $d $c $a) (shift $d $c $b) (shift $d $c $p) (shift $d $c $x)))
(= (shift $d $c (Bad $e)) (Bad $e))

(= (subst $j $s (Var $k)) (if (== $k $j) $s (if (> $k $j) (Var (- $k 1)) (Var $k))))
(= (subst $j $s (Srt $x)) (Srt $x))
(= (subst $j $s (Con $x)) (Con $x))
(= (subst $j $s (Def $x)) (Def $x))
(= (subst $j $s (App $f $a)) (App (subst $j $s $f) (subst $j $s $a)))
(= (subst $j $s (Pi  $A $B)) (Pi  (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $B)))
(= (subst $j $s (Lam $A $b)) (Lam (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $b)))
(= (subst $j $s (NatRec $P $zcase $scase $n))
   (NatRec (subst $j $s $P) (subst $j $s $zcase) (subst $j $s $scase) (subst $j $s $n)))
(= (subst $j $s (GEq $A $a $b))
   (GEq (subst $j $s $A) (subst $j $s $a) (subst $j $s $b)))
(= (subst $j $s (GRfl $A $a))
   (GRfl (subst $j $s $A) (subst $j $s $a)))
(= (subst $j $s (Transp $P $a $b $p $x))
   (Transp (subst $j $s $P) (subst $j $s $a) (subst $j $s $b) (subst $j $s $p) (subst $j $s $x)))
(= (subst $j $s (GTransp $A $P $a $b $p $x))
   (GTransp (subst $j $s $A) (subst $j $s $P) (subst $j $s $a) (subst $j $s $b) (subst $j $s $p) (subst $j $s $x)))
(= (subst $j $s (Bad $e)) (Bad $e))

(= (nf $sig (Var $k)) (Var $k))
(= (nf $sig (Srt $s)) (Srt $s))
(= (nf $sig (Con $x)) (Con $x))
(= (nf $sig (Def $x))
   (let $body (def-body-of $sig $x)
     (if (is-bad $body) (Bad unknown-definition) (nf $sig $body))))
(= (nf $sig (Pi  $A $B)) (Pi  (nf $sig $A) (nf $sig $B)))
(= (nf $sig (Lam $A $b)) (Lam (nf $sig $A) (nf $sig $b)))
(= (nf $sig (NatRec $P $zcase $scase $n))
   (nf-natrec $sig (nf $sig $P) (nf $sig $zcase) (nf $sig $scase) (nf $sig $n)))
(= (nf $sig (GEq $A $a $b))
   (GEq (nf $sig $A) (nf $sig $a) (nf $sig $b)))
(= (nf $sig (GRfl $A $a))
   (GRfl (nf $sig $A) (nf $sig $a)))
(= (nf $sig (Transp $P $a $b $p $x))
   (nf-transp $sig (nf $sig $P) (nf $sig $a) (nf $sig $b) (nf $sig $p) (nf $sig $x)))
(= (nf $sig (GTransp $A $P $a $b $p $x))
   (nf-gtransp $sig (nf $sig $A) (nf $sig $P) (nf $sig $a) (nf $sig $b) (nf $sig $p) (nf $sig $x)))
(= (nf $sig (Bad $e)) (Bad $e))
(= (nf $sig (App $f $a)) (nf-app $sig (nf $sig $f) (nf $sig $a)))
(= (nf-app $sig $f $a) (unify $f (Lam $A $b) (nf $sig (subst 0 $a $b)) (App $f $a)))
(= (nf-natrec $sig $P $zcase $scase $n)
   (unify $n (Con z)
     $zcase
     (unify $n (App (Con s) $k)
       (nf $sig (App (App $scase $k) (NatRec $P $zcase $scase $k)))
       (NatRec $P $zcase $scase $n))))
(= (nf-transp $sig $P $a $b $p $x)
   (unify $p (App (Con rfl) $k)
     (if (== $a $k)
       (if (== $b $k) $x (Transp $P $a $b $p $x))
       (Transp $P $a $b $p $x))
     (Transp $P $a $b $p $x)))
(= (nf-gtransp $sig $A $P $a $b $p $x)
   (unify $p (GRfl $A0 $k)
     (if (== $A $A0)
       (if (== $a $k)
         (if (== $b $k) $x (GTransp $A $P $a $b $p $x))
         (GTransp $A $P $a $b $p $x))
       (GTransp $A $P $a $b $p $x))
     (GTransp $A $P $a $b $p $x)))

(= (conv $sig $x $y)
   (if (is-bad (nf $sig $x)) False
     (if (is-bad (nf $sig $y)) False
       (== (nf $sig $x) (nf $sig $y)))))

(= (ctx-nth $i CtxNil) (Bad var-out-of-range))
(= (ctx-nth $i (CtxCons $h $t)) (if (== $i 0) $h (ctx-nth (- $i 1) $t)))
(= (ctx-type $i $ctx) (shift (+ $i 1) 0 (ctx-nth $i $ctx)))

(= (pts-rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi-bad-codomain)))
     (Bad pi-domain-not-type)))

(= (infer $sig $ctx (Srt type)) (Srt kind))
(= (infer $sig $ctx (Srt kind)) (Bad kind-is-topsort))
(= (infer $sig $ctx (Bad $e)) (Bad $e))
(= (infer $sig $ctx (Var $i))  (ctx-type $i $ctx))
(= (infer $sig $ctx (Con $c))  (decl-type-of $sig $c))
(= (infer $sig $ctx (Def $c))  (decl-type-of $sig $c))
(= (infer $sig $ctx (Pi $A $B))
   (let $sA (nf $sig (infer $sig $ctx $A))
     (let $sB (nf $sig (infer $sig (CtxCons $A $ctx) $B)) (pts-rule $sA $sB))))
(= (infer-lam $sig $ctx $A $b)
   (let $sA (nf $sig (infer $sig $ctx $A))
     (unify $sA (Srt type)
        (let $tb (infer $sig (CtxCons $A $ctx) $b)
          (let $ntb (nf $sig $tb)
            (let $bad (is-bad $ntb)
              (if $bad (Bad lam-body-bad-type) (Pi $A $tb)))))
        (Bad lam-domain-not-a-type))))
(= (infer $sig $ctx (Lam $A $b)) (infer-lam $sig $ctx $A $b))
(= (infer-app $sig $ctx $f $a)
   (let $tf (nf $sig (infer $sig $ctx $f))
     (unify $tf (Pi $A $B)
        (if (conv $sig (infer $sig $ctx $a) $A) (subst 0 $a $B) (Bad arg-type-mismatch))
        (Bad applied-a-non-function))))
(= (infer $sig $ctx (App $f $a)) (infer-app $sig $ctx $f $a))
(= (natrec-step-type $P)
   (Pi (Con nat)
     (Pi (App (shift 1 0 $P) (Var 0))
       (App (shift 2 0 $P) (App (Con s) (Var 1))))))
(= (infer-natrec $sig $ctx $P $zcase $scase $n)
   (if (check-conv $sig $ctx $P (Pi (Con nat) (Srt type)))
     (if (check-conv $sig $ctx $zcase (App $P (Con z)))
       (if (check-conv $sig $ctx $scase (natrec-step-type $P))
         (if (check-conv $sig $ctx $n (Con nat))
           (App $P $n)
           (Bad natrec-scrutinee-not-nat))
         (Bad natrec-bad-step))
       (Bad natrec-bad-zero))
     (Bad natrec-bad-motive)))
(= (infer $sig $ctx (NatRec $P $zcase $scase $n)) (infer-natrec $sig $ctx $P $zcase $scase $n))
(= (infer-geq $sig $ctx $A $a $b)
   (if (check-conv $sig $ctx $A (Srt type))
     (if (check-conv $sig $ctx $a $A)
       (if (check-conv $sig $ctx $b $A)
         (Srt type)
         (Bad geq-bad-right))
       (Bad geq-bad-left))
     (Bad geq-bad-carrier)))
(= (infer $sig $ctx (GEq $A $a $b)) (infer-geq $sig $ctx $A $a $b))
(= (infer-grfl $sig $ctx $A $a)
   (if (check-conv $sig $ctx $A (Srt type))
     (if (check-conv $sig $ctx $a $A)
       (GEq $A $a $a)
       (Bad grfl-bad-term))
     (Bad grfl-bad-carrier)))
(= (infer $sig $ctx (GRfl $A $a)) (infer-grfl $sig $ctx $A $a))
(= (infer-transp $sig $ctx $P $a $b $p $x)
   (if (check-conv $sig $ctx $P (Pi (Con nat) (Srt type)))
     (if (check-conv $sig $ctx $a (Con nat))
       (if (check-conv $sig $ctx $b (Con nat))
         (if (check-conv $sig $ctx $p (App (App (Con eqn) $a) $b))
           (if (check-conv $sig $ctx $x (App $P $a))
             (App $P $b)
             (Bad transp-bad-elem))
           (Bad transp-bad-proof))
         (Bad transp-bad-b))
       (Bad transp-bad-a))
     (Bad transp-bad-motive)))
(= (infer $sig $ctx (Transp $P $a $b $p $x)) (infer-transp $sig $ctx $P $a $b $p $x))
(= (infer-gtransp $sig $ctx $A $P $a $b $p $x)
   (if (check-conv $sig $ctx $A (Srt type))
     (if (check-conv $sig $ctx $P (Pi $A (Srt type)))
       (if (check-conv $sig $ctx $a $A)
         (if (check-conv $sig $ctx $b $A)
           (if (check-conv $sig $ctx $p (GEq $A $a $b))
             (if (check-conv $sig $ctx $x (App $P $a))
               (App $P $b)
               (Bad gtransp-bad-elem))
             (Bad gtransp-bad-proof))
           (Bad gtransp-bad-b))
         (Bad gtransp-bad-a))
       (Bad gtransp-bad-motive))
     (Bad gtransp-bad-carrier)))
(= (infer $sig $ctx (GTransp $A $P $a $b $p $x)) (infer-gtransp $sig $ctx $A $P $a $b $p $x))
(= (sort-ok $s)
   (unify $s (Srt type) True
     (unify $s (Srt kind) True False)))
(= (type-ok $sig $ctx $ty)
   (let $ITY (infer $sig $ctx $ty)
     (let $S (nf $sig $ITY) (sort-ok $S))))
(= (check-conv $sig $ctx $t $ty) (conv $sig (infer $sig $ctx $t) $ty))
(= (check $sig $ctx $t $ty)
   (let $okTy (type-ok $sig $ctx $ty)
     (if $okTy (check-conv $sig $ctx $t $ty) False)))
(= (check-result $sig $ctx $t $ty) (check $sig $ctx $t $ty))

; ---------- signature admission ---------------------------------------------
(= (wf-decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT)
       (sort-ok $S))))
(= (wf-decl $prefix (DDef $n $T $body))
   (let $okT (wf-decl $prefix (DConst $n $T))
     (if $okT (check-conv $prefix CtxNil $body $T) False)))
(= (wf-decl $prefix (DAxiom $n $T)) (wf-decl $prefix (DConst $n $T)))

(= (wf-sig-prefix $prefix SNil) True)
(= (wf-sig-prefix $prefix (SCons $d $rest))
   (let $ok (wf-decl $prefix $d)
     (if $ok
       (wf-sig-prefix (SCons $d $prefix) $rest)
       False)))

(= (sig-admitted $sig)
   (let $u (unique-sig $sig)
     (if $u (wf-sig-prefix SNil $sig) False)))

; ---------- theorem provenance over checked proof terms ----------------------
(= (term-axioms $sig (Var $k)) ANil)
(= (term-axioms $sig (Srt $s)) ANil)
(= (term-axioms $sig (Con $c))
   (if (is-axiom-name $sig $c) (ACons $c ANil) ANil))
(= (term-axioms $sig (Def $c)) ANil)
(= (term-axioms $sig (Pi $A $B)) (ax-union (term-axioms $sig $A) (term-axioms $sig $B)))
(= (term-axioms $sig (Lam $A $b)) (ax-union (term-axioms $sig $A) (term-axioms $sig $b)))
(= (term-axioms $sig (App $f $a)) (ax-union (term-axioms $sig $f) (term-axioms $sig $a)))
(= (term-axioms $sig (NatRec $P $zcase $scase $n))
   (ax-union (term-axioms $sig $P)
     (ax-union (term-axioms $sig $zcase)
       (ax-union (term-axioms $sig $scase) (term-axioms $sig $n)))))
(= (term-axioms $sig (GEq $A $a $b))
   (ax-union (term-axioms $sig $A)
     (ax-union (term-axioms $sig $a) (term-axioms $sig $b))))
(= (term-axioms $sig (GRfl $A $a))
   (ax-union (term-axioms $sig $A) (term-axioms $sig $a)))
(= (term-axioms $sig (Transp $P $a $b $p $x))
   (ax-union (term-axioms $sig $P)
     (ax-union (term-axioms $sig $a)
       (ax-union (term-axioms $sig $b)
         (ax-union (term-axioms $sig $p) (term-axioms $sig $x))))))
(= (term-axioms $sig (GTransp $A $P $a $b $p $x))
   (ax-union (term-axioms $sig $A)
     (ax-union (term-axioms $sig $P)
       (ax-union (term-axioms $sig $a)
         (ax-union (term-axioms $sig $b)
           (ax-union (term-axioms $sig $p) (term-axioms $sig $x)))))))
(= (term-axioms $sig (Bad $e)) ANil)

(= (kernel-check-checked $sig $term $type True)
   (let $uses (term-axioms $sig $term)
     (Ok (CheckedPrf $uses $term $type))))
(= (kernel-check-checked $sig $term $type False) (Err check-failed))
(= (kernel-check-admitted $sig $term $type True)
   (kernel-check-checked $sig $term $type (check-result $sig CtxNil $term $type)))
(= (kernel-check-admitted $sig $term $type False) (Err signature-not-admitted))
(= (kernel-check $sig $term $type)
   (case (sig-admitted $sig)
     ((True (kernel-check-checked $sig $term $type (check-result $sig CtxNil $term $type)))
      (False (Err signature-not-admitted)))))

; ---------- finite curriculum signature --------------------------------------
(= (good-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DConst imp (Pi (Con o) (Pi (Con o) (Con o))))
   (SCons (DConst impI
     (Pi (Con o) (Pi (Con o)
       (Pi (Pi (App (Con prf) (Var 1)) (App (Con prf) (Var 1)))
           (App (Con prf) (App (App (Con imp) (Var 2)) (Var 1)))))))
   (SCons (DConst impE
     (Pi (Con o) (Pi (Con o)
       (Pi (App (Con prf) (App (App (Con imp) (Var 1)) (Var 0)))
         (Pi (App (Con prf) (Var 2)) (App (Con prf) (Var 2)))))))
   (SCons (DConst A (Con o))
   (SCons (DConst B (Con o))
   (SCons (DDef holds (Pi (Con o) (Srt type)) (Lam (Con o) (App (Con prf) (Var 0))))
   (SCons (DConst nat (Srt type))
   (SCons (DConst z (Con nat))
   (SCons (DConst s (Pi (Con nat) (Con nat)))
   (SCons (DConst eqn (Pi (Con nat) (Pi (Con nat) (Srt type))))
   (SCons (DConst rfl (Pi (Con nat) (App (App (Con eqn) (Var 0)) (Var 0))))
   (SCons (DDef plus
     (Pi (Con nat) (Pi (Con nat) (Con nat)))
     (Lam (Con nat)
       (Lam (Con nat)
         (NatRec
           (Lam (Con nat) (Con nat))
           (Var 0)
           (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
           (Var 1)))))
   (SCons (DConst set (Srt type))
   (SCons (DConst In (Pi (Con set) (Pi (Con set) (Con o))))
   (SCons (DConst a (Con set))
   (SCons (DConst b (Con set))
   (SCons (DAxiom axMem (App (Con prf) (App (App (Con In) (Con a)) (Con b))))
   (SCons (DAxiom axSym
     (App (Con prf) (App (App (Con imp) (App (App (Con In) (Con a)) (Con b)))
                                        (App (App (Con In) (Con b)) (Con a)))))
          SNil)))))))))))))))))))))

(= (bad-def-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst A (Con o))
   (SCons (DConst falseP (Con o))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DDef defAsPrf (App (Con prf) (Con falseP)) (Con A))
          SNil))))))

(= (dup-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst o (Srt type))
          SNil)))

(= (forward-ref-sig)
   (SCons (DDef useLater (Con later) (Con later))
   (SCons (DConst later (Srt type))
          SNil)))

(= (inconsistent-ledger-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DConst falseP (Con o))
   (SCons (DConst B (Con o))
   (SCons (DConst falseE
     (Pi (App (Con prf) (Con falseP)) (Pi (Con o) (App (Con prf) (Var 0)))))
   (SCons (DAxiom boom (App (Con prf) (Con falseP)))
          SNil)))))))

; ---------- admission regressions -------------------------------------------
!(assertEqual (sig-admitted (good-sig)) True)
!(assertEqual (sig-admitted (bad-def-sig)) False)
!(assertEqual (sig-admitted (dup-sig)) False)
!(assertEqual (sig-admitted (forward-ref-sig)) False)
!(assertEqual (sig-admitted (inconsistent-ledger-sig)) True)

; Bad is not a type.
!(assertEqual (infer (good-sig) CtxNil (Lam (Srt type) (Var 0))) (Bad lam-domain-not-a-type))
!(assertEqual (check (good-sig) CtxNil (Lam (Con o) (Srt kind)) (Pi (Con o) (Bad kind-is-topsort))) False)

; Delta conversion through an admitted definition.
!(assertEqual (conv (good-sig) (App (Def holds) (Con A)) (App (Con prf) (Con A))) True)

; Entry examples: DTT rfl, HOL implication proofs, beta, HOTG axiom composition.
!(assertEqual
   (kernel-check (good-sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (Con z)))
   (Ok (CheckedPrf ANil (App (Con rfl) (Con z)) (App (App (Con eqn) (Con z)) (Con z)))))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))
   (Ok (CheckedPrf ANil
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (Con impI) (Con A)) (App (App (Con imp) (Con B)) (Con A)))
          (Lam (App (Con prf) (Con A))
               (App (App (App (Con impI) (Con B)) (Con A))
                    (Lam (App (Con prf) (Con B)) (Var 1)))))
     (App (Con prf) (App (App (Con imp) (Con A)) (App (App (Con imp) (Con B)) (Con A)))))
   (Ok (CheckedPrf ANil
     (App (App (App (Con impI) (Con A)) (App (App (Con imp) (Con B)) (Con A)))
          (Lam (App (Con prf) (Con A))
               (App (App (App (Con impI) (Con B)) (Con A))
                    (Lam (App (Con prf) (Con B)) (Var 1)))))
     (App (Con prf) (App (App (Con imp) (Con A)) (App (App (Con imp) (Con B)) (Con A)))))))

!(assertEqual
   (kernel-check (good-sig)
     (App (Lam (Con nat) (Var 0)) (Con z))
     (Con nat))
   (Ok (CheckedPrf ANil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))))

; NatRec is a real dependent eliminator, not an opaque constant.
!(assertEqual
   (infer (good-sig) CtxNil
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z)))
   (App (Lam (Con nat) (Con nat)) (Con z)))

; Iota at zero: NatRec P z s z reduces to the zero case.
!(assertEqual
   (conv (good-sig)
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z))
     (Con z))
   True)

; Iota at successor: NatRec P z s (s z) reduces by one successor step.
!(assertEqual
   (conv (good-sig)
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

; plus is admitted only because its body checks against nat -> nat -> nat.
!(assertEqual
   (conv (good-sig)
     (App (App (Def plus) (Con z)) (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

!(assertEqual
   (conv (good-sig)
     (App (App (Def plus) (App (Con s) (Con z))) (Con z))
     (App (Con s) (Con z)))
   True)

; The old Exp2 wall is closed for concrete plus-zero by computation: rfl now checks.
!(assertEqual
   (kernel-check (good-sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Def plus) (Con z)) (Con z))) (Con z)))
   (Ok (CheckedPrf ANil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Def plus) (Con z)) (Con z))) (Con z)))))

; Negative: the motive must be nat -> Type.
!(assertEqual
   (infer (good-sig) CtxNil
     (NatRec
       (Con nat)
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z)))
   (Bad natrec-bad-motive))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (App (Con impE) (App (App (Con In) (Con a)) (Con b)))
                                    (App (App (Con In) (Con b)) (Con a)))
               (Con axSym)) (Con axMem))
     (App (Con prf) (App (App (Con In) (Con b)) (Con a))))
   (Ok (CheckedPrf (ACons axSym (ACons axMem ANil))
     (App (App (App (App (Con impE) (App (App (Con In) (Con a)) (Con b)))
                                    (App (App (Con In) (Con b)) (Con a)))
               (Con axSym)) (Con axMem))
     (App (Con prf) (App (App (Con In) (Con b)) (Con a))))))

; Old break probes no longer break admitted signatures.
!(assertEqual
   (kernel-check (bad-def-sig) (Def defAsPrf) (App (Con prf) (Con falseP)))
   (Err signature-not-admitted))

!(assertEqual
   (kernel-check (inconsistent-ledger-sig)
     (App (App (Con falseE) (Con boom)) (Con B))
     (App (Con prf) (Con B)))
   (Ok (CheckedPrf (ACons boom ANil)
     (App (App (Con falseE) (Con boom)) (Con B))
     (App (Con prf) (Con B)))))

; Wrong proof targets still reject.
!(assertEqual
   (kernel-check (good-sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (App (Con s) (Con z))))
   (Err check-failed))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con B))))
   (Err check-failed))

; ==================== EQUALITY ELIMINATION (transport) ======================
; transport iota:  Transp P z z (rfl z) z  reduces to  z
!(assertEqual
   (conv (good-sig)
     (Transp (Lam (Con nat) (Con nat)) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z))
     (Con z))
   True)
; transport infers its result type  (App P b)
!(assertEqual
   (infer (good-sig) CtxNil
     (Transp (Lam (Con nat) (Con nat)) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z)))
   (App (Lam (Con nat) (Con nat)) (Con z)))
; cong-s : Pi a b. eqn a b -> eqn (s a) (s b)  -- DERIVED from transport (not ad hoc),
; checks at its declared type:
!(assertEqual
   (check (good-sig) CtxNil
     (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
       (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
               (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
     (Pi (Con nat) (Pi (Con nat) (Pi (App (App (Con eqn) (Var 1)) (Var 0))
       (App (App (Con eqn) (App (Con s) (Var 2))) (App (Con s) (Var 1)))))))
   True)
; negative: a WRONG congruence target is rejected (eqn (s a)(s b) is NOT eqn a b)
!(assertEqual
   (check (good-sig) CtxNil
     (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
       (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
               (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
     (Pi (Con nat) (Pi (Con nat) (Pi (App (App (Con eqn) (Var 1)) (Var 0))
       (App (App (Con eqn) (Var 2)) (Var 1))))))
   False)
; negative: malformed transport motive (P := nat, not nat -> Type) is rejected
!(assertEqual
   (infer (good-sig) CtxNil
     (Transp (Con nat) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z)))
   (Bad transp-bad-motive))

; negative: Transp iota fires only at matching rfl endpoints.
!(assertEqual
   (conv (good-sig)
     (Transp (Lam (Con nat) (Srt type))
             (Con z)
             (App (Con s) (Con z))
             (App (Con rfl) (Con z))
             (Con nat))
     (Con nat))
   False)

; negative: kernel-check refuses ill-formed expected types instead of normalizing
; them away.  This is the permanent regression probe for the old exploit.
!(assertEqual
   (kernel-check (good-sig)
     (Con z)
     (Transp (Lam (Con nat) (Srt type))
             (Con z)
             (App (Con s) (Con z))
             (App (Con rfl) (Con z))
             (Con nat)))
   (Err check-failed))

; ==================== GENERAL TRANSPORT (type-indexed identity) ==============
; GTransp generalizes transport from nat equality to any carrier A : Type.
!(assertEqual
   (kernel-check (good-sig)
     (GTransp (Con nat)
       (Lam (Con nat) (Con nat))
       (Con z) (Con z)
       (GRfl (Con nat) (Con z))
       (Con z))
     (Con nat))
   (Ok (CheckedPrf ANil
     (GTransp (Con nat)
       (Lam (Con nat) (Con nat))
       (Con z) (Con z)
       (GRfl (Con nat) (Con z))
       (Con z))
     (Con nat))))

; Same primitive over propositions: transporting an axiom proof along reflexive
; proposition equality keeps the axiom provenance visible.
!(assertEqual
   (kernel-check (good-sig)
     (GTransp (Con o)
       (Lam (Con o) (App (Con prf) (Var 0)))
       (App (App (Con In) (Con a)) (Con b))
       (App (App (Con In) (Con a)) (Con b))
       (GRfl (Con o) (App (App (Con In) (Con a)) (Con b)))
       (Con axMem))
     (App (Con prf) (App (App (Con In) (Con a)) (Con b))))
   (Ok (CheckedPrf (ACons axMem ANil)
     (GTransp (Con o)
       (Lam (Con o) (App (Con prf) (Var 0)))
       (App (App (Con In) (Con a)) (Con b))
       (App (App (Con In) (Con a)) (Con b))
       (GRfl (Con o) (App (App (Con In) (Con a)) (Con b)))
       (Con axMem))
     (App (Con prf) (App (App (Con In) (Con a)) (Con b))))))

; negative: general transport does not accept a reflexivity proof at mismatched
; endpoints.
!(assertEqual
   (kernel-check (good-sig)
     (GTransp (Con nat)
       (Lam (Con nat) (Con nat))
       (Con z) (App (Con s) (Con z))
       (GRfl (Con nat) (Con z))
       (Con z))
     (Con nat))
   (Err check-failed))

; ===== INDUCTION:  forall n. plus n z = n  (the curriculum plus_O_r shape) =====
; `plus` recurses on its FIRST arg, so `plus n z` is STUCK for variable n -- this
; genuinely needs induction, not computation.  Proof term:
;   \n. NatRec (\m. eqn (plus m z) m)  (rfl z)  (\k \ih. cong-s (plus k z) k ih)  n
; with cong-s inlined (its standalone form is the checked derivation above).
!(assertEqual
   (kernel-check (good-sig)
     (Lam (Con nat)
       (NatRec
         (Lam (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0)))
         (App (Con rfl) (Con z))
         (Lam (Con nat)
           (Lam (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))
             (App (App (App
                 (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
                   (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
                           (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
                 (App (App (Def plus) (Var 1)) (Con z))) (Var 1)) (Var 0))))
         (Var 0)))
     (Pi (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))))
   (Ok (CheckedPrf ANil
     (Lam (Con nat)
       (NatRec
         (Lam (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0)))
         (App (Con rfl) (Con z))
         (Lam (Con nat)
           (Lam (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))
             (App (App (App
                 (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
                   (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
                           (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
                 (App (App (Def plus) (Var 1)) (Con z))) (Var 1)) (Var 0))))
         (Var 0)))
     (Pi (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))))))
; negative: the FALSE statement  forall n. plus n z = s n  does NOT check (base fails)
!(assertEqual
   (check (good-sig) CtxNil
     (Lam (Con nat)
       (NatRec
         (Lam (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0))))
         (App (Con rfl) (Con z))
         (Lam (Con nat) (Lam (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0)))
           (Var 0)))
         (Var 0)))
     (Pi (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0)))))
   False)
