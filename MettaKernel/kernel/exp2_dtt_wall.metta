; =============================================================================
; exp2_dtt_wall.metta
;
; WebClaude Experiment 2: localize the DTT/conversion wall in the current
; admitted lambda-Pi seed, without faking recursors or induction.
;
; Result under test:
;   * beta works.
;   * delta through admitted definitions works.
;   * rfl/equality-introduction works for the opaque identity family.
;   * the first real DTT wall is recursor/iota computation and induction:
;       Nat recursors are not in the kernel/signature yet, so plus-zero and
;       plus_O_r cannot be obtained by computation or induction.
;
; Run:
;   /home/aimama/aihub/hyperon/CeTTa/cetta exp2_dtt_wall.metta
; =============================================================================

!(import! &self kernel_binding_waist_v1)

; ---------- admitted lambda-Pi kernel core -----------------------------------
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

; Public capture-avoiding `shift`/`subst` traversal comes from the shared binding
; waist.  This wall-localization probe is a checker client, not binding code.

(= (nf $sig (Var $k)) (Var $k))
(= (nf $sig (Srt $s)) (Srt $s))
(= (nf $sig (Con $x)) (Con $x))
(= (nf $sig (Def $x))
   (let $body (def-body-of $sig $x)
     (if (is-bad $body) (Bad unknown-definition) (nf $sig $body))))
(= (nf $sig (Pi $A $B)) (Pi (nf $sig $A) (nf $sig $B)))
(= (nf $sig (Lam $A $b)) (Lam (nf $sig $A) (nf $sig $b)))
(= (nf $sig (Bad $e)) (Bad $e))
(= (nf $sig (App $f $a)) (nf-app $sig (nf $sig $f) (nf $sig $a)))
(= (nf-app $sig $f $a) (unify $f (Lam $A $b) (nf $sig (subst 0 $a $b)) (App $f $a)))
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
(= (infer $sig $ctx (Var $i)) (ctx-type $i $ctx))
(= (infer $sig $ctx (Con $c)) (decl-type-of $sig $c))
(= (infer $sig $ctx (Def $c)) (decl-type-of $sig $c))
(= (infer $sig $ctx (Pi $A $B))
   (let $sA (nf $sig (infer $sig $ctx $A))
     (let $sB (nf $sig (infer $sig (CtxCons $A $ctx) $B)) (pts-rule $sA $sB))))
(= (infer-lam $sig $ctx $A $b)
   (let $sA (nf $sig (infer $sig $ctx $A))
     (unify $sA (Srt type)
        (let $tb (infer $sig (CtxCons $A $ctx) $b)
          (if (is-bad (nf $sig $tb)) (Bad lam-body-bad-type) (Pi $A $tb)))
        (Bad lam-domain-not-a-type))))
(= (infer $sig $ctx (Lam $A $b)) (infer-lam $sig $ctx $A $b))
(= (infer-app $sig $ctx $f $a)
   (let $tf (nf $sig (infer $sig $ctx $f))
     (unify $tf (Pi $A $B)
        (if (conv $sig (infer $sig $ctx $a) $A) (subst 0 $a $B) (Bad arg-type-mismatch))
        (Bad applied-a-non-function))))
(= (infer $sig $ctx (App $f $a)) (infer-app $sig $ctx $f $a))
(= (check $sig $ctx $t $ty) (conv $sig (infer $sig $ctx $t) $ty))

!(assertEqual (subst 0 (Con z) (Var 1)) (Var 0))
!(assertEqual (subst 0 (Var 0) (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 1)))
!(assertEqual (shift 1 0 (Lam (Con nat) (Var 0))) (Lam (Con nat) (Var 0)))
!(assertEqual (shift 1 0 (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 2)))

(= (sort-ok $s) (unify $s (Srt type) True (unify $s (Srt kind) True False)))
(= (wf-decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT) (sort-ok $S))))
(= (wf-decl $prefix (DDef $n $T $body))
   (if (wf-decl $prefix (DConst $n $T)) (check $prefix CtxNil $body $T) False))
(= (wf-decl $prefix (DAxiom $n $T)) (wf-decl $prefix (DConst $n $T)))
(= (wf-sig-prefix $prefix SNil) True)
(= (wf-sig-prefix $prefix (SCons $d $rest))
   (let $ok (wf-decl $prefix $d)
     (if $ok (wf-sig-prefix (SCons $d $prefix) $rest) False)))
(= (sig-admitted $sig)
   (let $u (unique-sig $sig)
     (if $u (wf-sig-prefix SNil $sig) False)))

; ---------- DTT probe signature ---------------------------------------------
(= (dtt-probe-sig)
   (SCons (DConst nat (Srt type))
   (SCons (DConst z (Con nat))
   (SCons (DConst s (Pi (Con nat) (Con nat)))
   (SCons (DConst eqn (Pi (Con nat) (Pi (Con nat) (Srt type))))
   (SCons (DConst rfl (Pi (Con nat) (App (App (Con eqn) (Var 0)) (Var 0))))
   (SCons (DDef idNat (Pi (Con nat) (Con nat)) (Lam (Con nat) (Var 0)))
   (SCons (DConst plus (Pi (Con nat) (Pi (Con nat) (Con nat))))
   (SCons (DConst natRec
     (Pi (Con nat)
       (Pi (Pi (Con nat) (Con nat))
         (Pi (Con nat) (Con nat)))))
          SNil)))))))))

; ---------- positives: what the current seed genuinely has ------------------
!(assertEqual (sig-admitted (dtt-probe-sig)) True)

; beta: ((fun x => x) z) : nat and normalizes to z
!(assertEqual (check (dtt-probe-sig) CtxNil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat)) True)
!(assertEqual (conv (dtt-probe-sig) (App (Lam (Con nat) (Var 0)) (Con z)) (Con z)) True)

; delta: admitted definition idNat unfolds, then beta reduces
!(assertEqual (check (dtt-probe-sig) CtxNil (App (Def idNat) (Con z)) (Con nat)) True)
!(assertEqual (conv (dtt-probe-sig) (App (Def idNat) (Con z)) (Con z)) True)

; rfl: opaque equality family can be introduced at reflexive endpoints
!(assertEqual
   (check (dtt-probe-sig) CtxNil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (Con z)))
   True)

; ---------- negatives: first real wall ---------------------------------------
; plus is only an opaque constant, so plus z z does NOT iota-reduce to z.
!(assertEqual
   (conv (dtt-probe-sig)
     (App (App (Con plus) (Con z)) (Con z))
     (Con z))
   False)

; natRec is only an opaque constant, so no recursor/iota computation exists.
!(assertEqual
   (conv (dtt-probe-sig)
     (App (App (App (Con natRec) (Con z)) (Lam (Con nat) (Con z))) (Con z))
     (Con z))
   False)

; Therefore a computational proof of plus z z = z by rfl is unavailable.
!(assertEqual
   (check (dtt-probe-sig) CtxNil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Con plus) (Con z)) (Con z))) (Con z)))
   False)

; Final classification for the report.
(= (dtt-wall) (Wall recursor-iota-and-induction-missing))

!(assertEqual
   (dtt-wall)
   (Wall recursor-iota-and-induction-missing))
