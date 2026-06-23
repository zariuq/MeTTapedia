; =============================================================================
; kernel_signature_lf_v0.metta
;
; A finite-admitted-signature lambda-Pi-modulo kernel seed.
;
; This merges the two previous good halves:
;   * lambda-Pi dependent checking from curriculum_lf_demo.metta
;   * finite prefix admission + axiom provenance from kernel_signature_v0.metta
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

!(import! &self kernel_binding_waist_v1)

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
; Public capture-avoiding `shift`/`subst` traversal comes from
; `kernel_binding_waist_v1`; this kernel is a client, not a second binding
; implementation.

(= (nf $sig (Var $k)) (Var $k))
(= (nf $sig (Srt $s)) (Srt $s))
(= (nf $sig (Con $x)) (Con $x))
(= (nf $sig (Def $x))
   (let $body (def-body-of $sig $x)
     (if (is-bad $body) (Bad unknown-definition) (nf $sig $body))))
(= (nf $sig (Pi  $A $B)) (Pi  (nf $sig $A) (nf $sig $B)))
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
(= (check-result $sig $ctx $t $ty) (check $sig $ctx $t $ty))

; ---------- signature admission ---------------------------------------------
(= (sort-ok $s)
   (unify $s (Srt type) True
     (unify $s (Srt kind) True False)))

(= (wf-decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT)
       (sort-ok $S))))
(= (wf-decl $prefix (DDef $n $T $body))
   (if (wf-decl $prefix (DConst $n $T))
       (check $prefix CtxNil $body $T)
       False))
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
   (SCons (DConst set (Srt type))
   (SCons (DConst In (Pi (Con set) (Pi (Con set) (Con o))))
   (SCons (DConst a (Con set))
   (SCons (DConst b (Con set))
   (SCons (DAxiom axMem (App (Con prf) (App (App (Con In) (Con a)) (Con b))))
   (SCons (DAxiom axSym
     (App (Con prf) (App (App (Con imp) (App (App (Con In) (Con a)) (Con b)))
                                        (App (App (Con In) (Con b)) (Con a)))))
          SNil))))))))))))))))))))

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

; Binding waist replay: the shared waist preserves this kernel's de Bruijn behavior.
(= (lf-v0-shadow-term) (Lam (Con nat) (Lam (Con nat) (Var 2))))
(= (lf-v0-shadow-replay) (subst 0 (Var 0) (lf-v0-shadow-term)))
!(assertEqual (subst 0 (Con z) (Var 1)) (Var 0))                         ; index decrement
!(assertEqual (subst 0 (Var 0) (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 1))) ; no capture
!(assertEqual (shift 1 0 (Lam (Con nat) (Var 0))) (Lam (Con nat) (Var 0))) ; bound var fixed under binder
!(assertEqual (shift 1 0 (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 2))) ; free var shifts under binder
!(assertEqual (lf-v0-shadow-replay) (lf-v0-shadow-term))                  ; nested shadowing

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
