; =============================================================================
;  curriculum_lf_demo.metta
;  ONE lambda-Pi-modulo kernel  x  THREE paradigm signatures  x  easy curriculum
;  theorems from each -- the unified-waist thesis, made runnable.
;
;  Kernel core = Claude Web's mettakernel + Codex's CeTTa-safe repair
;  (Bad-propagation; infer-app/infer-lam helper factoring; lambda-domain must be a
;   proper type).  Object logics are SIGNATURES over this one checker, never
;   changes to it -- HOL/STT, DTT (inductive data + identity), HOTG (sets + axioms).
;
;  Each paradigm shows POSITIVES (a real typed/sealed proof term checks) and a
;  NEGATIVE (a wrong proof is rejected).  Run:
;    /home/aimama/aihub/hyperon/CeTTa/cetta curriculum_lf_demo.metta
; =============================================================================

!(import! &self kernel_binding_waist_v1)

; ============================ THE TRUSTED KERNEL ============================
; Public capture-avoiding `shift`/`subst` traversal comes from the shared binding
; waist.  This curriculum demo is a checker client, not a binding implementation.

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

; ============================================================================
;  THE SIGNATURE  (all three object logics live over the ONE kernel above)
; ============================================================================
; ---- HOL / simple type theory (ICL10-12, HOL06) ----
(= (sigT o)    (Srt type))
(= (sigT prf)  (Pi (Con o) (Srt type)))
(= (sigT imp)  (Pi (Con o) (Pi (Con o) (Con o))))
(= (sigT impI)
   (Pi (Con o) (Pi (Con o)
     (Pi (Pi (App (Con prf) (Var 1)) (App (Con prf) (Var 1)))
         (App (Con prf) (App (App (Con imp) (Var 2)) (Var 1)))))))
(= (sigT impE)
   (Pi (Con o) (Pi (Con o)
     (Pi (App (Con prf) (App (App (Con imp) (Var 1)) (Var 0)))
       (Pi (App (Con prf) (Var 2)) (App (Con prf) (Var 2)))))))
(= (sigT A) (Con o))
(= (sigT B) (Con o))
(= (sigT holds) (Pi (Con o) (Srt type)))
(= (defBody holds) (Lam (Con o) (App (Con prf) (Var 0))))

; ---- DTT : inductive data + the identity type (Coq ICL01-03, Lean 01-04) ----
(= (sigT nat) (Srt type))
(= (sigT z)   (Con nat))
(= (sigT s)   (Pi (Con nat) (Con nat)))
(= (sigT eqn) (Pi (Con nat) (Pi (Con nat) (Srt type))))          ; eqn : nat -> nat -> Type
(= (sigT rfl) (Pi (Con nat) (App (App (Con eqn) (Var 0)) (Var 0)))) ; rfl : Px:nat. eqn x x

; ---- HOTG : sets + membership + LEDGERED AXIOMS over HOL (Megalodon H1-H5) ----
(= (sigT set) (Srt type))
(= (sigT In)  (Pi (Con set) (Pi (Con set) (Con o))))            ; In : set -> set -> o
(= (sigT a)   (Con set))
(= (sigT b)   (Con set))
(= (sigT axMem) (App (Con prf) (App (App (Con In) (Con a)) (Con b))))   ; AXIOM: prf (In a b)
(= (sigT axSym)                                                        ; AXIOM: prf (In a b => In b a)
   (App (Con prf) (App (App (Con imp) (App (App (Con In) (Con a)) (Con b)))
                                      (App (App (Con In) (Con b)) (Con a)))))

; ================================= TESTS ====================================
; ---- waist sanity ----
!(assertEqual (subst 0 (Con z) (Var 1)) (Var 0))
!(assertEqual (subst 0 (Var 0) (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 1)))
!(assertEqual (shift 1 0 (Lam (Con nat) (Var 0))) (Lam (Con nat) (Var 0)))
!(assertEqual (shift 1 0 (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 2)))
!(assertEqual (infer CtxNil (Srt type)) (Srt kind))
!(assertEqual (infer CtxNil (App (Con prf) (Con A))) (Srt type))
; Bad is not a type: the safe checker rejects failed inference results instead
; of letting them masquerade as ordinary terms/types.
!(assertEqual (infer CtxNil (Lam (Srt type) (Var 0))) (Bad lam-domain-not-a-type))
!(assertEqual (check CtxNil (Lam (Con o) (Srt kind)) (Pi (Con o) (Bad kind-is-topsort))) False)

; ============================ DTT paradigm =================================
; numeral  s (s z) : nat
!(assertEqual (check CtxNil (App (Con s) (App (Con s) (Con z))) (Con nat)) True)
; identity intro:  rfl z : eqn z z
!(assertEqual (check CtxNil (App (Con rfl) (Con z)) (App (App (Con eqn) (Con z)) (Con z))) True)
; self-implication identity (Curry-Howard image of NIK's propositional ph->ph; cross-profile anchor):
;   lambda x:o. x : o -> o  -- the lambda-Pi profile inhabits A->A, agreeing with the Metamath profile
!(assertEqual (check CtxNil (Lam (Con o) (Var 0)) (Pi (Con o) (Con o))) True)
; NEGATIVE: rfl z does not prove  eqn z (s z)
!(assertEqual (check CtxNil (App (Con rfl) (Con z)) (App (App (Con eqn) (Con z)) (App (Con s) (Con z)))) False)

; =========================== HOTG paradigm =================================
; the ledgered axiom inhabits its stated proposition:  axMem : prf (In a b)
!(assertEqual (check CtxNil (Con axMem) (App (Con prf) (App (App (Con In) (Con a)) (Con b)))) True)
; axioms compose through the HOL rule impE:  In b a  from  (In a b => In b a) and (In a b)
!(assertEqual
   (check CtxNil
     (App (App (App (App (Con impE) (App (App (Con In) (Con a)) (Con b)))
                                    (App (App (Con In) (Con b)) (Con a)))
               (Con axSym)) (Con axMem))
     (App (Con prf) (App (App (Con In) (Con b)) (Con a))))
   True)
; NEGATIVE: axMem (In a b) does not prove (In b a)
!(assertEqual (check CtxNil (Con axMem) (App (Con prf) (App (App (Con In) (Con b)) (Con a)))) False)

; ========================= HOL / STT paradigm ==============================
; A => A   by   impI A A (\h:prf A. h)
!(assertEqual
   (check CtxNil
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))
   True)
; K : A => B => A   by   impI A (B=>A) (\h. impI B A (\g. h))
!(assertEqual
   (check CtxNil
     (App (App (App (Con impI) (Con A)) (App (App (Con imp) (Con B)) (Con A)))
          (Lam (App (Con prf) (Con A))
               (App (App (App (Con impI) (Con B)) (Con A))
                    (Lam (App (Con prf) (Con B)) (Var 1)))))
     (App (Con prf) (App (App (Con imp) (Con A)) (App (App (Con imp) (Con B)) (Con A)))))
   True)
; NEGATIVE: the A=>A proof does not prove  A => B
!(assertEqual
   (check CtxNil
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con B))))
   False)

; ==================== MODULO: conversion = rewriting =======================
; the delta-defined  holds A  is definitionally equal to  prf A
!(assertEqual (conv (App (Def holds) (Con A)) (App (Con prf) (Con A))) True)
