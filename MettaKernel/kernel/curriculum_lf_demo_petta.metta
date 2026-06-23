!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; =============================================================================
;  curriculum_lf_demo.metta
;  ONE lambda-Pi-modulo kernel  x  THREE paradigm signatures  x  easy curriculum
;  theorems from each -- the unified-waist thesis, made runnable.
;
;  Kernel core = Claude Web's mettakernel + Codex's CeTTa-safe repair
;  (Bad-propagation; infer_app/infer_lam helper factoring; lambda-domain must be a
;   proper type).  Object logics are SIGNATURES over this one checker, never
;   changes to it -- HOL/STT, DTT (inductive data + identity), HOTG (sets + axioms).
;
;  Each paradigm shows POSITIVES (a real typed/sealed proof term checks) and a
;  NEGATIVE (a wrong proof is rejected).  Run:
;    /home/aimama/aihub/hyperon/CeTTa/cetta curriculum_lf_demo.metta
; =============================================================================

; ============================ THE TRUSTED KERNEL ============================
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
(= (nf (App $f $a)) (nf_app (nf $f) (nf $a)))
(= (nf_app $f $a) (unify $f (Lam $A $b) (nf (subst 0 $a $b)) (App $f $a)))
(= (is_bad $x) (unify $x (Bad $e) True False))
(= (conv $x $y) (if (is_bad (nf $x)) False (if (is_bad (nf $y)) False (== (nf $x) (nf $y)))))

(= (ctx_nth $i CtxNil) (Bad var_out_of_range))
(= (ctx_nth $i (CtxCons $h $t)) (if (== $i 0) $h (ctx_nth (- $i 1) $t)))
(= (ctx_type $i $ctx) (shift (+ $i 1) 0 (ctx_nth $i $ctx)))

(= (pts_rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi_bad_codomain)))
     (Bad pi_domain_not_type)))

(= (infer $ctx (Srt type)) (Srt kind))
(= (infer $ctx (Srt kind)) (Bad kind_is_topsort))
(= (infer $ctx (Var $i))  (ctx_type $i $ctx))
(= (infer $ctx (Con $c))  (sigT $c))
(= (infer $ctx (Def $c))  (sigT $c))
(= (infer $ctx (Pi $A $B))
   (let $sA (nf (infer $ctx $A))
     (let $sB (nf (infer (CtxCons $A $ctx) $B)) (pts_rule $sA $sB))))
(= (infer_lam $ctx $A $b)
   (let $sA (nf (infer $ctx $A))
     (unify $sA (Srt type)
        (let $tb (infer (CtxCons $A $ctx) $b)
          (if (is_bad (nf $tb)) (Bad lam_body_bad_type) (Pi $A $tb)))
        (Bad lam_domain_not_a_type))))
(= (infer $ctx (Lam $A $b)) (infer_lam $ctx $A $b))
(= (infer_app $ctx $f $a)
   (let $tf (nf (infer $ctx $f))
     (unify $tf (Pi $A $B)
        (if (conv (infer $ctx $a) $A) (subst 0 $a $B) (Bad arg_type_mismatch))
        (Bad applied_a_non_function))))
(= (infer $ctx (App $f $a)) (infer_app $ctx $f $a))
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
!(test (infer CtxNil (Srt type)) (Srt kind))
!(test (infer CtxNil (App (Con prf) (Con A))) (Srt type))
; Bad is not a type: the safe checker rejects failed inference results instead
; of letting them masquerade as ordinary terms/types.
!(test (infer CtxNil (Lam (Srt type) (Var 0))) (Bad lam_domain_not_a_type))
!(test (check CtxNil (Lam (Con o) (Srt kind)) (Pi (Con o) (Bad kind_is_topsort))) False)

; ============================ DTT paradigm =================================
; numeral  s (s z) : nat
!(test (check CtxNil (App (Con s) (App (Con s) (Con z))) (Con nat)) True)
; identity intro:  rfl z : eqn z z
!(test (check CtxNil (App (Con rfl) (Con z)) (App (App (Con eqn) (Con z)) (Con z))) True)
; NEGATIVE: rfl z does not prove  eqn z (s z)
!(test (check CtxNil (App (Con rfl) (Con z)) (App (App (Con eqn) (Con z)) (App (Con s) (Con z)))) False)

; =========================== HOTG paradigm =================================
; the ledgered axiom inhabits its stated proposition:  axMem : prf (In a b)
!(test (check CtxNil (Con axMem) (App (Con prf) (App (App (Con In) (Con a)) (Con b)))) True)
; axioms compose through the HOL rule impE:  In b a  from  (In a b => In b a) and (In a b)
!(test
   (check CtxNil
     (App (App (App (App (Con impE) (App (App (Con In) (Con a)) (Con b)))
                                    (App (App (Con In) (Con b)) (Con a)))
               (Con axSym)) (Con axMem))
     (App (Con prf) (App (App (Con In) (Con b)) (Con a))))
   True)
; NEGATIVE: axMem (In a b) does not prove (In b a)
!(test (check CtxNil (Con axMem) (App (Con prf) (App (App (Con In) (Con b)) (Con a)))) False)

; ========================= HOL / STT paradigm ==============================
; A => A   by   impI A A (\h:prf A. h)
!(test
   (check CtxNil
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))
   True)
; K : A => B => A   by   impI A (B=>A) (\h. impI B A (\g. h))
!(test
   (check CtxNil
     (App (App (App (Con impI) (Con A)) (App (App (Con imp) (Con B)) (Con A)))
          (Lam (App (Con prf) (Con A))
               (App (App (App (Con impI) (Con B)) (Con A))
                    (Lam (App (Con prf) (Con B)) (Var 1)))))
     (App (Con prf) (App (App (Con imp) (Con A)) (App (App (Con imp) (Con B)) (Con A)))))
   True)
; NEGATIVE: the A=>A proof does not prove  A => B
!(test
   (check CtxNil
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con B))))
   False)

; ==================== MODULO: conversion = rewriting =======================
; the delta-defined  holds A  is definitionally equal to  prf A
!(test (conv (App (Def holds) (Con A)) (App (Con prf) (Con A))) True)
