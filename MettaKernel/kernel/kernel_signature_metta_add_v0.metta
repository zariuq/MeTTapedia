; =============================================================================
; kernel_signature_metta_add_v0.metta
;
; Classification: derived.
;
; This file is a kernel-side fixture for the MeTTaAdd table-to-signature
; lowering.  The source table is the addDecls rule table in the Lean
; MIEvalHosting path; the declarations below mirror the kernel-admissible
; reachability slice used by that generated surface and are checked by the
; existing lambda-Pi kernel.  There is no evaluator, trace validator, or
; MeTTa-specific checker here: the only witnesses are LF proof terms.
;
; Run:
;   cetta kernel_signature_metta_add_v0.metta
; =============================================================================

!(import! &self kernel_signature_lf_v0)

; ---------- local term shorthands -------------------------------------------
(= (ma-ty) (Srt type))
(= (ma-name-ty) (Con __ldName))
(= (ma-index-ty) (Con __ldIndex))
(= (ma-pattern-ty) (Con __ldPattern))
(= (ma-pattern-list-ty) (Con __ldPatternList))
(= (ma-name-list-ty) (Con __ldNameList))
(= (ma-coll-ty) (Con __ldColl))

(= (ma-pnil) (Con __ldPNil))
(= (ma-pcons $p $rest) (App (App (Con __ldPCons) $p) $rest))
(= (ma-papply $n $args) (App (App (Con __ldPApply) $n) $args))
(= (ma-pfvar $n) (App (Con __ldPFVar) $n))

(= (ma-n-add) (Con name:add))
(= (ma-n-z) (Con name:Z))
(= (ma-n-s) (Con name:S))
(= (ma-n-n) (Con name:n))
(= (ma-n-m) (Con name:m))

(= (ma-pz) (ma-papply (ma-n-z) (ma-pnil)))
(= (ma-ps $x) (ma-papply (ma-n-s) (ma-pcons $x (ma-pnil))))
(= (ma-padd $x $y) (ma-papply (ma-n-add) (ma-pcons $x (ma-pcons $y (ma-pnil)))))
(= (ma-pone) (ma-ps (ma-pz)))
(= (ma-ptwo) (ma-ps (ma-pone)))
(= (ma-pthree) (ma-ps (ma-ptwo)))

(= (ma-reduces $x $y) (App (App (Con MeTTaAdd:Reduces) $x) $y))
(= (ma-evaleq $x $y) (App (App (Con MeTTaAdd:EvalEq) $x) $y))

(= (ma-sig-append SNil $ys) $ys)
(= (ma-sig-append (SCons $x $xs) $ys) (SCons $x (ma-sig-append $xs $ys)))

; ---------- generated signature surface -------------------------------------
(= (ma-extraction-scaffold)
   (SCons (DConst __ldName (ma-ty))
   (SCons (DConst __ldIndex (ma-ty))
   (SCons (DConst __ldPattern (ma-ty))
   (SCons (DConst __ldPatternList (ma-ty))
   (SCons (DConst __ldNameList (ma-ty))
   (SCons (DConst __ldColl (ma-ty))
   (SCons (DConst __ldNoName (ma-name-ty))
   (SCons (DConst __ldNameNil (ma-name-list-ty))
   (SCons (DConst __ldNameCons
             (Pi (ma-name-ty) (Pi (ma-name-list-ty) (ma-name-list-ty))))
   (SCons (DConst __ldPNil (ma-pattern-list-ty))
   (SCons (DConst __ldPCons
             (Pi (ma-pattern-ty) (Pi (ma-pattern-list-ty) (ma-pattern-list-ty))))
   (SCons (DConst __ldPBVar
             (Pi (ma-index-ty) (ma-pattern-ty)))
   (SCons (DConst __ldPFVar
             (Pi (ma-name-ty) (ma-pattern-ty)))
   (SCons (DConst __ldPApply
             (Pi (ma-name-ty) (Pi (ma-pattern-list-ty) (ma-pattern-ty))))
   (SCons (DConst __ldPLambda
             (Pi (ma-name-ty) (Pi (ma-pattern-ty) (ma-pattern-ty))))
   (SCons (DConst __ldPMultiLambda
             (Pi (ma-index-ty)
               (Pi (ma-name-list-ty) (Pi (ma-pattern-ty) (ma-pattern-ty)))))
   (SCons (DConst __ldPSubst
             (Pi (ma-pattern-ty) (Pi (ma-pattern-ty) (ma-pattern-ty))))
   (SCons (DConst __ldPCollection
             (Pi (ma-coll-ty)
               (Pi (ma-pattern-list-ty) (Pi (ma-name-ty) (ma-pattern-ty)))))
   (SCons (DConst __ldCollVec (ma-coll-ty))
   (SCons (DConst __ldCollHashBag (ma-coll-ty))
   (SCons (DConst __ldCollHashSet (ma-coll-ty))
   (SCons (DConst __ldEquationRule
             (Pi (ma-pattern-ty) (Pi (ma-pattern-ty) (ma-ty))))
   (SCons (DConst __ldRewriteRule
             (Pi (ma-pattern-ty) (Pi (ma-pattern-ty) (ma-ty))))
          SNil))))))))))))))))))))))))

(= (ma-language-literals)
   (SCons (DConst MTerm (ma-ty))
   (SCons (DConst name:add (ma-name-ty))
   (SCons (DConst name:Z (ma-name-ty))
   (SCons (DConst name:n (ma-name-ty))
   (SCons (DConst name:S (ma-name-ty))
   (SCons (DConst name:m (ma-name-ty))
          SNil)))))))

(= (ma-p-n-meta) (ma-pfvar (ma-n-n)))
(= (ma-p-m-meta) (ma-pfvar (ma-n-m)))
(= (ma-add-z-left-meta) (ma-padd (ma-pz) (ma-p-n-meta)))
(= (ma-add-s-left-meta) (ma-padd (ma-ps (ma-p-m-meta)) (ma-p-n-meta)))
(= (ma-add-s-right-meta) (ma-ps (ma-padd (ma-p-m-meta) (ma-p-n-meta))))

(= (ma-rewrite-metadata)
   (SCons (DConst rewrite:add-z
             (App (App (Con __ldRewriteRule) (ma-add-z-left-meta)) (ma-p-n-meta)))
   (SCons (DConst rewrite:add-s
             (App (App (Con __ldRewriteRule) (ma-add-s-left-meta)) (ma-add-s-right-meta)))
          SNil)))

(= (ma-reachability-scaffold)
   (SCons (DConst MeTTaAdd:Reduces
             (Pi (ma-pattern-ty) (Pi (ma-pattern-ty) (ma-ty))))
   (SCons (DConst MeTTaAdd:EvalEq
             (Pi (ma-pattern-ty) (Pi (ma-pattern-ty) (ma-ty))))
   (SCons (DConst MeTTaAdd:reduces-refl
             (Pi (ma-pattern-ty) (ma-reduces (Var 0) (Var 0))))
   (SCons (DConst MeTTaAdd:reduces-trans
             (Pi (ma-pattern-ty)
               (Pi (ma-pattern-ty)
                 (Pi (ma-pattern-ty)
                   (Pi (ma-reduces (Var 2) (Var 1))
                     (Pi (ma-reduces (Var 2) (Var 1))
                       (ma-reduces (Var 4) (Var 2))))))))
   (SCons (DConst MeTTaAdd:eval-eq-intro
             (Pi (ma-pattern-ty)
               (Pi (ma-pattern-ty)
                 (Pi (ma-reduces (Var 1) (Var 0))
                   (ma-evaleq (Var 2) (Var 1))))))
   (SCons (DConst MeTTaAdd:reduces-apply-head
             (Pi (ma-name-ty)
               (Pi (ma-pattern-ty)
                 (Pi (ma-pattern-ty)
                   (Pi (ma-pattern-list-ty)
                     (Pi (ma-reduces (Var 2) (Var 1))
                       (ma-reduces
                         (ma-papply (Var 4) (ma-pcons (Var 3) (Var 1)))
                         (ma-papply (Var 4) (ma-pcons (Var 2) (Var 1))))))))))
   (SCons (DConst MeTTaAdd:reduces-apply-second
             (Pi (ma-name-ty)
               (Pi (ma-pattern-ty)
                 (Pi (ma-pattern-ty)
                   (Pi (ma-pattern-ty)
                     (Pi (ma-reduces (Var 1) (Var 0))
                       (ma-reduces
                         (ma-papply (Var 4)
                           (ma-pcons (Var 3)
                             (ma-pcons (Var 2) (ma-pnil))))
                         (ma-papply (Var 4)
                           (ma-pcons (Var 3)
                             (ma-pcons (Var 1) (ma-pnil))))))))))))
          SNil)))))))

(= (ma-rewrite-reachability)
   (SCons (DConst MeTTaAdd:rewrite:add-z
             (Pi (ma-pattern-ty)
               (ma-reduces (ma-padd (ma-pz) (Var 0)) (Var 0))))
   (SCons (DConst MeTTaAdd:rewrite:add-s
             (Pi (ma-pattern-ty)
               (Pi (ma-pattern-ty)
                 (ma-reduces
                   (ma-padd (ma-ps (Var 1)) (Var 0))
                   (ma-ps (ma-padd (Var 1) (Var 0)))))))
          SNil)))

(= (ma-metta-add-sig)
(SCons (DConst __ldName (Srt type))
(SCons (DConst __ldIndex (Srt type))
(SCons (DConst __ldPattern (Srt type))
(SCons (DConst __ldPatternList (Srt type))
(SCons (DConst __ldNameList (Srt type))
(SCons (DConst __ldColl (Srt type))
(SCons (DConst __ldNoName (Con __ldName))
(SCons (DConst __ldNameNil (Con __ldNameList))
(SCons (DConst __ldNameCons (Pi (Con __ldName) (Pi (Con __ldNameList) (Con __ldNameList))))
(SCons (DConst __ldPNil (Con __ldPatternList))
(SCons (DConst __ldPCons (Pi (Con __ldPattern) (Pi (Con __ldPatternList) (Con __ldPatternList))))
(SCons (DConst __ldPBVar (Pi (Con __ldIndex) (Con __ldPattern)))
(SCons (DConst __ldPFVar (Pi (Con __ldName) (Con __ldPattern)))
(SCons (DConst __ldPApply (Pi (Con __ldName) (Pi (Con __ldPatternList) (Con __ldPattern))))
(SCons (DConst __ldPLambda (Pi (Con __ldName) (Pi (Con __ldPattern) (Con __ldPattern))))
(SCons (DConst __ldPMultiLambda (Pi (Con __ldIndex) (Pi (Con __ldNameList) (Pi (Con __ldPattern) (Con __ldPattern)))))
(SCons (DConst __ldPSubst (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Con __ldPattern))))
(SCons (DConst __ldPCollection (Pi (Con __ldColl) (Pi (Con __ldPatternList) (Pi (Con __ldName) (Con __ldPattern)))))
(SCons (DConst __ldCollVec (Con __ldColl))
(SCons (DConst __ldCollHashBag (Con __ldColl))
(SCons (DConst __ldCollHashSet (Con __ldColl))
(SCons (DConst __ldEquationRule (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst __ldRewriteRule (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst MTerm (Srt type))
(SCons (DConst name:add (Con __ldName))
(SCons (DConst name:Z (Con __ldName))
(SCons (DConst name:n (Con __ldName))
(SCons (DConst name:S (Con __ldName))
(SCons (DConst name:m (Con __ldName))
(SCons (DConst rewrite:add-z (App (App (Con __ldRewriteRule) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:Z)) (Con __ldPNil))) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:n))) (Con __ldPNil))))) (App (Con __ldPFVar) (Con name:n))))
(SCons (DConst rewrite:add-s (App (App (Con __ldRewriteRule) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:m))) (Con __ldPNil)))) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:n))) (Con __ldPNil))))) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:m))) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:n))) (Con __ldPNil))))) (Con __ldPNil)))))
(SCons (DConst MeTTaAdd:Reduces (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst MeTTaAdd:EvalEq (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst MeTTaAdd:reduces-refl (Pi (Con __ldPattern) (App (App (Con MeTTaAdd:Reduces) (Var 0)) (Var 0))))
(SCons (DConst MeTTaAdd:reduces-trans (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 2)) (Var 1)) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 2)) (Var 1)) (App (App (Con MeTTaAdd:Reduces) (Var 4)) (Var 2))))))))
(SCons (DConst MeTTaAdd:eval-eq-intro (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 1)) (Var 0)) (App (App (Con MeTTaAdd:EvalEq) (Var 2)) (Var 1))))))
(SCons (DConst MeTTaAdd:reduces-apply-head (Pi (Con __ldName) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (Con __ldPatternList) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 2)) (Var 1)) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 3)) (Var 1)))) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 2)) (Var 1))))))))))
(SCons (DConst MeTTaAdd:reduces-apply-second (Pi (Con __ldName) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 1)) (Var 0)) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 3)) (App (App (Con __ldPCons) (Var 2)) (Con __ldPNil))))) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 3)) (App (App (Con __ldPCons) (Var 1)) (Con __ldPNil)))))))))))
(SCons (DConst MeTTaAdd:rewrite:add-z (Pi (Con __ldPattern) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:Z)) (Con __ldPNil))) (App (App (Con __ldPCons) (Var 0)) (Con __ldPNil))))) (Var 0))))
(SCons (DConst MeTTaAdd:rewrite:add-s (Pi (Con __ldPattern) (Pi (Con __ldPattern) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (Var 1)) (Con __ldPNil)))) (App (App (Con __ldPCons) (Var 0)) (Con __ldPNil))))) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (Var 1)) (App (App (Con __ldPCons) (Var 0)) (Con __ldPNil))))) (Con __ldPNil)))))))
SNil)))))))))))))))))))))))))))))))))))))))))

; ---------- proof terms ------------------------------------------------------
(= (ma-add-z-one-type)
   (ma-reduces (ma-padd (ma-pz) (ma-pone)) (ma-pone)))

(= (ma-add-z-one-proof)
   (App (Con MeTTaAdd:rewrite:add-z) (ma-pone)))

(= (ma-add-s-z-one-root-type)
   (ma-reduces
     (ma-padd (ma-pone) (ma-pone))
     (ma-ps (ma-padd (ma-pz) (ma-pone)))))

(= (ma-add-s-z-one-root-proof)
   (App (App (Con MeTTaAdd:rewrite:add-s) (ma-pz)) (ma-pone)))

(= (ma-s-cong-add-z-one-type)
   (ma-reduces
     (ma-ps (ma-padd (ma-pz) (ma-pone)))
     (ma-ptwo)))

(= (ma-s-cong-add-z-one-proof)
   (App
     (App
       (App
         (App
           (App (Con MeTTaAdd:reduces-apply-head)
             (ma-n-s))
           (ma-padd (ma-pz) (ma-pone)))
         (ma-pone))
       (ma-pnil))
     (ma-add-z-one-proof)))

(= (ma-add-one-one-type)
   (ma-reduces (ma-padd (ma-pone) (ma-pone)) (ma-ptwo)))

(= (ma-add-one-one-proof)
   (App
     (App
       (App
         (App
           (App (Con MeTTaAdd:reduces-trans)
             (ma-padd (ma-pone) (ma-pone)))
           (ma-ps (ma-padd (ma-pz) (ma-pone))))
         (ma-ptwo))
       (ma-add-s-z-one-root-proof))
     (ma-s-cong-add-z-one-proof)))

(= (ma-add-one-one-evaleq-type)
   (ma-evaleq (ma-padd (ma-pone) (ma-pone)) (ma-ptwo)))

(= (ma-add-one-one-evaleq-proof)
   (App
     (App
       (App (Con MeTTaAdd:eval-eq-intro)
         (ma-padd (ma-pone) (ma-pone)))
       (ma-ptwo))
     (ma-add-one-one-proof)))

(= (ma-add-s-one-one-root-type)
   (ma-reduces
     (ma-padd (ma-ptwo) (ma-pone))
     (ma-ps (ma-padd (ma-pone) (ma-pone)))))

(= (ma-add-s-one-one-root-proof)
   (App (App (Con MeTTaAdd:rewrite:add-s) (ma-pone)) (ma-pone)))

(= (ma-s-cong-add-one-one-type)
   (ma-reduces
     (ma-ps (ma-padd (ma-pone) (ma-pone)))
     (ma-pthree)))

(= (ma-s-cong-add-one-one-proof)
   (App
     (App
       (App
         (App
           (App (Con MeTTaAdd:reduces-apply-head)
             (ma-n-s))
           (ma-padd (ma-pone) (ma-pone)))
         (ma-ptwo))
       (ma-pnil))
     (ma-add-one-one-proof)))

(= (ma-add-two-one-type)
   (ma-reduces (ma-padd (ma-ptwo) (ma-pone)) (ma-pthree)))

(= (ma-add-two-one-proof)
   (App
     (App
       (App
         (App
           (App (Con MeTTaAdd:reduces-trans)
             (ma-padd (ma-ptwo) (ma-pone)))
           (ma-ps (ma-padd (ma-pone) (ma-pone))))
         (ma-pthree))
       (ma-add-s-one-one-root-proof))
     (ma-s-cong-add-one-one-proof)))

(= (ma-add-two-one-evaleq-type)
   (ma-evaleq (ma-padd (ma-ptwo) (ma-pone)) (ma-pthree)))

(= (ma-add-two-one-evaleq-proof)
   (App
     (App
       (App (Con MeTTaAdd:eval-eq-intro)
         (ma-padd (ma-ptwo) (ma-pone)))
       (ma-pthree))
     (ma-add-two-one-proof)))

(= (ma-add-z-one-false-target-type)
   (ma-reduces (ma-padd (ma-pz) (ma-pone)) (ma-pz)))

(= (ma-add-z-one-wrong-source-type)
   (ma-reduces (ma-padd (ma-pone) (ma-pone)) (ma-pone)))

(= (ma-add-one-one-false-target-type)
   (ma-reduces (ma-padd (ma-pone) (ma-pone)) (ma-pone)))

(= (ma-add-two-one-false-target-type)
   (ma-reduces (ma-padd (ma-ptwo) (ma-pone)) (ma-ptwo)))

(= (ma-metta-add-thms)
   (SCons (DThm MeTTaAdd:thm:add-z-one
             (ma-add-z-one-type)
             (ma-add-z-one-proof))
   (SCons (DThm MeTTaAdd:thm:add-s-z-one-root
             (ma-add-s-z-one-root-type)
             (ma-add-s-z-one-root-proof))
   (SCons (DThm MeTTaAdd:thm:add-one-one
             (ma-add-one-one-type)
             (ma-add-one-one-proof))
   (SCons (DThm MeTTaAdd:thm:add-one-one-evaleq
             (ma-add-one-one-evaleq-type)
             (ma-add-one-one-evaleq-proof))
   (SCons (DThm MeTTaAdd:thm:add-two-one
             (ma-add-two-one-type)
             (ma-add-two-one-proof))
   (SCons (DThm MeTTaAdd:thm:add-two-one-evaleq
             (ma-add-two-one-evaleq-type)
             (ma-add-two-one-evaleq-proof))
          SNil)))))))

; ---------- gates ------------------------------------------------------------
!(assertEqual (unique-sig (ma-metta-add-sig)) True)
!(assertEqual (wf-sig-prefix SNil (ma-metta-add-sig)) True)
!(assertEqual (sig-admitted (ma-metta-add-sig)) True)
!(assertEqual (thm-chain-admitted (ma-metta-add-sig) (ma-metta-add-thms)) True)

!(assertEqual
   (kernel-check (ma-metta-add-sig) (ma-add-z-one-proof) (ma-add-z-one-type))
   (Ok (CheckedPrf ANil (ma-add-z-one-proof) (ma-add-z-one-type))))

!(assertEqual
   (kernel-check (ma-metta-add-sig) (ma-add-z-one-proof) (ma-add-z-one-false-target-type))
   (Err check-failed))

!(assertEqual
   (kernel-check (ma-metta-add-sig) (ma-add-z-one-proof) (ma-add-z-one-wrong-source-type))
   (Err check-failed))

!(assertEqual
   (kernel-check-batch-judgments-with-thms
     (ma-metta-add-sig)
     (ma-metta-add-thms)
     (Cons (Accept
       (Con MeTTaAdd:thm:add-one-one)
       (ma-add-one-one-type))
     (Cons (Accept
       (Con MeTTaAdd:thm:add-one-one-evaleq)
       (ma-add-one-one-evaleq-type))
     (Cons (Accept
       (Con MeTTaAdd:thm:add-two-one)
       (ma-add-two-one-type))
     (Cons (Accept
       (Con MeTTaAdd:thm:add-two-one-evaleq)
       (ma-add-two-one-evaleq-type))
     (Cons (Reject
       (Con MeTTaAdd:thm:add-two-one)
       (ma-add-two-one-false-target-type))
     (Cons (Reject
       (Con MeTTaAdd:thm:add-one-one)
       (ma-add-one-one-false-target-type))
     (Cons (Reject
       (Con MeTTaAdd:thm:add-z-one)
       (ma-add-z-one-false-target-type))
       Nil))))))))
   True)
