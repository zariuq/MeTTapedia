; =============================================================================
; kernel_signature_metta_rev_v0.metta
;
; Classification: derived.
;
; Kernel-side proof-term fixture for the generated MeTTaRev reachability
; signature.  The signature itself is generated from the reverse rule table; this
; file only constructs LF proof terms over that signature and asks the existing
; lambda-Pi kernel to check them.  No evaluator, trace checker, or MeTTa-specific
; proof validator is defined here.
;
; Run:
;   cetta kernel_signature_metta_rev_v0.metta
; =============================================================================

!(import! &self kernel_signature_metta_rev_generated_v0)

; ---------- local term shorthands -------------------------------------------
(= (mrv-metta-rev-sig) (mr-generated-metta-rev-sig))

(= (mrv-pnil) (Con __ldPNil))
(= (mrv-pcons $p $rest) (App (App (Con __ldPCons) $p) $rest))
(= (mrv-papply $n $args) (App (App (Con __ldPApply) $n) $args))

(= (mrv-n-z) (Con name:Z))
(= (mrv-n-s) (Con name:S))
(= (mrv-n-nil) (Con name:Nil))
(= (mrv-n-cons) (Con name:Cons))
(= (mrv-n-rev) (Con name:rev))
(= (mrv-n-append) (Con name:listAppend))

(= (mrv-pz) (mrv-papply (mrv-n-z) (mrv-pnil)))
(= (mrv-ps $x) (mrv-papply (mrv-n-s) (mrv-pcons $x (mrv-pnil))))
(= (mrv-pone) (mrv-ps (mrv-pz)))
(= (mrv-ptwo) (mrv-ps (mrv-pone)))

(= (mrv-pnil-value) (mrv-papply (mrv-n-nil) (mrv-pnil)))
(= (mrv-pcons-value $x $xs)
   (mrv-papply (mrv-n-cons) (mrv-pcons $x (mrv-pcons $xs (mrv-pnil)))))
(= (mrv-singleton $x) (mrv-pcons-value $x (mrv-pnil-value)))
(= (mrv-prev $xs) (mrv-papply (mrv-n-rev) (mrv-pcons $xs (mrv-pnil))))
(= (mrv-pappend $xs $ys)
   (mrv-papply (mrv-n-append) (mrv-pcons $xs (mrv-pcons $ys (mrv-pnil)))))

(= (mrv-list-0) (mrv-singleton (mrv-pz)))
(= (mrv-list-1) (mrv-singleton (mrv-pone)))
(= (mrv-list-2) (mrv-singleton (mrv-ptwo)))
(= (mrv-list-01) (mrv-pcons-value (mrv-pz) (mrv-list-1)))
(= (mrv-list-10) (mrv-pcons-value (mrv-pone) (mrv-list-0)))
(= (mrv-list-12) (mrv-pcons-value (mrv-pone) (mrv-list-2)))
(= (mrv-list-21) (mrv-pcons-value (mrv-ptwo) (mrv-list-1)))
(= (mrv-list-012) (mrv-pcons-value (mrv-pz) (mrv-list-12)))
(= (mrv-list-210) (mrv-pcons-value (mrv-ptwo) (mrv-list-10)))

(= (mrv-reduces $x $y) (App (App (Con MeTTaRev:Reduces) $x) $y))
(= (mrv-evaleq $x $y) (App (App (Con MeTTaRev:EvalEq) $x) $y))

; ---------- proof-term shorthands -------------------------------------------
(= (mrv-trans $x $y $z $xy $yz)
   (App
     (App
       (App
         (App
           (App (Con MeTTaRev:reduces-trans) $x)
           $y)
         $z)
       $xy)
     $yz))

(= (mrv-cong-head $head $p $q $rest $proof)
   (App
     (App
       (App
         (App
           (App (Con MeTTaRev:reduces-apply-head) $head)
           $p)
         $q)
       $rest)
     $proof))

(= (mrv-cong-second $head $first $p $q $proof)
   (App
     (App
       (App
         (App
           (App (Con MeTTaRev:reduces-apply-second) $head)
           $first)
         $p)
       $q)
     $proof))

(= (mrv-eval-eq-intro $x $y $proof)
   (App
     (App
       (App (Con MeTTaRev:eval-eq-intro) $x)
       $y)
     $proof))

(= (mrv-append-nil-proof $ys)
   (App (Con MeTTaRev:rewrite:append-nil) $ys))

(= (mrv-append-cons-step-proof $x $xs $ys)
   (App (App (App (Con MeTTaRev:rewrite:append-cons) $x) $xs) $ys))

(= (mrv-rev-nil-proof)
   (Con MeTTaRev:rewrite:rev-nil))

(= (mrv-rev-cons-step-proof $x $xs)
   (App (App (Con MeTTaRev:rewrite:rev-cons) $x) $xs))

(= (mrv-append-cons-normal-proof $x $xs $ys $result $tail-proof)
   (mrv-trans
     (mrv-pappend (mrv-pcons-value $x $xs) $ys)
     (mrv-pcons-value $x (mrv-pappend $xs $ys))
     (mrv-pcons-value $x $result)
     (mrv-append-cons-step-proof $x $xs $ys)
     (mrv-cong-second (mrv-n-cons) $x (mrv-pappend $xs $ys) $result $tail-proof)))

(= (mrv-rev-cons-normal-proof $x $xs $rev-xs $result $rev-xs-proof $append-proof)
   (mrv-trans
     (mrv-prev (mrv-pcons-value $x $xs))
     (mrv-pappend (mrv-prev $xs) (mrv-singleton $x))
     $result
     (mrv-rev-cons-step-proof $x $xs)
     (mrv-trans
       (mrv-pappend (mrv-prev $xs) (mrv-singleton $x))
       (mrv-pappend $rev-xs (mrv-singleton $x))
       $result
       (mrv-cong-head
         (mrv-n-append)
         (mrv-prev $xs)
         $rev-xs
         (mrv-pcons (mrv-singleton $x) (mrv-pnil))
         $rev-xs-proof)
       $append-proof)))

; ---------- concrete append derivations -------------------------------------
(= (mrv-append-nil-list0-type)
   (mrv-reduces (mrv-pappend (mrv-pnil-value) (mrv-list-0)) (mrv-list-0)))
(= (mrv-append-nil-list0-proof) (mrv-append-nil-proof (mrv-list-0)))

(= (mrv-append-nil-list1-type)
   (mrv-reduces (mrv-pappend (mrv-pnil-value) (mrv-list-1)) (mrv-list-1)))
(= (mrv-append-nil-list1-proof) (mrv-append-nil-proof (mrv-list-1)))

(= (mrv-append-list0-list1-type)
   (mrv-reduces (mrv-pappend (mrv-list-0) (mrv-list-1)) (mrv-list-01)))
(= (mrv-append-list0-list1-proof)
   (mrv-append-cons-normal-proof
     (mrv-pz) (mrv-pnil-value) (mrv-list-1) (mrv-list-1)
     (Con MeTTaRev:thm:append-nil-list1)))

; ---------- concrete reverse derivations ------------------------------------
(= (mrv-rev-nil-type)
   (mrv-reduces (mrv-prev (mrv-pnil-value)) (mrv-pnil-value)))

(= (mrv-rev-list0-type)
   (mrv-reduces (mrv-prev (mrv-list-0)) (mrv-list-0)))
(= (mrv-rev-list0-proof)
   (mrv-rev-cons-normal-proof
     (mrv-pz) (mrv-pnil-value) (mrv-pnil-value) (mrv-list-0)
     (Con MeTTaRev:thm:rev-nil)
     (Con MeTTaRev:thm:append-nil-list0)))

(= (mrv-rev-involution-list0-type)
   (mrv-reduces (mrv-prev (mrv-prev (mrv-list-0))) (mrv-list-0)))
(= (mrv-rev-involution-list0-proof)
   (mrv-trans
     (mrv-prev (mrv-prev (mrv-list-0)))
     (mrv-prev (mrv-list-0))
     (mrv-list-0)
     (mrv-cong-head
       (mrv-n-rev)
       (mrv-prev (mrv-list-0))
       (mrv-list-0)
       (mrv-pnil)
       (Con MeTTaRev:thm:rev-list0))
     (Con MeTTaRev:thm:rev-list0)))

(= (mrv-rev-involution-list0-evaleq-type)
   (mrv-evaleq (mrv-prev (mrv-prev (mrv-list-0))) (mrv-list-0)))
(= (mrv-rev-involution-list0-evaleq-proof)
   (mrv-eval-eq-intro
     (mrv-prev (mrv-prev (mrv-list-0)))
     (mrv-list-0)
     (Con MeTTaRev:thm:rev-involution-list0)))

; ---------- negative targets -------------------------------------------------
(= (mrv-rev-nil-false-target-type)
   (mrv-reduces (mrv-prev (mrv-pnil-value)) (mrv-list-0)))

(= (mrv-rev-involution-list0-false-target-type)
   (mrv-reduces (mrv-prev (mrv-prev (mrv-list-0))) (mrv-list-1)))

(= (mrv-append-nil-wrong-source-type)
   (mrv-reduces (mrv-pappend (mrv-list-0) (mrv-list-1)) (mrv-list-1)))

; ---------- theorem bundle and gates ----------------------------------------
(= (mrv-metta-rev-thms)
   (SCons (DThm MeTTaRev:thm:rev-nil
             (mrv-rev-nil-type)
             (mrv-rev-nil-proof))
   (SCons (DThm MeTTaRev:thm:append-nil-list0
             (mrv-append-nil-list0-type)
             (mrv-append-nil-list0-proof))
   (SCons (DThm MeTTaRev:thm:append-nil-list1
             (mrv-append-nil-list1-type)
             (mrv-append-nil-list1-proof))
   (SCons (DThm MeTTaRev:thm:append-list0-list1
             (mrv-append-list0-list1-type)
             (mrv-append-list0-list1-proof))
   (SCons (DThm MeTTaRev:thm:rev-list0
             (mrv-rev-list0-type)
             (mrv-rev-list0-proof))
   (SCons (DThm MeTTaRev:thm:rev-involution-list0
             (mrv-rev-involution-list0-type)
             (mrv-rev-involution-list0-proof))
   (SCons (DThm MeTTaRev:thm:rev-involution-list0-evaleq
             (mrv-rev-involution-list0-evaleq-type)
             (mrv-rev-involution-list0-evaleq-proof))
          SNil))))))))

(= (mrv-metta-rev-stage-sig)
   (thm-chain-prefix (mrv-metta-rev-sig) (mrv-metta-rev-thms)))

!(assertEqual (sig-admitted (mrv-metta-rev-sig)) True)
!(assertEqual (thm-chain-admitted (mrv-metta-rev-sig) (mrv-metta-rev-thms)) True)

!(assertEqual
   (kernel-check (mrv-metta-rev-sig) (mrv-rev-nil-proof) (mrv-rev-nil-type))
   (Ok (CheckedPrf ANil (mrv-rev-nil-proof) (mrv-rev-nil-type))))

!(assertEqual
   (kernel-check (mrv-metta-rev-sig) (mrv-rev-nil-proof) (mrv-rev-nil-false-target-type))
   (Err check-failed))

!(assertEqual
   (kernel-check (mrv-metta-rev-sig) (mrv-append-nil-list0-proof) (mrv-append-nil-wrong-source-type))
   (Err check-failed))

!(assertEqual
   (kernel-check-batch-judgments-with-thms
     (mrv-metta-rev-sig)
     (mrv-metta-rev-thms)
     (Cons (Accept
       (Con MeTTaRev:thm:append-list0-list1)
       (mrv-append-list0-list1-type))
     (Cons (Accept
       (Con MeTTaRev:thm:rev-involution-list0)
       (mrv-rev-involution-list0-type))
     (Cons (Accept
       (Con MeTTaRev:thm:rev-involution-list0-evaleq)
       (mrv-rev-involution-list0-evaleq-type))
     (Cons (Reject
       (Con MeTTaRev:thm:rev-involution-list0)
       (mrv-rev-involution-list0-false-target-type))
     (Cons (Reject
       (Con MeTTaRev:thm:rev-nil)
       (mrv-rev-nil-false-target-type))
       Nil))))))
   True)
