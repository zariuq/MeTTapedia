; =============================================================================
; kernel_signature_metta_rev_involution_slow_v0.metta
;
; Classification: derived / optional-slow.
;
; Optional slow proof-term fixture for the generated MeTTaRev reachability
; signature.  The ordinary 240s parity gate checks the small reverse theorem
; bundle in kernel_signature_metta_rev_v0.metta.  This file keeps the larger
; concrete theorem rev (rev [0,1,2]) = [0,1,2] as a kernel-checked LF proof-term
; artifact outside that fast gate.
;
; Run with an intentionally larger bound:
;   timeout 900 cetta kernel_signature_metta_rev_involution_slow_v0.metta
; =============================================================================

!(import! &self kernel_signature_metta_rev_v0)

; ---------- append derivations needed by the larger reverse proof ------------
(= (mrv-append-nil-list2-type)
   (mrv-reduces (mrv-pappend (mrv-pnil-value) (mrv-list-2)) (mrv-list-2)))
(= (mrv-append-nil-list2-proof) (mrv-append-nil-proof (mrv-list-2)))

(= (mrv-append-list2-list1-type)
   (mrv-reduces (mrv-pappend (mrv-list-2) (mrv-list-1)) (mrv-list-21)))
(= (mrv-append-list2-list1-proof)
   (mrv-append-cons-normal-proof
     (mrv-ptwo) (mrv-pnil-value) (mrv-list-1) (mrv-list-1)
     (Con MeTTaRev:thm:append-nil-list1)))

(= (mrv-append-list1-list0-type)
   (mrv-reduces (mrv-pappend (mrv-list-1) (mrv-list-0)) (mrv-list-10)))
(= (mrv-append-list1-list0-proof)
   (mrv-append-cons-normal-proof
     (mrv-pone) (mrv-pnil-value) (mrv-list-0) (mrv-list-0)
     (Con MeTTaRev:thm:append-nil-list0)))

(= (mrv-append-list21-list0-type)
   (mrv-reduces (mrv-pappend (mrv-list-21) (mrv-list-0)) (mrv-list-210)))
(= (mrv-append-list21-list0-proof)
   (mrv-append-cons-normal-proof
     (mrv-ptwo) (mrv-list-1) (mrv-list-0) (mrv-list-10)
     (mrv-append-list1-list0-proof)))

(= (mrv-append-list1-list2-type)
   (mrv-reduces (mrv-pappend (mrv-list-1) (mrv-list-2)) (mrv-list-12)))
(= (mrv-append-list1-list2-proof)
   (mrv-append-cons-normal-proof
     (mrv-pone) (mrv-pnil-value) (mrv-list-2) (mrv-list-2)
     (mrv-append-nil-list2-proof)))

(= (mrv-append-list01-list2-type)
   (mrv-reduces (mrv-pappend (mrv-list-01) (mrv-list-2)) (mrv-list-012)))
(= (mrv-append-list01-list2-proof)
   (mrv-append-cons-normal-proof
     (mrv-pz) (mrv-list-1) (mrv-list-2) (mrv-list-12)
     (mrv-append-list1-list2-proof)))

; ---------- reverse derivations for [0,1,2] and [2,1,0] ----------------------
(= (mrv-rev-list2-type)
   (mrv-reduces (mrv-prev (mrv-list-2)) (mrv-list-2)))
(= (mrv-rev-list2-proof)
   (mrv-rev-cons-normal-proof
     (mrv-ptwo) (mrv-pnil-value) (mrv-pnil-value) (mrv-list-2)
     (Con MeTTaRev:thm:rev-nil)
     (mrv-append-nil-list2-proof)))

(= (mrv-rev-list12-type)
   (mrv-reduces (mrv-prev (mrv-list-12)) (mrv-list-21)))
(= (mrv-rev-list12-proof)
   (mrv-rev-cons-normal-proof
     (mrv-pone) (mrv-list-2) (mrv-list-2) (mrv-list-21)
     (Con MeTTaRev:thm:rev-list2)
     (mrv-append-list2-list1-proof)))

(= (mrv-rev-list012-type)
   (mrv-reduces (mrv-prev (mrv-list-012)) (mrv-list-210)))
(= (mrv-rev-list012-proof)
   (mrv-rev-cons-normal-proof
     (mrv-pz) (mrv-list-12) (mrv-list-21) (mrv-list-210)
     (Con MeTTaRev:thm:rev-list12)
     (mrv-append-list21-list0-proof)))

(= (mrv-rev-list10-type)
   (mrv-reduces (mrv-prev (mrv-list-10)) (mrv-list-01)))
(= (mrv-rev-list10-proof)
   (mrv-rev-cons-normal-proof
     (mrv-pone) (mrv-list-0) (mrv-list-0) (mrv-list-01)
     (Con MeTTaRev:thm:rev-list0)
     (Con MeTTaRev:thm:append-list0-list1)))

(= (mrv-rev-list210-type)
   (mrv-reduces (mrv-prev (mrv-list-210)) (mrv-list-012)))
(= (mrv-rev-list210-proof)
   (mrv-rev-cons-normal-proof
     (mrv-ptwo) (mrv-list-10) (mrv-list-01) (mrv-list-012)
     (Con MeTTaRev:thm:rev-list10)
     (mrv-append-list01-list2-proof)))

(= (mrv-rev-involution-012-type)
   (mrv-reduces (mrv-prev (mrv-prev (mrv-list-012))) (mrv-list-012)))
(= (mrv-rev-involution-012-proof)
   (mrv-trans
     (mrv-prev (mrv-prev (mrv-list-012)))
     (mrv-prev (mrv-list-210))
     (mrv-list-012)
     (mrv-cong-head
       (mrv-n-rev)
       (mrv-prev (mrv-list-012))
       (mrv-list-210)
       (mrv-pnil)
       (Con MeTTaRev:thm:rev-list012))
     (Con MeTTaRev:thm:rev-list210)))

(= (mrv-rev-involution-012-evaleq-type)
   (mrv-evaleq (mrv-prev (mrv-prev (mrv-list-012))) (mrv-list-012)))
(= (mrv-rev-involution-012-evaleq-proof)
   (mrv-eval-eq-intro
     (mrv-prev (mrv-prev (mrv-list-012)))
     (mrv-list-012)
     (Con MeTTaRev:thm:rev-involution-012)))

; ---------- slow theorem chain ----------------------------------------------
(= (mrv-metta-rev-involution-slow-thms)
   (SCons (DThm MeTTaRev:thm:rev-list2
             (mrv-rev-list2-type)
             (mrv-rev-list2-proof))
   (SCons (DThm MeTTaRev:thm:rev-list12
             (mrv-rev-list12-type)
             (mrv-rev-list12-proof))
   (SCons (DThm MeTTaRev:thm:rev-list012
             (mrv-rev-list012-type)
             (mrv-rev-list012-proof))
   (SCons (DThm MeTTaRev:thm:rev-list10
             (mrv-rev-list10-type)
             (mrv-rev-list10-proof))
   (SCons (DThm MeTTaRev:thm:rev-list210
             (mrv-rev-list210-type)
             (mrv-rev-list210-proof))
   (SCons (DThm MeTTaRev:thm:rev-involution-012
             (mrv-rev-involution-012-type)
             (mrv-rev-involution-012-proof))
   (SCons (DThm MeTTaRev:thm:rev-involution-012-evaleq
             (mrv-rev-involution-012-evaleq-type)
             (mrv-rev-involution-012-evaleq-proof))
          SNil))))))))

(= (mrv-metta-rev-involution-slow-sig)
   (thm-chain-prefix (mrv-metta-rev-stage-sig) (mrv-metta-rev-involution-slow-thms)))

!(assertEqual
   (thm-chain-admitted (mrv-metta-rev-stage-sig) (mrv-metta-rev-involution-slow-thms))
   True)

!(assertEqual (sig-has-name MeTTaRev:thm:rev-involution-012 (mrv-metta-rev-involution-slow-sig)) True)
!(assertEqual (sig-has-name MeTTaRev:thm:rev-involution-012 (mrv-metta-rev-stage-sig)) False)
