; ============================================================================
; Dedukti cic.dk Stage-1 guest micro.
;
; Source:
;   /home/aimama/aihub/repos/dedukti/libraries/theories/cic.dk
;
; This hosts a tiny CIC-as-guest fragment in MIK.  It is not a port of
; Dedukti and not a replacement checker.  The guest syntax is data; a covered
; proof term lowers into the existing lambda-Pi kernel after a small, explicit
; guest normalization pass whose rewrite footprint is tracked.
; ============================================================================

!(import! &self ../../kernel/kernel_signature_lf_v0.metta)
!(import! &self ../../kernel/kernel_binding_decl_v1.metta)

; ---------- tiny .dk-shaped guest syntax ------------------------------------

(= (dk-lower (DKType)) (Srt type))
(= (dk-lower (DKVar $i)) (Var $i))
(= (dk-lower (DKConst $c)) (Con $c))
(= (dk-lower (DKApp $f $a)) (App (dk-lower $f) (dk-lower $a)))
(= (dk-lower (DKPi $name $A $B)) (Pi (dk-lower $A) (dk-lower $B)))
(= (dk-lower (DKLam $name $A $body))
   (dk-lower-lam-with-decl (dk-lambda-decl) $A $body))

(= (dk-lambda-decl) (Bind1 body))
(= (dk-lambda-body-depth) (binding-decl-depth (dk-lambda-decl) body))
(= (dk-lower-lam-with-decl $decl $A $body)
   (if (== (binding-decl-depth $decl body) 1)
     (Lam (dk-lower $A) (dk-lower $body))
     (Bad bad-dk-lambda-binding-decl)))

; ---------- hosted cic.dk stage-1 signature ---------------------------------
; Covered fragment:
;   Nat, z, s, m
;   Sort, prop, type
;   succ, rule
;   Univ, Term, univ, prod
;
; This is enough for Prop / Type_0 / Type_1 and dependent product hosting in
; the same lambda-Pi kernel used elsewhere in the curriculum.

(= (cic-stage1-sig)
   (SCons (DConst Nat (Srt type))
   (SCons (DConst z (Con Nat))
   (SCons (DConst s (Pi (Con Nat) (Con Nat)))
   (SCons (DConst m (Pi (Con Nat) (Pi (Con Nat) (Con Nat))))
   (SCons (DConst Sort (Srt type))
   (SCons (DConst prop (Con Sort))
   (SCons (DConst type (Pi (Con Nat) (Con Sort)))
   (SCons (DConst succ (Pi (Con Sort) (Con Sort)))
   (SCons (DConst rule (Pi (Con Sort) (Pi (Con Sort) (Con Sort))))
   (SCons (DConst Univ (Pi (Con Sort) (Srt type)))
   (SCons (DConst Term
            (Pi (Con Sort)
              (Pi (App (Con Univ) (Var 0))
                (Srt type))))
   (SCons (DConst univ
            (Pi (Con Sort)
              (App (Con Univ) (App (Con succ) (Var 0)))))
   (SCons (DConst prod
            (Pi (Con Sort)
              (Pi (Con Sort)
                (Pi (App (Con Univ) (Var 1))
                  (Pi (Pi (App (App (Con Term) (Var 2)) (Var 0))
                          (App (Con Univ) (Var 2)))
                    (App (Con Univ) (App (App (Con rule) (Var 3)) (Var 2))))))))
          SNil))))))))))))))

; ---------- guest constructors ----------------------------------------------

(= (dk-univ $s) (DKApp (DKConst Univ) $s))
(= (dk-term $s $a) (DKApp (DKApp (DKConst Term) $s) $a))
(= (dk-prod $s1 $s2 $a $b)
   (DKApp (DKApp (DKApp (DKApp (DKConst prod) $s1) $s2) $a) $b))
(= (dk-type0) (DKApp (DKConst type) (DKConst z)))
(= (dk-type1) (DKApp (DKConst succ) (dk-type0)))

; ---------- explicit rewrite-obligation footprint ---------------------------
; Covered guest rewrites from cic.dk:
;   m i z              --> i
;   m z j              --> j
;   m (s i) (s j)      --> s (m i j)
;   succ prop          --> type z
;   succ (type i)      --> type (s i)
;   rule s1 prop       --> prop
;   rule prop s2       --> s2
;   rule (type i) (type j) --> type (m i j)
;   Term _ (univ s)    --> Univ s
;   Term _ (prod ...)  --> Pi ...

(= (cic-stage1-required-obligations)
   (ObCons rew-m-i-z
     (ObCons rew-m-z-j
       (ObCons rew-m-s-s
         (ObCons rew-term-univ
           (ObCons rew-term-prod
             (ObCons rew-succ-prop
               (ObCons rew-succ-type
                 (ObCons rew-rule-s1-prop
                   (ObCons rew-rule-prop-s2
                     (ObCons rew-rule-type-type ObNil)))))))))))
(= (cic-stage1-obligations-ok $obs)
   (== $obs (cic-stage1-required-obligations)))

; ---------- guest normalization on lowered kernel terms ----------------------
; This is a tiny covered evaluator for the hosted cic.dk fragment.  It is not a
; general Dedukti checker: it only normalizes the exact guest rewrites claimed
; in the obligation footprint above, then hands the result to the real kernel.

(= (cic-nat-nf $n)
   (case $n
     (((Con z) (Con z))
      ((App (Con s) $k) (App (Con s) (cic-nat-nf $k)))
      ((App (App (Con m) $i) $j)
        (let $ni (cic-nat-nf $i)
          (let $nj (cic-nat-nf $j)
            (cic-nat-max $ni $nj))))
      ($other $other))))

(= (cic-nat-max $i $j)
   (unify $j (Con z)
     $i
     (unify $i (Con z)
       $j
       (unify $i (App (Con s) $i0)
         (unify $j (App (Con s) $j0)
           (App (Con s) (cic-nat-max $i0 $j0))
           (App (App (Con m) $i) $j))
         (App (App (Con m) $i) $j)))))

(= (cic-stage1-nf (Var $k)) (Var $k))
(= (cic-stage1-nf (Srt $s)) (Srt $s))
(= (cic-stage1-nf (Con $c)) (Con $c))
(= (cic-stage1-nf (Def $x)) (Def $x))
(= (cic-stage1-nf (Pi $A $B)) (Pi (cic-stage1-nf $A) (cic-stage1-nf $B)))
(= (cic-stage1-nf (Lam $A $b)) (Lam (cic-stage1-nf $A) (cic-stage1-nf $b)))
(= (cic-stage1-nf (Bad $e)) (Bad $e))
(= (cic-stage1-nf (App $f $a))
   (cic-stage1-nf-app (cic-stage1-nf $f) (cic-stage1-nf $a)))

(= (cic-stage1-nf-app $f $a)
   (case $f
     (((Con succ)
        (case $a
          (((Con prop) (App (Con type) (Con z)))
           ((App (Con type) $i) (App (Con type) (App (Con s) (cic-nat-nf $i))))
           ($other (App $f $a)))))
      ((Con m) (App (Con m) (cic-nat-nf $a)))
      ((App (Con m) $i) (cic-nat-max (cic-nat-nf $i) (cic-nat-nf $a)))
      ((App (Con rule) $lhs)
        (case $a
          (((Con prop) (Con prop))
           ($rhs
             (case $lhs
               (((Con prop) $a)
                ((App (Con type) $i)
                  (case $a
                    (((App (Con type) $j)
                       (App (Con type) (cic-nat-nf (App (App (Con m) $i) $j))))
                     ($other (App $f $a)))))
                ($other (App $f $a))))))))
      ((App (Con Term) $sort)
        (case $a
          (((App (Con univ) $s)
             (cic-stage1-nf (App (Con Univ) $s)))
           ((App (App (App (App (Con prod) $s1) $s2) $argA) $b)
             (Pi
               (cic-stage1-nf (App (App (Con Term) $s1) $argA))
               (cic-stage1-nf
                 (App (App (Con Term) (shift 1 0 $s2))
                   (App (shift 1 0 $b) (Var 0))))))
           ($other (App $f $a)))))
      ((Lam $A $b) (cic-stage1-nf (subst 0 $a $b)))
      ($other (App $f $a)))))

(= (cic-stage1-covered-nf $obs $t)
   (if (cic-stage1-obligations-ok $obs)
     (let $lt (dk-lower $t)
       (cic-stage1-nf $lt))
     (Err untracked-cic-rewrite-obligation)))

; ---------- external proof objects ------------------------------------------

(= (cic-proof-check $proof)
   (case $proof
     (((DKCICProof $obs $term $type)
        (if (cic-stage1-obligations-ok $obs)
          (let $lt (dk-lower $term)
            (let $ly (dk-lower $type)
              (kernel-check
                (cic-stage1-sig)
                (cic-stage1-nf $lt)
                (cic-stage1-nf $ly))))
          (Err untracked-cic-rewrite-obligation)))
      ($other (Err unknown-cic-proof-syntax)))))

(= (cic-id-term-source $sort)
   (DKLam A (dk-univ $sort)
     (DKLam x (dk-term $sort (DKVar 0))
       (DKVar 0))))

(= (cic-id-type-source $sort)
   (DKPi A (dk-univ $sort)
     (dk-term $sort
       (dk-prod $sort $sort (DKVar 0)
         (DKLam x (dk-term $sort (DKVar 0))
           (DKVar 1))))))

(= (cic-bad-id-term-source $sort)
   (DKLam A (dk-univ $sort)
     (DKLam x (dk-term $sort (DKVar 0))
       (DKVar 1))))

(= (cic-prop-id-source)
   (DKCICProof
     (cic-stage1-required-obligations)
     (cic-id-term-source (DKConst prop))
     (cic-id-type-source (DKConst prop))))

(= (cic-type0-id-source)
   (DKCICProof
     (cic-stage1-required-obligations)
     (cic-id-term-source (dk-type0))
     (cic-id-type-source (dk-type0))))

(= (cic-type1-id-source)
   (DKCICProof
     (cic-stage1-required-obligations)
     (cic-id-term-source (dk-type1))
     (cic-id-type-source (dk-type1))))

(= (cic-prop-id-untracked-source)
   (DKCICProof
     ObNil
     (cic-id-term-source (DKConst prop))
     (cic-id-type-source (DKConst prop))))

(= (cic-prop-id-bad-source)
   (DKCICProof
     (cic-stage1-required-obligations)
     (cic-bad-id-term-source (DKConst prop))
     (cic-id-type-source (DKConst prop))))

; ---------- checks -----------------------------------------------------------

!(assertEqual (sig-admitted (cic-stage1-sig)) True)
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (DKApp (DKConst succ) (DKConst prop)))
   (App (Con type) (Con z)))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (DKApp (DKConst succ) (dk-type0)))
   (App (Con type) (App (Con s) (Con z))))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (DKApp (DKApp (DKConst m) (DKApp (DKConst s) (DKConst z))) (DKApp (DKConst s) (DKConst z))))
   (App (Con s) (Con z)))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (DKApp (DKApp (DKConst rule) (DKConst prop)) (DKConst prop)))
   (Con prop))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (DKApp (DKApp (DKConst rule) (DKConst prop)) (dk-type0)))
   (dk-lower (dk-type0)))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (DKApp (DKApp (DKConst rule) (dk-type0)) (dk-type0)))
   (dk-lower (dk-type0)))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (DKApp (DKApp (DKConst rule) (dk-type1)) (dk-type0)))
   (App (Con type) (App (Con s) (Con z))))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (dk-term (DKApp (DKConst succ) (DKConst prop))
       (DKApp (DKConst univ) (DKConst prop))))
   (App (Con Univ) (Con prop)))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (cic-id-type-source (DKConst prop)))
   (Pi
     (App (Con Univ) (Con prop))
     (Pi (App (App (Con Term) (Con prop)) (Var 0))
       (App (App (Con Term) (Con prop)) (Var 1)))))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (cic-id-type-source (dk-type0)))
   (Pi
     (App (Con Univ) (App (Con type) (Con z)))
     (Pi (App (App (Con Term) (App (Con type) (Con z))) (Var 0))
       (App (App (Con Term) (App (Con type) (Con z))) (Var 1)))))
!(assertEqual
   (cic-stage1-covered-nf (cic-stage1-required-obligations)
     (cic-id-type-source (dk-type1)))
   (Pi
     (App (Con Univ) (App (Con type) (App (Con s) (Con z))))
     (Pi (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 0))
       (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 1)))))

!(assertEqual
   (cic-proof-check (cic-prop-id-source))
   (Ok (CheckedPrf ANil
     (Lam (App (Con Univ) (Con prop))
       (Lam (App (App (Con Term) (Con prop)) (Var 0))
         (Var 0)))
     (Pi
       (App (Con Univ) (Con prop))
       (Pi (App (App (Con Term) (Con prop)) (Var 0))
         (App (App (Con Term) (Con prop)) (Var 1)))))))
!(assertEqual
   (cic-proof-check (cic-type0-id-source))
   (Ok (CheckedPrf ANil
     (Lam (App (Con Univ) (App (Con type) (Con z)))
       (Lam (App (App (Con Term) (App (Con type) (Con z))) (Var 0))
         (Var 0)))
     (Pi
       (App (Con Univ) (App (Con type) (Con z)))
       (Pi (App (App (Con Term) (App (Con type) (Con z))) (Var 0))
         (App (App (Con Term) (App (Con type) (Con z))) (Var 1)))))))
!(assertEqual
   (cic-proof-check (cic-type1-id-source))
   (Ok (CheckedPrf ANil
     (Lam (App (Con Univ) (App (Con type) (App (Con s) (Con z))))
       (Lam (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 0))
         (Var 0)))
     (Pi
       (App (Con Univ) (App (Con type) (App (Con s) (Con z))))
       (Pi (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 0))
         (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 1)))))))
!(assertEqual
   (cic-proof-check (cic-prop-id-untracked-source))
   (Err untracked-cic-rewrite-obligation))
!(assertEqual
   (cic-proof-check (cic-prop-id-bad-source))
   (Err check-failed))
!(assertEqual (cic-proof-check bogus) (Err unknown-cic-proof-syntax))
