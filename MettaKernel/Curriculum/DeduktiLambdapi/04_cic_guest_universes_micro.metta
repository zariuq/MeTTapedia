; ============================================================================
; Dedukti cic.dk Stage-3 universes/cumulativity micro.
;
; Source:
;   /home/aimama/aihub/repos/dedukti/libraries/theories/cic.dk
;
; This extends the hosted Stage-1 cic.dk fragment with a minimal `max` / `lift`
; foothold so external guest proof terms can witness cumulativity and still be
; re-checked by the real lambda-Pi kernel. This is not a full cic.dk guest:
; the covered rewrite footprint is explicit and only the covered fragment is
; claimed here.
; ============================================================================

!(import! &self 02_cic_guest_sorts_pi_micro.metta)

; ---------- additional guest constructors -----------------------------------

(= (dk-type2) (DKApp (DKConst succ) (dk-type1)))

(= (dk-max $s1 $s2)
   (DKApp (DKApp (DKConst max) $s1) $s2))
(= (dk-lift $s1 $s2 $a)
   (DKApp (DKApp (DKApp (DKConst lift) $s1) $s2) $a))

; ---------- hosted cic.dk stage-3 signature ---------------------------------
; Covered extension beyond Stage-1:
;   max, lift
; together with the small cumulativity-facing rewrite footprint used below.

(= (cic-stage3-sig)
   (SCons (DConst Nat (Srt type))
   (SCons (DConst z (Con Nat))
   (SCons (DConst s (Pi (Con Nat) (Con Nat)))
   (SCons (DConst m (Pi (Con Nat) (Pi (Con Nat) (Con Nat))))
   (SCons (DConst Sort (Srt type))
   (SCons (DConst prop (Con Sort))
   (SCons (DConst type (Pi (Con Nat) (Con Sort)))
   (SCons (DConst succ (Pi (Con Sort) (Con Sort)))
   (SCons (DConst rule (Pi (Con Sort) (Pi (Con Sort) (Con Sort))))
   (SCons (DConst max (Pi (Con Sort) (Pi (Con Sort) (Con Sort))))
   (SCons (DConst Univ (Pi (Con Sort) (Srt type)))
   (SCons (DConst Term
            (Pi (Con Sort)
              (Pi (App (Con Univ) (Var 0))
                (Srt type))))
   (SCons (DConst univ
            (Pi (Con Sort)
              (App (Con Univ) (App (Con succ) (Var 0)))))
   (SCons (DConst lift
            (Pi (Con Sort)
              (Pi (Con Sort)
                (Pi (App (Con Univ) (Var 1))
                  (App (Con Univ)
                    (App (App (Con max) (Var 2)) (Var 1)))))))
   (SCons (DConst prod
            (Pi (Con Sort)
              (Pi (Con Sort)
                (Pi (App (Con Univ) (Var 1))
                  (Pi (Pi (App (App (Con Term) (Var 2)) (Var 0))
                          (App (Con Univ) (Var 2)))
                    (App (Con Univ) (App (App (Con rule) (Var 3)) (Var 2))))))))
          SNil))))))))))))))))

; ---------- explicit rewrite-obligation footprint ---------------------------
; Stage-1 rules stay live here; this row adds the minimal max/lift subset needed
; for direct cumulativity witnesses.

(= (cic-stage3-required-obligations)
   (ObCons rew-term-lift
     (ObCons rew-lift-id
       (ObCons rew-max-s1-prop
         (ObCons rew-max-prop-s2
           (ObCons rew-max-type-type
             (cic-stage1-required-obligations)))))))
(= (cic-stage3-obligations-ok $obs)
   (== $obs (cic-stage3-required-obligations)))

; ---------- guest normalization on lowered kernel terms ----------------------

(= (cic-stage3-nf (Var $k)) (Var $k))
(= (cic-stage3-nf (Srt $s)) (Srt $s))
(= (cic-stage3-nf (Con $c)) (Con $c))
(= (cic-stage3-nf (Def $x)) (Def $x))
(= (cic-stage3-nf (Pi $A $B)) (Pi (cic-stage3-nf $A) (cic-stage3-nf $B)))
(= (cic-stage3-nf (Lam $A $b)) (Lam (cic-stage3-nf $A) (cic-stage3-nf $b)))
(= (cic-stage3-nf (Bad $e)) (Bad $e))
(= (cic-stage3-nf (App $f $a))
   (cic-stage3-nf-app (cic-stage3-nf $f) (cic-stage3-nf $a)))

(= (cic-stage3-nf-app $f $a)
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
      ((App (Con max) $lhs)
        (case $a
          (((Con prop) (cic-stage3-nf $lhs))
           ($rhs
             (case $lhs
               (((Con prop) $rhs)
                ((App (Con type) $i)
                  (case $rhs
                    (((App (Con type) $j)
                       (App (Con type) (cic-nat-nf (App (App (Con m) $i) $j))))
                     ($other (App $f $a)))))
                ($other (App $f $a))))))))
      ((App (App (Con lift) $s1) $s2)
        (if (== $s1 $s2)
          $a
          (App $f $a)))
      ((App (Con Term) $sort)
        (case $a
          (((App (Con univ) $s)
             (cic-stage3-nf (App (Con Univ) $s)))
           ((App (App (App (Con lift) $s1) $s2) $u)
             (cic-stage3-nf
               (App (App (Con Term) $s1) $u)))
           ((App (App (App (App (Con prod) $s1) $s2) $argA) $b)
             (Pi
               (cic-stage3-nf (App (App (Con Term) $s1) $argA))
               (cic-stage3-nf
                 (App (App (Con Term) (shift 1 0 $s2))
                   (App (shift 1 0 $b) (Var 0))))))
           ($other (App $f $a)))))
      ((Lam $A $b) (cic-stage3-nf (subst 0 $a $b)))
      ($other (App $f $a)))))

(= (cic-stage3-covered-nf $obs $t)
   (if (cic-stage3-obligations-ok $obs)
     (let $lt (dk-lower $t)
       (cic-stage3-nf $lt))
     (Err untracked-cic-rewrite-obligation)))

; ---------- external proof objects ------------------------------------------

(= (cic-stage3-proof-check $proof)
   (case $proof
     (((DKCICProof $obs $term $type)
        (if (cic-stage3-obligations-ok $obs)
          (let $lt (dk-lower $term)
            (let $ly (dk-lower $type)
              (kernel-check
                (cic-stage3-sig)
                (cic-stage3-nf $lt)
                (cic-stage3-nf $ly))))
          (Err untracked-cic-rewrite-obligation)))
      ($other (Err unknown-cic-proof-syntax)))))

(= (cic-cumul-term-source $sortLo)
   (DKLam A (dk-univ $sortLo)
     (DKLam x (dk-term $sortLo (DKVar 0))
       (DKVar 0))))

(= (cic-cumul-type-source $sortLo $sortHi)
   (DKPi A (dk-univ $sortLo)
     (DKPi x (dk-term $sortLo (DKVar 0))
       (dk-term $sortHi
         (dk-lift $sortLo $sortHi (DKVar 1))))))

(= (cic-bad-cumul-term-source $sortLo)
   (DKLam A (dk-univ $sortLo)
     (DKLam x (dk-term $sortLo (DKVar 0))
       (DKVar 1))))

(= (cic-prop-to-type0-cumul-source)
   (DKCICProof
     (cic-stage3-required-obligations)
     (cic-cumul-term-source (DKConst prop))
     (cic-cumul-type-source (DKConst prop) (dk-type0))))

(= (cic-type0-to-type1-cumul-source)
   (DKCICProof
     (cic-stage3-required-obligations)
     (cic-cumul-term-source (dk-type0))
     (cic-cumul-type-source (dk-type0) (dk-type1))))

(= (cic-type1-to-type2-cumul-source)
   (DKCICProof
     (cic-stage3-required-obligations)
     (cic-cumul-term-source (dk-type1))
     (cic-cumul-type-source (dk-type1) (dk-type2))))

(= (cic-prop-to-type0-cumul-untracked-source)
   (DKCICProof
     ObNil
     (cic-cumul-term-source (DKConst prop))
     (cic-cumul-type-source (DKConst prop) (dk-type0))))

(= (cic-type0-to-type1-cumul-bad-source)
   (DKCICProof
     (cic-stage3-required-obligations)
     (cic-bad-cumul-term-source (dk-type0))
     (cic-cumul-type-source (dk-type0) (dk-type1))))

(= (cic-type1-to-type2-cumul-bad-source)
   (DKCICProof
     (cic-stage3-required-obligations)
     (cic-bad-cumul-term-source (dk-type1))
     (cic-cumul-type-source (dk-type1) (dk-type2))))

; ---------- checks -----------------------------------------------------------

!(assertEqual (sig-admitted (cic-stage3-sig)) True)

!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-max (DKConst prop) (dk-type0)))
   (dk-lower (dk-type0)))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-max (dk-type0) (DKConst prop)))
   (dk-lower (dk-type0)))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-max (dk-type0) (dk-type0)))
   (dk-lower (dk-type0)))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-max (dk-type1) (dk-type0)))
   (App (Con type) (App (Con s) (Con z))))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-max (dk-type0) (dk-type1)))
   (App (Con type) (App (Con s) (Con z))))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-lift (DKConst prop) (DKConst prop)
       (DKApp (DKConst univ) (DKConst prop))))
   (App (Con univ) (Con prop)))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-term (dk-type0)
       (dk-lift (DKConst prop) (dk-type0)
         (DKApp (DKConst univ) (DKConst prop)))))
   (App (Con Univ) (Con prop)))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-term (dk-type1)
       (dk-lift (dk-type0) (dk-type1)
         (DKApp (DKConst univ) (dk-type0)))))
   (App (Con Univ) (dk-lower (dk-type0))))
!(assertEqual
   (cic-stage3-covered-nf (cic-stage3-required-obligations)
     (dk-term (dk-type2)
       (dk-lift (dk-type1) (dk-type2)
         (DKApp (DKConst univ) (dk-type1)))))
   (App (Con Univ) (App (Con type) (App (Con s) (Con z)))))
!(assertEqual
   (cic-stage3-covered-nf ObNil
     (dk-max (DKConst prop) (dk-type0)))
   (Err untracked-cic-rewrite-obligation))

!(assertEqual
   (cic-stage3-proof-check (cic-prop-to-type0-cumul-source))
   (Ok (CheckedPrf ANil
     (Lam (App (Con Univ) (Con prop))
       (Lam (App (App (Con Term) (Con prop)) (Var 0))
         (Var 0)))
     (Pi
       (App (Con Univ) (Con prop))
       (Pi (App (App (Con Term) (Con prop)) (Var 0))
         (App (App (Con Term) (Con prop)) (Var 1)))))))
!(assertEqual
   (cic-stage3-proof-check (cic-type0-to-type1-cumul-source))
   (Ok (CheckedPrf ANil
     (Lam (App (Con Univ) (App (Con type) (Con z)))
       (Lam (App (App (Con Term) (App (Con type) (Con z))) (Var 0))
         (Var 0)))
     (Pi
       (App (Con Univ) (App (Con type) (Con z)))
       (Pi (App (App (Con Term) (App (Con type) (Con z))) (Var 0))
         (App (App (Con Term) (App (Con type) (Con z))) (Var 1)))))))
!(assertEqual
   (cic-stage3-proof-check (cic-type1-to-type2-cumul-source))
   (Ok (CheckedPrf ANil
     (Lam (App (Con Univ) (App (Con type) (App (Con s) (Con z))))
       (Lam (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 0))
         (Var 0)))
     (Pi
       (App (Con Univ) (App (Con type) (App (Con s) (Con z))))
       (Pi (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 0))
         (App (App (Con Term) (App (Con type) (App (Con s) (Con z)))) (Var 1)))))))
!(assertEqual
   (cic-stage3-proof-check (cic-prop-to-type0-cumul-untracked-source))
   (Err untracked-cic-rewrite-obligation))
!(assertEqual
   (cic-stage3-proof-check (cic-type0-to-type1-cumul-bad-source))
   (Err check-failed))
!(assertEqual
   (cic-stage3-proof-check (cic-type1-to-type2-cumul-bad-source))
   (Err check-failed))
!(assertEqual (cic-stage3-proof-check bogus) (Err unknown-cic-proof-syntax))
