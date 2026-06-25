; ============================================================================
; Dedukti-as-guest micro-coverage v1.
;
; Sources:
;   /home/aimama/aihub/repos/dedukti/examples/plus.dk
;   /home/aimama/aihub/repos/dedukti/examples/FO.dk
;   /home/aimama/aihub/repos/dedukti/examples/FO_theorems.dk  (context only)
;
; This file hosts a tiny .dk-shaped guest fragment in MIK.  It is not a port of
; Dedukti and not a replacement checker.  The guest syntax is data; covered
; proof terms lower into the existing lambda-Pi kernel, while rewrite rules
; carry explicit obligation footprints.
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
(= (dk-shift-lam-body $t) (binding-shift-under-depth 1 0 (dk-lambda-body-depth) $t))

; ---------- FO.dk proof-as-inhabitation micro-host ---------------------------
; Source line in FO.dk:
;   tt: prf true.

(= (dk-prf $P) (App (Con prf) $P))
(= (dk-fo-sig)
   (SCons (DConst Prop (Srt type))
   (SCons (DConst prf (Pi (Con Prop) (Srt type)))
   (SCons (DConst true (Con Prop))
   (SCons (DConst false (Con Prop))
   (SCons (DConst tt (dk-prf (Con true)))
          SNil))))))

(= (dk-tt-true-source) (DKProof (DKConst tt) (DKApp (DKConst prf) (DKConst true))))
(= (dk-tt-false-source) (DKProof (DKConst tt) (DKApp (DKConst prf) (DKConst false))))
(= (dk-proof-term (DKProof $term $type)) $term)
(= (dk-proof-type (DKProof $term $type)) $type)
(= (dk-proof-check-parsed (Ok $proof))
   (kernel-check (dk-fo-sig) (dk-lower (dk-proof-term $proof)) (dk-lower (dk-proof-type $proof))))
(= (dk-proof-check-parsed (Err $e)) (Err $e))
(= (dk-prs-proof $x)
   (if (== $x (dk-tt-true-source)) (Ok (dk-tt-true-source))
   (if (== $x (dk-tt-false-source)) (Ok (dk-tt-false-source))
       (Err unknown-dk-proof-syntax))))
(= (dk-proof-check $x) (dk-proof-check-parsed (dk-prs-proof $x)))

(= (dk-fo-proof-jobs)
   (Cons (Accept (Con tt) (dk-prf (Con true)))
   (Cons (Reject (Con tt) (dk-prf (Con false)))
         Nil)))
(= (dk-fo-proof-inhabitation-check)
   (kernel-check-batch-judgments (dk-fo-sig) (dk-fo-proof-jobs)))

; ---------- plus.dk rewrite micro-host --------------------------------------
; Source lines in plus.dk:
;   [m]   plus Z (S m) --> S m
;   [n]   plus n Z --> n
;   [n,m] plus (S n) (S m) --> S (S m).
;
; The rewrite rules are represented as guest data with an explicit obligation
; footprint.  v1 does not prove confluence/termination; a covered rewrite check
; must carry the footprint or reject.

(= (dk-plus-source-rewrites)
   (DKRewriteSet
     (ObCons rew-plus-Z-S
       (ObCons rew-plus-n-Z
         (ObCons rew-plus-S-S ObNil)))
     (Cons (DKRewrite (Cons m Nil)
             (DKApp (DKApp (DKConst plus) (DKConst Z)) (DKApp (DKConst S) (DKVar 0)))
             (DKApp (DKConst S) (DKVar 0)))
     (Cons (DKRewrite (Cons n Nil)
             (DKApp (DKApp (DKConst plus) (DKVar 0)) (DKConst Z))
             (DKVar 0))
     (Cons (DKRewrite (Cons n (Cons m Nil))
             (DKApp
               (DKApp (DKConst plus) (DKApp (DKConst S) (DKVar 1)))
               (DKApp (DKConst S) (DKVar 0)))
             (DKApp (DKConst S) (DKApp (DKConst S) (DKVar 0))))
           Nil)))))

(= (dk-plus-required-obligations)
   (ObCons rew-plus-Z-S
     (ObCons rew-plus-n-Z
       (ObCons rew-plus-S-S ObNil))))
(= (dk-rewrite-footprint (DKRewriteSet $obs $rules)) $obs)
(= (dk-rewrite-rules (DKRewriteSet $obs $rules)) $rules)
(= (dk-rewrite-obligations-ok $rewrites)
   (== (dk-rewrite-footprint $rewrites) (dk-plus-required-obligations)))

(= (dk-read-nat (DKConst Z)) dkZ)
(= (dk-read-nat (DKApp (DKConst S) $n)) (dkS (dk-read-nat $n)))
(= (dk-read-nat (DKApp (DKApp (DKConst plus) $a) $b))
   (dkPlus (dk-read-nat $a) (dk-read-nat $b)))

(= (dk-plus-Z-SZ-source)
   (DKApp (DKApp (DKConst plus) (DKConst Z))
     (DKApp (DKConst S) (DKConst Z))))
(= (dk-plus-SZ-Z-source)
   (DKApp (DKApp (DKConst plus) (DKApp (DKConst S) (DKConst Z)))
     (DKConst Z)))
(= (dk-plus-SZ-SZ-source)
   (DKApp (DKApp (DKConst plus) (DKApp (DKConst S) (DKConst Z)))
     (DKApp (DKConst S) (DKConst Z))))

(= (dk-nf $rewrites dkZ) dkZ)
(= (dk-nf $rewrites (dkS $n)) (dkS (dk-nf $rewrites $n)))
(= (dk-nf $rewrites (dkPlus $a $b)) (dk-plus-rewrite $rewrites $a $b))
(= (dk-plus-rewrite $rewrites $a $b)
   (unify $a dkZ
     (unify $b (dkS $m)
       (dk-nf $rewrites (dkS $m))
       (unify $b dkZ (dk-nf $rewrites dkZ) (Bad dk-plus-no-rule)))
     (unify $b dkZ
       (dk-nf $rewrites $a)
       (unify $a (dkS $n)
         (unify $b (dkS $m)
           (dk-nf $rewrites (dkS (dkS $m)))
           (Bad dk-plus-no-rule))
         (Bad dk-plus-no-rule)))))

(= (dk-lower-nat dkZ) (Con Z))
(= (dk-lower-nat (dkS $n)) (App (Con S) (dk-lower-nat $n)))
(= (dk-lower-nat (Bad $e)) (Bad $e))

(= (dk-nat-eq $x $y) (App (App (Con eqn) $x) $y))
(= (dk-nat-sig)
   (SCons (DConst nat (Srt type))
   (SCons (DConst Z (Con nat))
   (SCons (DConst S (Pi (Con nat) (Con nat)))
   (SCons (DConst eqn (Pi (Con nat) (Pi (Con nat) (Srt type))))
   (SCons (DConst rfl (Pi (Con nat) (dk-nat-eq (Var 0) (Var 0))))
          SNil))))))

(= (dk-plus-eq-covered $rewrites $lhs $rhs)
   (if (dk-rewrite-obligations-ok $rewrites)
     (let $lnf (dk-nf $rewrites (dk-read-nat $lhs))
       (let $rnf (dk-nf $rewrites (dk-read-nat $rhs))
         (kernel-check-batch-judgments
           (dk-nat-sig)
           (Cons
             (Accept
               (App (Con rfl) (dk-lower-nat $lnf))
               (dk-nat-eq (dk-lower-nat $lnf) (dk-lower-nat $rnf)))
             Nil))))
     (Err untracked-rewrite-obligation)))

(= (dk-plus-good-check)
   (if (dk-plus-eq-covered (dk-plus-source-rewrites) (dk-plus-Z-SZ-source) (DKApp (DKConst S) (DKConst Z)))
     (if (dk-plus-eq-covered (dk-plus-source-rewrites) (dk-plus-SZ-Z-source) (DKApp (DKConst S) (DKConst Z)))
       (dk-plus-eq-covered
         (dk-plus-source-rewrites)
         (dk-plus-SZ-SZ-source)
         (DKApp (DKConst S) (DKApp (DKConst S) (DKConst Z))))
       False)
     False))

; ---------- checks -----------------------------------------------------------

!(assertEqual (dk-lower (DKConst Prop)) (Con Prop))
!(assertEqual (dk-lower (DKApp (DKConst prf) (DKConst true))) (dk-prf (Con true)))
!(assertEqual (dk-lower (DKPi x (DKConst Prop) (DKConst Prop))) (Pi (Con Prop) (Con Prop)))
!(assertEqual (dk-lower (DKLam x (DKConst Prop) (DKVar 0))) (Lam (Con Prop) (Var 0)))
!(assertEqual (dk-lower-lam-with-decl Bind0 (DKConst Prop) (DKVar 0)) (Bad bad-dk-lambda-binding-decl))
!(assertEqual (dk-shift-lam-body (Var 0)) (Var 0))
!(assertEqual (dk-shift-lam-body (Var 1)) (Var 2))

!(assertEqual (dk-fo-proof-inhabitation-check) True)
!(assertEqual
  (dk-proof-check (dk-tt-true-source))
  (Ok (CheckedPrf ANil (Con tt) (dk-prf (Con true)))))
!(assertEqual (dk-proof-check (dk-tt-false-source)) (Err check-failed))
!(assertEqual (dk-proof-check (DKProof bogus bogus)) (Err unknown-dk-proof-syntax))

!(assertEqual (dk-rewrite-obligations-ok (dk-plus-source-rewrites)) True)
!(assertEqual (dk-rewrite-rules (dk-plus-source-rewrites)) (dk-rewrite-rules (dk-plus-source-rewrites)))
!(assertEqual (dk-read-nat (dk-plus-SZ-SZ-source)) (dkPlus (dkS dkZ) (dkS dkZ)))
!(assertEqual (dk-nf (dk-plus-source-rewrites) (dk-read-nat (dk-plus-Z-SZ-source))) (dkS dkZ))
!(assertEqual (dk-nf (dk-plus-source-rewrites) (dk-read-nat (dk-plus-SZ-Z-source))) (dkS dkZ))
!(assertEqual (dk-nf (dk-plus-source-rewrites) (dk-read-nat (dk-plus-SZ-SZ-source))) (dkS (dkS dkZ)))
!(assertEqual (dk-plus-good-check) True)
!(assertEqual
  (dk-plus-eq-covered
    (DKRewriteSet ObNil (dk-rewrite-rules (dk-plus-source-rewrites)))
    (dk-plus-Z-SZ-source)
    (DKApp (DKConst S) (DKConst Z)))
  (Err untracked-rewrite-obligation))
