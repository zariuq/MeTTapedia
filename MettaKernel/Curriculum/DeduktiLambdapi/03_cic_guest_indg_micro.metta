; ============================================================================
; Dedukti cic.dk Stage-2 guest micro.
;
; Source:
;   /home/aimama/aihub/repos/dedukti/libraries/theories/cic.dk
;
; This file keeps inductive machinery inside the existing DIndG kernel engine.
; The new work here is only guest-side CIC witness data plus lowering into the
; kernel's generic IndG form, followed by real in-kernel re-checking.
;
; Current shape: the external witness terms are explicit data under
; `cic-stage2-source-term` / `cic-stage2-source-type`, and the covered DK
; fragment lowers structurally into the kernel's generic IndG form. Broader
; cic.dk / Lean-core guest lowering remains future work.
; ============================================================================

!(import! &self ../../kernel/kernel_signature_lf_indexed_lib_v0.metta)
!(import! &self ../../kernel/kernel_binding_decl_v1.metta)

; ---------- guest witness data -----------------------------------------------

(= (dk-idnat-src $a $b)
   (DKApp (DKApp (DKApp (DKConst Id) (DKConst nat)) $a) $b))
(= (dk-rflnat-src $a)
   (DKApp (DKApp (DKConst refl) (DKConst nat)) $a))
(= (dk-plus-src $a $b)
   (DKApp (DKApp (DKDef plus) $a) $b))

(= (cic-stage2-source-term nat-id)
   (DKIndG nat DKArgsNil
     (DKLam n (DKConst nat) (DKConst nat))
     (DKCases (DKCase z (DKConst z))
       (DKCases (DKCase s
         (DKLam n (DKConst nat)
           (DKLam ih (DKConst nat)
             (DKApp (DKConst s) (DKVar 0))))) DKCasesNil))
     DKArgsNil
     (DKApp (DKConst s) (DKConst z))))

(= (cic-stage2-source-type nat-id)
   (DKConst nat))

(= (cic-stage2-source-term id-j)
   (DKIndG Id
     (DKArgsCons (DKConst nat) (DKArgsCons (DKConst z) DKArgsNil))
     (DKLam y (DKConst nat)
       (DKLam p (dk-idnat-src (DKConst z) (DKVar 0))
         (DKConst nat)))
     (DKCases (DKCase refl (DKConst z)) DKCasesNil)
     (DKArgsCons (DKConst z) DKArgsNil)
     (dk-rflnat-src (DKConst z))))

(= (cic-stage2-source-type id-j)
   (DKConst nat))

(= (cic-stage2-source-term cong-s-generated-j)
   (DKLam a (DKConst nat)
     (DKLam b (DKConst nat)
       (DKLam p (dk-idnat-src (DKVar 1) (DKVar 0))
         (DKIndG Id
           (DKArgsCons (DKConst nat) (DKArgsCons (DKVar 2) DKArgsNil))
           (DKLam y (DKConst nat)
             (DKLam q (dk-idnat-src (DKVar 3) (DKVar 0))
               (dk-idnat-src
                 (DKApp (DKConst s) (DKVar 4))
                 (DKApp (DKConst s) (DKVar 1)))))
           (DKCases
             (DKCase refl (dk-rflnat-src (DKApp (DKConst s) (DKVar 2))))
             DKCasesNil)
           (DKArgsCons (DKVar 1) DKArgsNil)
           (DKVar 0))))))

(= (cic-stage2-source-type cong-s-generated-j)
   (DKPi a (DKConst nat)
     (DKPi b (DKConst nat)
       (DKPi p (dk-idnat-src (DKVar 1) (DKVar 0))
         (dk-idnat-src
           (DKApp (DKConst s) (DKVar 2))
           (DKApp (DKConst s) (DKVar 1)))))))

(= (cic-stage2-source-term plus-O-r)
   (DKLam n (DKConst nat)
     (DKIndG nat DKArgsNil
       (DKLam k (DKConst nat)
         (dk-idnat-src (dk-plus-src (DKVar 0) (DKConst z)) (DKVar 0)))
       (DKCases (DKCase z (dk-rflnat-src (DKConst z)))
         (DKCases (DKCase s
           (DKLam n (DKConst nat)
             (DKLam ih (dk-idnat-src (dk-plus-src (DKVar 0) (DKConst z)) (DKVar 0))
               (DKApp
                 (DKApp
                   (DKApp (cic-stage2-source-term cong-s-generated-j)
                     (dk-plus-src (DKVar 1) (DKConst z)))
                   (DKVar 1))
                 (DKVar 0))))) DKCasesNil))
       DKArgsNil
       (DKVar 0))))

(= (cic-stage2-source-type plus-O-r)
   (DKPi n (DKConst nat)
     (dk-idnat-src (dk-plus-src (DKVar 0) (DKConst z)) (DKVar 0))))

(= (cic-stage2-source-type plus-O-r-bad)
   (DKPi n (DKConst nat)
     (dk-idnat-src
       (dk-plus-src (DKVar 0) (DKConst z))
       (DKApp (DKConst s) (DKVar 0)))))

; ---------- local DIndG-hosted kernel data ----------------------------------

(= (cic-stage2-good-sig)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG Id (TCons (Srt type) (TCons (Var 0) TNil)) (TCons (Var 1) TNil)
            (GCtors (GCtor refl TNil (ArgsCons (Var 0) ArgsNil)) GCNil))
          SNil)))

(= (cic-stage2-IdNat $a $b)
   (App (App (App (Con Id) (Con nat)) $a) $b))
(= (cic-stage2-RflNat $a)
   (App (App (Con refl) (Con nat)) $a))

(= (cic-stage2-plus-sig)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG Id (TCons (Srt type) (TCons (Var 0) TNil)) (TCons (Var 1) TNil)
            (GCtors (GCtor refl TNil (ArgsCons (Var 0) ArgsNil)) GCNil))
   (SCons (DDef plus (Pi (Con nat) (Pi (Con nat) (Con nat)))
            (Lam (Con nat) (Lam (Con nat)
              (IndG nat ArgsNil (Lam (Con nat) (Con nat))
                (Cases (Case z (Var 0))
                  (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
                ArgsNil (Var 1)))))
          SNil))))

(= (cic-stage2-nat-id-term)
   (IndG nat ArgsNil
     (Lam (Con nat) (Con nat))
     (Cases (Case z (Con z))
       (Cases (Case s
         (Lam (Con nat)
           (Lam (Con nat)
             (App (Con s) (Var 0))))) CasesNil))
     ArgsNil
     (App (Con s) (Con z))))

(= (cic-stage2-id-j-term)
   (IndG Id
     (ArgsCons (Con nat) (ArgsCons (Con z) ArgsNil))
     (Lam (Con nat)
       (Lam (cic-stage2-IdNat (Con z) (Var 0))
         (Con nat)))
     (Cases (Case refl (Con z)) CasesNil)
     (ArgsCons (Con z) ArgsNil)
     (cic-stage2-RflNat (Con z))))

(= (cic-stage2-cong-s-generated-j-type)
   (Pi (Con nat)
     (Pi (Con nat)
       (Pi (cic-stage2-IdNat (Var 1) (Var 0))
         (cic-stage2-IdNat
           (App (Con s) (Var 2))
           (App (Con s) (Var 1)))))))

(= (cic-stage2-cong-s-generated-j-term)
   (Lam (Con nat)
     (Lam (Con nat)
       (Lam (cic-stage2-IdNat (Var 1) (Var 0))
         (IndG Id
           (ArgsCons (Con nat) (ArgsCons (Var 2) ArgsNil))
           (Lam (Con nat)
             (Lam (cic-stage2-IdNat (Var 3) (Var 0))
               (cic-stage2-IdNat
                 (App (Con s) (Var 4))
                 (App (Con s) (Var 1)))))
           (Cases
             (Case refl (cic-stage2-RflNat (App (Con s) (Var 2))))
             CasesNil)
           (ArgsCons (Var 1) ArgsNil)
           (Var 0))))))

(= (cic-stage2-plus-O-r-type)
   (Pi (Con nat)
     (cic-stage2-IdNat
       (App (App (Def plus) (Var 0)) (Con z))
       (Var 0))))

(= (cic-stage2-plus-O-r-term)
   (Lam (Con nat)
     (IndG nat ArgsNil
       (Lam (Con nat)
         (cic-stage2-IdNat
           (App (App (Def plus) (Var 0)) (Con z))
           (Var 0)))
       (Cases (Case z (cic-stage2-RflNat (Con z)))
         (Cases (Case s
           (Lam (Con nat)
             (Lam (cic-stage2-IdNat
                    (App (App (Def plus) (Var 0)) (Con z))
                    (Var 0))
               (App
                 (App
                   (App (cic-stage2-cong-s-generated-j-term)
                     (App (App (Def plus) (Var 1)) (Con z)))
                   (Var 1))
                 (Var 0))))) CasesNil))
       ArgsNil
       (Var 0))))

; ---------- structural lowering for the covered DK fragment ------------------

(= (dk-stage2-lower (DKType)) (Srt type))
(= (dk-stage2-lower (DKVar $i)) (Var $i))
(= (dk-stage2-lower (DKConst $c)) (Con $c))
(= (dk-stage2-lower (DKDef $x)) (Def $x))
(= (dk-stage2-lower (DKApp $f $a)) (App (dk-stage2-lower $f) (dk-stage2-lower $a)))
(= (dk-stage2-lower (DKPi $name $A $B)) (Pi (dk-stage2-lower $A) (dk-stage2-lower $B)))
(= (dk-stage2-lower (DKLam $name $A $body))
   (dk-stage2-lower-lam-with-decl (dk-stage2-lambda-decl) $A $body))
(= (dk-stage2-lower (DKIndG $fam $params $motive $cases $indices $scrutinee))
   (IndG $fam
     (dk-stage2-lower-args $params)
     (dk-stage2-lower $motive)
     (dk-stage2-lower-cases $cases)
     (dk-stage2-lower-args $indices)
     (dk-stage2-lower $scrutinee)))

(= (dk-stage2-lambda-decl) (Bind1 body))
(= (dk-stage2-lower-lam-with-decl $decl $A $body)
   (if (== (binding-decl-depth $decl body) 1)
     (Lam (dk-stage2-lower $A) (dk-stage2-lower $body))
     (Bad bad-dk-lambda-binding-decl)))

(= (dk-stage2-lower-args DKArgsNil) ArgsNil)
(= (dk-stage2-lower-args (DKArgsCons $arg $rest))
   (ArgsCons (dk-stage2-lower $arg) (dk-stage2-lower-args $rest)))

(= (dk-stage2-lower-cases DKCasesNil) CasesNil)
(= (dk-stage2-lower-cases (DKCases (DKCase $cn $body) $rest))
   (Cases (Case $cn (dk-stage2-lower $body)) (dk-stage2-lower-cases $rest)))

(= (cic-stage2-lower-term $name)
   (dk-stage2-lower (cic-stage2-source-term $name)))

(= (cic-stage2-lower-type $name)
   (dk-stage2-lower (cic-stage2-source-type $name)))

; ---------- checks -----------------------------------------------------------

!(assertEqual (sig-admitted (cic-stage2-good-sig)) True)
!(assertEqual (sig-admitted (cic-stage2-plus-sig)) True)

!(assertEqual (cic-stage2-lower-term nat-id) (cic-stage2-nat-id-term))
!(assertEqual (cic-stage2-lower-term id-j) (cic-stage2-id-j-term))
!(assertEqual
   (cic-stage2-lower-term cong-s-generated-j)
   (cic-stage2-cong-s-generated-j-term))
!(assertEqual (cic-stage2-lower-term plus-O-r) (cic-stage2-plus-O-r-term))

!(assertEqual (cic-stage2-lower-type nat-id) (Con nat))
!(assertEqual (cic-stage2-lower-type id-j) (Con nat))
!(assertEqual
   (cic-stage2-lower-type cong-s-generated-j)
   (cic-stage2-cong-s-generated-j-type))
!(assertEqual (cic-stage2-lower-type plus-O-r) (cic-stage2-plus-O-r-type))
!(assertEqual
   (cic-stage2-lower-type plus-O-r-bad)
   (Pi (Con nat)
     (cic-stage2-IdNat
       (App (App (Def plus) (Var 0)) (Con z))
       (App (Con s) (Var 0)))))

!(assertEqual
   (kernel-check (cic-stage2-plus-sig) (cic-stage2-lower-term nat-id) (cic-stage2-lower-type nat-id))
   (Ok (CheckedPrf ANil (cic-stage2-nat-id-term) (Con nat))))
!(assertEqual
   (conv (cic-stage2-plus-sig) (cic-stage2-lower-term nat-id) (App (Con s) (Con z)))
   True)

!(assertEqual
   (kernel-check (cic-stage2-plus-sig) (cic-stage2-lower-term id-j) (cic-stage2-lower-type id-j))
   (Ok (CheckedPrf ANil (cic-stage2-id-j-term) (Con nat))))
!(assertEqual
   (conv (cic-stage2-plus-sig) (cic-stage2-lower-term id-j) (Con z))
   True)

!(assertEqual
   (kernel-check
     (cic-stage2-plus-sig)
     (cic-stage2-lower-term cong-s-generated-j)
     (cic-stage2-lower-type cong-s-generated-j))
   (Ok (CheckedPrf ANil (cic-stage2-cong-s-generated-j-term) (cic-stage2-cong-s-generated-j-type))))

!(assertEqual
   (kernel-check
     (cic-stage2-plus-sig)
     (cic-stage2-lower-term plus-O-r)
     (cic-stage2-lower-type plus-O-r))
   (Ok (CheckedPrf ANil (cic-stage2-plus-O-r-term) (cic-stage2-plus-O-r-type))))
!(assertEqual
   (kernel-check
     (cic-stage2-plus-sig)
     (cic-stage2-lower-term plus-O-r)
     (cic-stage2-lower-type plus-O-r-bad))
   (Err check-failed))
