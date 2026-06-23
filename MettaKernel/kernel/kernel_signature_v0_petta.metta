; =============================================================================
; kernel_signature_v0_petta.metta
;
; A stricter GSLT-style kernel seed:
;   raw finite signatures -> admission check -> certificate checking.
;
; This is not the final foundation.  It is the signature/certificate discipline
; every final foundation needs: no ambient raw-term-type equations, no reusable
; theorem handles, definitions checked against declared types, duplicate names
; rejected, forward references rejected, and axioms tracked as provenance.
;
; Run:
;   cd /home/aimama/aihub/hyperon/PeTTa && ./run.sh /home/aimama/aihub/Mettapedia/MettaKernel/kernel/kernel_signature_v0_petta.metta --silent
; =============================================================================

!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; ---------- booleans and error discipline -----------------------------------
(= (and_b True  $y) $y)
(= (and_b False $y) False)
(= (is_bad $x) (unify $x (Bad $e) True False))

; ---------- lists for hypotheses and axiom provenance ------------------------
(= (hyp_remove $x HNil) HNil)
(= (hyp_remove $x (HCons $y $ys))
   (if (== $x $y) (hyp_remove $x $ys) (HCons $y (hyp_remove $x $ys))))

(= (hyp_union HNil $ys) $ys)
(= (hyp_union (HCons $x $xs) $ys) (HCons $x (hyp_union $xs $ys)))

(= (ax_union ANil $ys) $ys)
(= (ax_union (ACons $x $xs) $ys) (ACons $x (ax_union $xs $ys)))

; ---------- simple object types ---------------------------------------------
(= (wf_ty $T)
   (case $T
     ((bool True)
      (num True)
      (set True)
      (prop True)
      ((Arr $A $B) (if (wf_ty $A) (wf_ty $B) False))
      (Empty False))))

; ---------- finite raw signatures -------------------------------------------
; SNil | SCons Decl Rest
; Decl ::= DConst name ty | DDef name ty body | DAxiom name prop

(= (decl_name (DConst $n $T)) $n)
(= (decl_name (DDef $n $T $body)) $n)
(= (decl_name (DAxiom $n $prop)) $n)

(= (sig_has_name $n SNil) False)
(= (sig_has_name $n (SCons $d $rest))
   (if (== $n (decl_name $d)) True (sig_has_name $n $rest)))

(= (unique_sig SNil) True)
(= (unique_sig (SCons $d $rest))
   (if (sig_has_name (decl_name $d) $rest) False (unique_sig $rest)))

; Lookup only reads an already finite signature object.  No ambient global
; raw-term-type / sigT equations participate in kernel checking.
(= (term_type_of SNil $c) (Bad unknown_constant))
(= (term_type_of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (term_type_of $rest $x)))
(= (term_type_of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (term_type_of $rest $x)))
(= (term_type_of (SCons (DAxiom $ax $prop) $rest) $x)
   (term_type_of $rest $x))

(= (axiom_prop_of SNil $ax) (Bad unknown_axiom))
(= (axiom_prop_of (SCons (DAxiom $a $p) $rest) $x)
   (if (== $x $a) $p (axiom_prop_of $rest $x)))
(= (axiom_prop_of (SCons (DConst $c $T) $rest) $x)
   (axiom_prop_of $rest $x))
(= (axiom_prop_of (SCons (DDef $c $T $body) $rest) $x)
   (axiom_prop_of $rest $x))

; ---------- typing contexts and terms ---------------------------------------
(= (ctx_lookup $x TyEnvNil) (Bad unknown_var))
(= (ctx_lookup $x (TyEnvCons $y $T $rest))
   (if (== $x $y) $T (ctx_lookup $x $rest)))

(= (infer_tm $sig $ctx $t)
   (unify $t (Var $x)
     (ctx_lookup $x $ctx)
     (unify $t (Cst $c)
       (term_type_of $sig $c)
       (unify $t (Lam $x $A $body)
         (if (wf_ty $A)
             (let $B (infer_tm $sig (TyEnvCons $x $A $ctx) $body)
               (if (is_bad $B) (Bad lam_body_bad) (Arr $A $B)))
             (Bad lam_domain_not_type))
         (unify $t (App $f $a)
           (let $TF (infer_tm $sig $ctx $f)
             (unify $TF (Arr $A $B)
               (if (tm_check $sig $ctx $a $A) $B (Bad arg_type_mismatch))
               (Bad applied_non_function)))
           (Bad term_infer_failed))))))

(= (tm_check $sig $ctx $t $T)
   (if (wf_ty $T)
       (let $IT (infer_tm $sig $ctx $t)
         (if (is_bad $IT) False (== $IT $T)))
       False))

; ---------- proposition well-formedness --------------------------------------
(= (wf_prop $sig $ctx $p)
   (unify $p (Atom $name) True
     (unify $p (Imp $a $b)
       (if (wf_prop $sig $ctx $a) (wf_prop $sig $ctx $b) False)
       (unify $p (Eq $t $u)
         (let $TT (infer_tm $sig $ctx $t)
           (if (is_bad $TT) False (tm_check $sig $ctx $u $TT)))
         (unify $p (In $x $y)
           (if (tm_check $sig $ctx $x set) (tm_check $sig $ctx $y set) False)
           False)))))

; ---------- prefix admission -------------------------------------------------
; A declaration may mention only earlier declarations.  This gives a small,
; deterministic, PureKernel-like prefix discipline.
(= (wf_decl $prefix (DConst $n $T)) (wf_ty $T))
(= (wf_decl $prefix (DDef $n $T $body))
   (if (wf_ty $T) (tm_check $prefix TyEnvNil $body $T) False))
(= (wf_decl $prefix (DAxiom $n $prop)) (wf_prop $prefix TyEnvNil $prop))

(= (wf_sig_prefix $prefix SNil) True)
(= (wf_sig_prefix $prefix (SCons $d $rest))
   (if (wf_decl $prefix $d)
       (wf_sig_prefix (SCons $d $prefix) $rest)
       False))

(= (sig_admitted $sig)
   (if (unique_sig $sig) (wf_sig_prefix SNil $sig) False))

; ---------- substitution for beta certificates -------------------------------
; Named, intentionally small, and tested only for the closed entry-level beta
; examples below.  The final kernel should use de Bruijn/locally nameless terms.
(= (tm_subst $x $u $t)
   (unify $t (Var $y)
     (if (== $x $y) $u (Var $y))
     (unify $t (Cst $c)
       (Cst $c)
       (unify $t (App $f $a)
         (App (tm_subst $x $u $f) (tm_subst $x $u $a))
         (unify $t (Lam $y $T $b)
           (if (== $x $y) (Lam $y $T $b) (Lam $y $T (tm_subst $x $u $b)))
           $t)))))

; ---------- certificate checker ---------------------------------------------
; Cert ::= CRefl t | CAssume p | CUseAxiom ax | CDisch p cert
;        | CMP cert cert | CBeta redex | CTrans cert cert
;
; The only trusted API is (kernel_check sig cert).  CheckedThm values are
; printed outputs, not accepted as reusable trusted inputs.
(= (kernel_check $sig $cert)
   (if (sig_admitted $sig)
       (kernel_check_admitted $sig $cert)
       (Err signature_not_admitted)))

(= (kernel_check_admitted $sig $cert)
   (unify $cert (CRefl $t)
     (if (is_bad (infer_tm $sig TyEnvNil $t))
         (Err refl_ill_typed_term)
         (Ok (CheckedThm ANil (Seq HNil (Eq $t $t)))))
     (unify $cert (CAssume $p)
       (if (wf_prop $sig TyEnvNil $p)
           (Ok (CheckedThm ANil (Seq (HCons $p HNil) $p)))
           (Err assume_ill_formed_prop))
       (unify $cert (CUseAxiom $ax)
         (let $p (axiom_prop_of $sig $ax)
           (if (is_bad $p)
               (Err unknown_or_ill_formed_axiom)
               (Ok (CheckedThm (ACons $ax ANil) (Seq HNil $p)))))
         (unify $cert (CDisch $p $c)
           (let $R (kernel_check_admitted $sig $c)
             (unify $R (Ok (CheckedThm $uses (Seq $G $q)))
               (if (wf_prop $sig TyEnvNil $p)
                   (Ok (CheckedThm $uses (Seq (hyp_remove $p $G) (Imp $p $q))))
                   (Err disch_ill_formed_prop))
               $R))
           (unify $cert (CMP $c1 $c2)
             (let $R1 (kernel_check_admitted $sig $c1)
               (let $R2 (kernel_check_admitted $sig $c2)
                 (unify $R1 (Ok (CheckedThm $u1 (Seq $G1 (Imp $p $q))))
                   (unify $R2 (Ok (CheckedThm $u2 (Seq $G2 $p2)))
                     (if (== $p $p2)
                         (Ok (CheckedThm (ax_union $u1 $u2) (Seq (hyp_union $G1 $G2) $q)))
                         (Err mp_antecedent_mismatch))
                     $R2)
                   $R1)))
             (unify $cert (CBeta $t)
               (unify $t (App (Lam $x $T $b) $u)
                 (let $wholeT (infer_tm $sig TyEnvNil $t)
                   (if (is_bad $wholeT)
                       (Err beta_ill_typed)
                       (let $rhs (tm_subst $x $u $b)
                         (if (tm_check $sig TyEnvNil $rhs $wholeT)
                             (Ok (CheckedThm ANil (Seq HNil (Eq $t $rhs))))
                             (Err beta_rhs_ill_typed)))))
                 (Err beta_not_a_redex))
               (unify $cert (CTrans $c1 $c2)
                 (let $R1 (kernel_check_admitted $sig $c1)
                   (let $R2 (kernel_check_admitted $sig $c2)
                     (unify $R1 (Ok (CheckedThm $u1 (Seq $G1 (Eq $a $b))))
                       (unify $R2 (Ok (CheckedThm $u2 (Seq $G2 (Eq $b2 $c))))
                         (if (== $b $b2)
                             (Ok (CheckedThm (ax_union $u1 $u2) (Seq (hyp_union $G1 $G2) (Eq $a $c))))
                             (Err trans_middle_mismatch))
                         $R2)
                       $R1)))
                 (Err unknown_certificate)))))))))

; ---------- entry-level curriculum signatures --------------------------------
(= (good_sig)
   (SCons (DConst zero num)
   (SCons (DConst succ (Arr num num))
   (SCons (DConst a set)
   (SCons (DConst b set)
   (SCons (DDef idnum (Arr num num) (Lam x num (Var x)))
   (SCons (DAxiom axMem (In (Cst a) (Cst b)))
   (SCons (DAxiom axSym (Imp (In (Cst a) (Cst b)) (In (Cst b) (Cst a))))
   (SCons (DAxiom exFalso (Imp (Atom FalseP) (Atom AnyP)))
          SNil)))))))))

(= (bad_def_sig)
   (SCons (DConst zero num)
   (SCons (DDef badDef set (Cst zero))
          SNil)))

(= (dup_sig)
   (SCons (DConst flip num)
   (SCons (DConst flip set)
          SNil)))

(= (forward_ref_sig)
   (SCons (DDef useLater num (Cst later))
   (SCons (DConst later num)
          SNil)))

(= (inconsistent_ledger_sig)
   (SCons (DAxiom boom (Atom FalseP))
   (SCons (DAxiom exFalsoB (Imp (Atom FalseP) (Atom B)))
          SNil)))

; ---------- regression and entry-level curriculum checks ---------------------
!(test (sig_admitted (good_sig)) True)
!(test (sig_admitted (bad_def_sig)) False)
!(test (sig_admitted (dup_sig)) False)
!(test (sig_admitted (forward_ref_sig)) False)
!(test (sig_admitted (inconsistent_ledger_sig)) True)

; Coq/Lean/HOL entry: P -> P
!(test
   (kernel_check (good_sig) (CDisch (Atom P) (CAssume (Atom P))))
   (Ok (CheckedThm ANil (Seq HNil (Imp (Atom P) (Atom P))))))

; HOL entry: K combinator theorem, P -> Q -> P
!(test
   (kernel_check (good_sig)
     (CDisch (Atom P) (CDisch (Atom Q) (CAssume (Atom P)))))
   (Ok (CheckedThm ANil (Seq HNil (Imp (Atom P) (Imp (Atom Q) (Atom P)))))))

; Equality entry: zero = zero
!(test
   (kernel_check (good_sig) (CRefl (Cst zero)))
   (Ok (CheckedThm ANil (Seq HNil (Eq (Cst zero) (Cst zero))))))

; Beta entry: ((lambda x:num. x) zero) = zero
!(test
   (kernel_check (good_sig) (CBeta (App (Lam x num (Var x)) (Cst zero))))
   (Ok (CheckedThm ANil (Seq HNil (Eq (App (Lam x num (Var x)) (Cst zero)) (Cst zero))))))

; HOTG/Megalodon entry: axSym axMem proves In b a, with provenance.
!(test
   (kernel_check (good_sig) (CMP (CUseAxiom axSym) (CUseAxiom axMem)))
   (Ok (CheckedThm (ACons axSym (ACons axMem ANil)) (Seq HNil (In (Cst b) (Cst a))))))

; Negative: invalid MP is rejected.
!(test
   (kernel_check (good_sig) (CMP (CUseAxiom axSym) (CAssume (Atom R))))
   (Err mp_antecedent_mismatch))

; Negative: a theorem-shaped literal is not a certificate.
!(test
   (kernel_check (good_sig) (CheckedThm ANil (Seq HNil (Atom forged))))
   (Err unknown_certificate))

; Inconsistent axioms are admitted only as explicit ledgered assumptions.
!(test
   (kernel_check (inconsistent_ledger_sig) (CMP (CUseAxiom exFalsoB) (CUseAxiom boom)))
   (Ok (CheckedThm (ACons exFalsoB (ACons boom ANil)) (Seq HNil (Atom B)))))

; ---------- WM-PLN / evidence-mode bridge -----------------------------------
; Classical kernel checking stays crisp.  A checked certificate can be projected
; into WM-PLN evidence with maximal truth; WM-PLN evidence is NOT a certificate
; and cannot be fed back into kernel_check to mint theorems.
(= (cert_to_wm_evidence $sig $cert)
   (let $R (kernel_check $sig $cert)
     (unify $R (Ok (CheckedThm $uses $seq))
       (Ok (WMEvidence (TV 1 1) (KernelChecked $uses) $seq))
       $R)))

; A tiny symbolic graded inference example: modus ponens in the evidence mode.
; It produces a WM claim, not a kernel theorem.
(= (wm_mp
     (WMEvidence $tv1 $src1 (Seq HNil (Imp $p $q)))
     (WMEvidence $tv2 $src2 (Seq HNil $p)))
   (WMEvidence (TVAnd $tv1 $tv2) (PLNMP $src1 $src2) (WMClaim $q)))

!(test
   (cert_to_wm_evidence (good_sig) (CDisch (Atom P) (CAssume (Atom P))))
   (Ok (WMEvidence (TV 1 1) (KernelChecked ANil)
        (Seq HNil (Imp (Atom P) (Atom P))))))

!(test
   (kernel_check (good_sig)
     (WMEvidence (TV 1 1) (KernelChecked ANil) (Seq HNil (Atom P))))
   (Err unknown_certificate))

!(test
   (cert_to_wm_evidence (good_sig) (CheckedThm ANil (Seq HNil (Atom forged))))
   (Err unknown_certificate))

!(test
   (wm_mp
     (WMEvidence (TV 0.8 0.9) observed (Seq HNil (Imp (Atom P) (Atom Q))))
     (WMEvidence (TV 0.7 0.8) observed (Seq HNil (Atom P))))
   (WMEvidence (TVAnd (TV 0.8 0.9) (TV 0.7 0.8))
     (PLNMP observed observed)
     (WMClaim (Atom Q))))

!(kernel_check (good_sig) (CDisch (Atom P) (CAssume (Atom P))))
!(kernel_check (good_sig) (CMP (CUseAxiom axSym) (CUseAxiom axMem)))
!(kernel_check (inconsistent_ledger_sig) (CMP (CUseAxiom exFalsoB) (CUseAxiom boom)))
