; =============================================================================
; kernel_signature_v0.metta
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
;   /home/aimama/aihub/hyperon/CeTTa/cetta kernel_signature_v0.metta
; =============================================================================

; ---------- booleans and error discipline -----------------------------------
(= (and-b True  $y) $y)
(= (and-b False $y) False)
(= (is-bad $x) (unify $x (Bad $e) True False))

; ---------- lists for hypotheses and axiom provenance ------------------------
(= (hyp-remove $x HNil) HNil)
(= (hyp-remove $x (HCons $y $ys))
   (if (== $x $y) (hyp-remove $x $ys) (HCons $y (hyp-remove $x $ys))))

(= (hyp-union HNil $ys) $ys)
(= (hyp-union (HCons $x $xs) $ys) (HCons $x (hyp-union $xs $ys)))

(= (ax-union ANil $ys) $ys)
(= (ax-union (ACons $x $xs) $ys) (ACons $x (ax-union $xs $ys)))

; ---------- simple object types ---------------------------------------------
(= (wf-ty $T)
   (unify $T bool True
     (unify $T num True
       (unify $T set True
         (unify $T prop True
           (unify $T (Arr $A $B)
             (if (wf-ty $A) (wf-ty $B) False)
             False))))))

; ---------- finite raw signatures -------------------------------------------
; SNil | SCons Decl Rest
; Decl ::= DConst name ty | DDef name ty body | DAxiom name prop

(= (decl-name (DConst $n $T)) $n)
(= (decl-name (DDef $n $T $body)) $n)
(= (decl-name (DAxiom $n $prop)) $n)

(= (sig-has-name $n SNil) False)
(= (sig-has-name $n (SCons $d $rest))
   (if (== $n (decl-name $d)) True (sig-has-name $n $rest)))

(= (unique-sig SNil) True)
(= (unique-sig (SCons $d $rest))
   (if (sig-has-name (decl-name $d) $rest) False (unique-sig $rest)))

; Lookup only reads an already finite signature object.  No ambient global
; raw-term-type / sigT equations participate in kernel checking.
(= (term-type-of SNil $c) (Bad unknown-constant))
(= (term-type-of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (term-type-of $rest $x)))
(= (term-type-of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (term-type-of $rest $x)))
(= (term-type-of (SCons (DAxiom $ax $prop) $rest) $x)
   (term-type-of $rest $x))

(= (axiom-prop-of SNil $ax) (Bad unknown-axiom))
(= (axiom-prop-of (SCons (DAxiom $a $p) $rest) $x)
   (if (== $x $a) $p (axiom-prop-of $rest $x)))
(= (axiom-prop-of (SCons (DConst $c $T) $rest) $x)
   (axiom-prop-of $rest $x))
(= (axiom-prop-of (SCons (DDef $c $T $body) $rest) $x)
   (axiom-prop-of $rest $x))

; ---------- typing contexts and terms ---------------------------------------
(= (ctx-lookup $x TyEnvNil) (Bad unknown-var))
(= (ctx-lookup $x (TyEnvCons $y $T $rest))
   (if (== $x $y) $T (ctx-lookup $x $rest)))

(= (infer-tm $sig $ctx $t)
   (unify $t (Var $x)
     (ctx-lookup $x $ctx)
     (unify $t (Cst $c)
       (term-type-of $sig $c)
       (unify $t (Lam $x $A $body)
         (if (wf-ty $A)
             (let $B (infer-tm $sig (TyEnvCons $x $A $ctx) $body)
               (if (is-bad $B) (Bad lam-body-bad) (Arr $A $B)))
             (Bad lam-domain-not-type))
         (unify $t (App $f $a)
           (let $TF (infer-tm $sig $ctx $f)
             (unify $TF (Arr $A $B)
               (if (tm-check $sig $ctx $a $A) $B (Bad arg-type-mismatch))
               (Bad applied-non-function)))
           (Bad term-infer-failed))))))

(= (tm-check $sig $ctx $t $T)
   (if (wf-ty $T)
       (let $IT (infer-tm $sig $ctx $t)
         (if (is-bad $IT) False (== $IT $T)))
       False))

; ---------- proposition well-formedness --------------------------------------
(= (wf-prop $sig $ctx $p)
   (unify $p (Atom $name) True
     (unify $p (Imp $a $b)
       (if (wf-prop $sig $ctx $a) (wf-prop $sig $ctx $b) False)
       (unify $p (Eq $t $u)
         (let $TT (infer-tm $sig $ctx $t)
           (if (is-bad $TT) False (tm-check $sig $ctx $u $TT)))
         (unify $p (In $x $y)
           (if (tm-check $sig $ctx $x set) (tm-check $sig $ctx $y set) False)
           False)))))

; ---------- prefix admission -------------------------------------------------
; A declaration may mention only earlier declarations.  This gives a small,
; deterministic, PureKernel-like prefix discipline.
(= (wf-decl $prefix (DConst $n $T)) (wf-ty $T))
(= (wf-decl $prefix (DDef $n $T $body))
   (if (wf-ty $T) (tm-check $prefix TyEnvNil $body $T) False))
(= (wf-decl $prefix (DAxiom $n $prop)) (wf-prop $prefix TyEnvNil $prop))

(= (wf-sig-prefix $prefix SNil) True)
(= (wf-sig-prefix $prefix (SCons $d $rest))
   (if (wf-decl $prefix $d)
       (wf-sig-prefix (SCons $d $prefix) $rest)
       False))

(= (sig-admitted $sig)
   (if (unique-sig $sig) (wf-sig-prefix SNil $sig) False))

; ---------- substitution for beta certificates -------------------------------
; Named, intentionally small, and tested only for the closed entry-level beta
; examples below.  The final kernel should use de Bruijn/locally nameless terms.
(= (tm-subst $x $u $t)
   (unify $t (Var $y)
     (if (== $x $y) $u (Var $y))
     (unify $t (Cst $c)
       (Cst $c)
       (unify $t (App $f $a)
         (App (tm-subst $x $u $f) (tm-subst $x $u $a))
         (unify $t (Lam $y $T $b)
           (if (== $x $y) (Lam $y $T $b) (Lam $y $T (tm-subst $x $u $b)))
           $t)))))

; ---------- certificate checker ---------------------------------------------
; Cert ::= CRefl t | CAssume p | CUseAxiom ax | CDisch p cert
;        | CMP cert cert | CBeta redex | CTrans cert cert
;
; The only trusted API is (kernel-check sig cert).  CheckedThm values are
; printed outputs, not accepted as reusable trusted inputs.
(= (kernel-check $sig $cert)
   (if (sig-admitted $sig)
       (kernel-check-admitted $sig $cert)
       (Err signature-not-admitted)))

(= (kernel-check-admitted $sig $cert)
   (unify $cert (CRefl $t)
     (if (is-bad (infer-tm $sig TyEnvNil $t))
         (Err refl-ill-typed-term)
         (Ok (CheckedThm ANil (Seq HNil (Eq $t $t)))))
     (unify $cert (CAssume $p)
       (if (wf-prop $sig TyEnvNil $p)
           (Ok (CheckedThm ANil (Seq (HCons $p HNil) $p)))
           (Err assume-ill-formed-prop))
       (unify $cert (CUseAxiom $ax)
         (let $p (axiom-prop-of $sig $ax)
           (if (is-bad $p)
               (Err unknown-or-ill-formed-axiom)
               (Ok (CheckedThm (ACons $ax ANil) (Seq HNil $p)))))
         (unify $cert (CDisch $p $c)
           (let $R (kernel-check-admitted $sig $c)
             (unify $R (Ok (CheckedThm $uses (Seq $G $q)))
               (if (wf-prop $sig TyEnvNil $p)
                   (Ok (CheckedThm $uses (Seq (hyp-remove $p $G) (Imp $p $q))))
                   (Err disch-ill-formed-prop))
               $R))
           (unify $cert (CMP $c1 $c2)
             (let $R1 (kernel-check-admitted $sig $c1)
               (let $R2 (kernel-check-admitted $sig $c2)
                 (unify $R1 (Ok (CheckedThm $u1 (Seq $G1 (Imp $p $q))))
                   (unify $R2 (Ok (CheckedThm $u2 (Seq $G2 $p2)))
                     (if (== $p $p2)
                         (Ok (CheckedThm (ax-union $u1 $u2) (Seq (hyp-union $G1 $G2) $q)))
                         (Err mp-antecedent-mismatch))
                     $R2)
                   $R1)))
             (unify $cert (CBeta $t)
               (unify $t (App (Lam $x $T $b) $u)
                 (let $wholeT (infer-tm $sig TyEnvNil $t)
                   (if (is-bad $wholeT)
                       (Err beta-ill-typed)
                       (let $rhs (tm-subst $x $u $b)
                         (if (tm-check $sig TyEnvNil $rhs $wholeT)
                             (Ok (CheckedThm ANil (Seq HNil (Eq $t $rhs))))
                             (Err beta-rhs-ill-typed)))))
                 (Err beta-not-a-redex))
               (unify $cert (CTrans $c1 $c2)
                 (let $R1 (kernel-check-admitted $sig $c1)
                   (let $R2 (kernel-check-admitted $sig $c2)
                     (unify $R1 (Ok (CheckedThm $u1 (Seq $G1 (Eq $a $b))))
                       (unify $R2 (Ok (CheckedThm $u2 (Seq $G2 (Eq $b2 $c))))
                         (if (== $b $b2)
                             (Ok (CheckedThm (ax-union $u1 $u2) (Seq (hyp-union $G1 $G2) (Eq $a $c))))
                             (Err trans-middle-mismatch))
                         $R2)
                       $R1)))
                 (Err unknown-certificate)))))))))

; ---------- entry-level curriculum signatures --------------------------------
(= (good-sig)
   (SCons (DConst zero num)
   (SCons (DConst succ (Arr num num))
   (SCons (DConst a set)
   (SCons (DConst b set)
   (SCons (DDef idnum (Arr num num) (Lam x num (Var x)))
   (SCons (DAxiom axMem (In (Cst a) (Cst b)))
   (SCons (DAxiom axSym (Imp (In (Cst a) (Cst b)) (In (Cst b) (Cst a))))
   (SCons (DAxiom exFalso (Imp (Atom FalseP) (Atom AnyP)))
          SNil)))))))))

(= (bad-def-sig)
   (SCons (DConst zero num)
   (SCons (DDef badDef set (Cst zero))
          SNil)))

(= (dup-sig)
   (SCons (DConst flip num)
   (SCons (DConst flip set)
          SNil)))

(= (forward-ref-sig)
   (SCons (DDef useLater num (Cst later))
   (SCons (DConst later num)
          SNil)))

(= (inconsistent-ledger-sig)
   (SCons (DAxiom boom (Atom FalseP))
   (SCons (DAxiom exFalsoB (Imp (Atom FalseP) (Atom B)))
          SNil)))

; ---------- regression and entry-level curriculum checks ---------------------
!(assertEqual (sig-admitted (good-sig)) True)
!(assertEqual (sig-admitted (bad-def-sig)) False)
!(assertEqual (sig-admitted (dup-sig)) False)
!(assertEqual (sig-admitted (forward-ref-sig)) False)
!(assertEqual (sig-admitted (inconsistent-ledger-sig)) True)

; Coq/Lean/HOL entry: P -> P
!(assertEqual
   (kernel-check (good-sig) (CDisch (Atom P) (CAssume (Atom P))))
   (Ok (CheckedThm ANil (Seq HNil (Imp (Atom P) (Atom P))))))

; HOL entry: K combinator theorem, P -> Q -> P
!(assertEqual
   (kernel-check (good-sig)
     (CDisch (Atom P) (CDisch (Atom Q) (CAssume (Atom P)))))
   (Ok (CheckedThm ANil (Seq HNil (Imp (Atom P) (Imp (Atom Q) (Atom P)))))))

; Equality entry: zero = zero
!(assertEqual
   (kernel-check (good-sig) (CRefl (Cst zero)))
   (Ok (CheckedThm ANil (Seq HNil (Eq (Cst zero) (Cst zero))))))

; Beta entry: ((lambda x:num. x) zero) = zero
!(assertEqual
   (kernel-check (good-sig) (CBeta (App (Lam x num (Var x)) (Cst zero))))
   (Ok (CheckedThm ANil (Seq HNil (Eq (App (Lam x num (Var x)) (Cst zero)) (Cst zero))))))

; HOTG/Megalodon entry: axSym axMem proves In b a, with provenance.
!(assertEqual
   (kernel-check (good-sig) (CMP (CUseAxiom axSym) (CUseAxiom axMem)))
   (Ok (CheckedThm (ACons axSym (ACons axMem ANil)) (Seq HNil (In (Cst b) (Cst a))))))

; Negative: invalid MP is rejected.
!(assertEqual
   (kernel-check (good-sig) (CMP (CUseAxiom axSym) (CAssume (Atom R))))
   (Err mp-antecedent-mismatch))

; Negative: a theorem-shaped literal is not a certificate.
!(assertEqual
   (kernel-check (good-sig) (CheckedThm ANil (Seq HNil (Atom forged))))
   (Err unknown-certificate))

; Inconsistent axioms are admitted only as explicit ledgered assumptions.
!(assertEqual
   (kernel-check (inconsistent-ledger-sig) (CMP (CUseAxiom exFalsoB) (CUseAxiom boom)))
   (Ok (CheckedThm (ACons exFalsoB (ACons boom ANil)) (Seq HNil (Atom B)))))

; ---------- WM-PLN / evidence-mode bridge -----------------------------------
; Classical kernel checking stays crisp.  A checked certificate can be projected
; into WM-PLN evidence with maximal truth; WM-PLN evidence is NOT a certificate
; and cannot be fed back into kernel-check to mint theorems.
(= (cert->wm-evidence $sig $cert)
   (let $R (kernel-check $sig $cert)
     (unify $R (Ok (CheckedThm $uses $seq))
       (Ok (WMEvidence (TV 1 1) (KernelChecked $uses) $seq))
       $R)))

; A tiny symbolic graded inference example: modus ponens in the evidence mode.
; It produces a WM claim, not a kernel theorem.
(= (wm-mp
     (WMEvidence $tv1 $src1 (Seq HNil (Imp $p $q)))
     (WMEvidence $tv2 $src2 (Seq HNil $p)))
   (WMEvidence (TVAnd $tv1 $tv2) (PLNMP $src1 $src2) (WMClaim $q)))

!(assertEqual
   (cert->wm-evidence (good-sig) (CDisch (Atom P) (CAssume (Atom P))))
   (Ok (WMEvidence (TV 1 1) (KernelChecked ANil)
        (Seq HNil (Imp (Atom P) (Atom P))))))

!(assertEqual
   (kernel-check (good-sig)
     (WMEvidence (TV 1 1) (KernelChecked ANil) (Seq HNil (Atom P))))
   (Err unknown-certificate))

!(assertEqual
   (cert->wm-evidence (good-sig) (CheckedThm ANil (Seq HNil (Atom forged))))
   (Err unknown-certificate))

!(assertEqual
   (wm-mp
     (WMEvidence (TV .8 .9) observed (Seq HNil (Imp (Atom P) (Atom Q))))
     (WMEvidence (TV .7 .8) observed (Seq HNil (Atom P))))
   (WMEvidence (TVAnd (TV .8 .9) (TV .7 .8))
     (PLNMP observed observed)
     (WMClaim (Atom Q))))

!(kernel-check (good-sig) (CDisch (Atom P) (CAssume (Atom P))))
!(kernel-check (good-sig) (CMP (CUseAxiom axSym) (CUseAxiom axMem)))
!(kernel-check (inconsistent-ledger-sig) (CMP (CUseAxiom exFalsoB) (CUseAxiom boom)))
