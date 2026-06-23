; =============================================================================
; kernel_signature_lf_ind_v1.metta
;
; Runnable inductive-family admission slice over kernel_signature_lf_eq_v0.metta.
;
; New admission form:
;   DInd name ParamsNil (ICtors (ICtor ctorName ctorType) ... ICNil)
;
; Generated/checked in this file:
;   * carrier lookup:      (Con name) : Type
;   * constructor lookup:  ctorName : ctorType
;   * strict positivity for non-parametric constructors
;   * generated recursor term: IndRec ind P cases scrut
;   * generated iota rules for non-indexed constructor telescopes whose
;     recursive arguments are bare I occurrences, e.g.
;       - nullary constructors       c : I
;       - unary recursive            c : I -> I
;       - nonrecursive argument      c : A -> I
;       - mixed telescope            c : A -> I -> I
;
; Demonstrated:
;   * Nat is admitted as DInd, not DConst nat/z/s.
;   * plus is a checked DDef whose body uses IndRec nat, not NatRec.
;   * plus z z = z by computation through generated IndRec.
;   * forall n. plus n z = n checks by generated IndRec induction.
;   * Bool is admitted as DInd with bnot, and forall b. bnot (bnot b) = b checks.
;   * A non-strictly-positive DInd is rejected at admission.
;
; Remaining obligation for the full requested generator:
;   GEq/GRfl/GTransp/Transp and indexed families (Id/J, Vec, parameters,
;   proof-dependent motives) are still hard-coded / not generated here.  Equality
;   remains primitive until DInd supports parameters and indices; generating Id
;   from ParamsNil would be a masquerade.
;
; Run:
;   /home/aimama/aihub/hyperon/CeTTa/cetta kernel_signature_lf_ind_v0.metta
; =============================================================================

; ---------- list helpers -----------------------------------------------------
(= (is-bad $x) (unify $x (Bad $e) True False))

(= (decl-name (DConst $n $T)) $n)
(= (decl-name (DDef $n $T $body)) $n)
(= (decl-name (DAxiom $n $T)) $n)
(= (decl-name (DInd $n $params $ctors)) $n)

; Inductive-family declarations used in this v0 slice:
;   DInd name ParamsNil (ICtors (ICtor ctorName ctorType) ... ICNil)
; Supported generated recursors:
;   - nullary constructor:        c : I
;   - unary recursive constructor c : I -> I
; This is enough to rederive Nat and Bool without hard-coded NatRec in proofs.

(= (ctor-has-name $n ICNil) False)
(= (ctor-has-name $n (ICtors (ICtor $c $T) $rest))
   (if (== $n $c) True (ctor-has-name $n $rest)))

(= (unique-ctors ICNil) True)
(= (unique-ctors (ICtors (ICtor $c $T) $rest))
   (if (ctor-has-name $c $rest) False (unique-ctors $rest)))

(= (decl-has-name $n (DConst $c $T)) (== $n $c))
(= (decl-has-name $n (DDef $c $T $body)) (== $n $c))
(= (decl-has-name $n (DAxiom $c $T)) (== $n $c))
(= (decl-has-name $n (DInd $i $params $ctors))
   (if (== $n $i) True (ctor-has-name $n $ctors)))

(= (sig-has-name $n SNil) False)
(= (sig-has-name $n (SCons $d $rest))
   (if (decl-has-name $n $d) True (sig-has-name $n $rest)))

(= (decl-names-disjoint-rest (DConst $n $T) $rest) (if (sig-has-name $n $rest) False True))
(= (decl-names-disjoint-rest (DDef $n $T $body) $rest) (if (sig-has-name $n $rest) False True))
(= (decl-names-disjoint-rest (DAxiom $n $T) $rest) (if (sig-has-name $n $rest) False True))
(= (ctors-disjoint-rest ICNil $rest) True)
(= (ctors-disjoint-rest (ICtors (ICtor $c $T) $cs) $rest)
   (if (sig-has-name $c $rest) False (ctors-disjoint-rest $cs $rest)))
(= (decl-names-disjoint-rest (DInd $n $params $ctors) $rest)
   (if (sig-has-name $n $rest) False
     (if (unique-ctors $ctors) (ctors-disjoint-rest $ctors $rest) False)))

(= (unique-sig SNil) True)
(= (unique-sig (SCons $d $rest))
   (if (decl-names-disjoint-rest $d $rest) (unique-sig $rest) False))

(= (ax-union ANil $ys) $ys)
(= (ax-union (ACons $x $xs) $ys) (ACons $x (ax-union $xs $ys)))

; ---------- finite signature lookup -----------------------------------------
; Declarations:
;   DConst name type    -- checked constant/constructor
;   DDef   name type body -- checked definition, unfolds during normalization
;   DAxiom name type    -- unchecked postulate, visible in theorem provenance

(= (ctor-type-of ICNil $x) (Bad unknown-constructor))
(= (ctor-type-of (ICtors (ICtor $c $T) $rest) $x)
   (if (== $x $c) $T (ctor-type-of $rest $x)))

(= (ind-ctors-of SNil $x) (Bad unknown-inductive))
(= (ind-ctors-of (SCons (DInd $i $params $ctors) $rest) $x)
   (if (== $x $i) $ctors (ind-ctors-of $rest $x)))
(= (ind-ctors-of (SCons (DConst $c $T) $rest) $x) (ind-ctors-of $rest $x))
(= (ind-ctors-of (SCons (DDef $c $T $body) $rest) $x) (ind-ctors-of $rest $x))
(= (ind-ctors-of (SCons (DAxiom $c $T) $rest) $x) (ind-ctors-of $rest $x))

(= (decl-type-of SNil $c) (Bad unknown-declaration))
(= (decl-type-of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DAxiom $c $T) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DInd $i $params ICNil) $rest) $x)
   (if (== $x $i) (Srt type) (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DInd $i $params (ICtors (ICtor $c $T) $ctors)) $rest) $x)
   (if (== $x $i) (Srt type)
     (if (== $x $c) $T
       (decl-type-of (SCons (DInd $i $params $ctors) $rest) $x))))

(= (def-body-of SNil $c) (Bad unknown-definition))
(= (def-body-of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $body (def-body-of $rest $x)))
(= (def-body-of (SCons (DConst $c $T) $rest) $x) (def-body-of $rest $x))
(= (def-body-of (SCons (DAxiom $c $T) $rest) $x) (def-body-of $rest $x))
(= (def-body-of (SCons (DInd $i $params $ctors) $rest) $x) (def-body-of $rest $x))

(= (is-axiom-name SNil $x) False)
(= (is-axiom-name (SCons (DAxiom $a $T) $rest) $x)
   (if (== $x $a) True (is-axiom-name $rest $x)))
(= (is-axiom-name (SCons (DConst $c $T) $rest) $x) (is-axiom-name $rest $x))
(= (is-axiom-name (SCons (DDef $c $T $body) $rest) $x) (is-axiom-name $rest $x))
(= (is-axiom-name (SCons (DInd $i $params $ctors) $rest) $x) (is-axiom-name $rest $x))

; ---------- lambda-Pi term machinery ----------------------------------------
(= (shift $d $c (Var $k)) (if (< $k $c) (Var $k) (Var (+ $k $d))))
(= (shift $d $c (Srt $s)) (Srt $s))
(= (shift $d $c (Con $x)) (Con $x))
(= (shift $d $c (Def $x)) (Def $x))
(= (shift $d $c (App $f $a)) (App (shift $d $c $f) (shift $d $c $a)))
(= (shift $d $c (Pi  $A $B)) (Pi  (shift $d $c $A) (shift $d (+ $c 1) $B)))
(= (shift $d $c (Lam $A $b)) (Lam (shift $d $c $A) (shift $d (+ $c 1) $b)))
(= (shift $d $c (NatRec $P $zcase $scase $n))
   (NatRec (shift $d $c $P) (shift $d $c $zcase) (shift $d $c $scase) (shift $d $c $n)))
(= (shift $d $c (IndRec $ind $P $cases $n))
   (IndRec $ind (shift $d $c $P) (shift-cases $d $c $cases) (shift $d $c $n)))
(= (shift $d $c (GEq $A $a $b))
   (GEq (shift $d $c $A) (shift $d $c $a) (shift $d $c $b)))
(= (shift $d $c (GRfl $A $a))
   (GRfl (shift $d $c $A) (shift $d $c $a)))
(= (shift $d $c (Transp $P $a $b $p $x))
   (Transp (shift $d $c $P) (shift $d $c $a) (shift $d $c $b) (shift $d $c $p) (shift $d $c $x)))
(= (shift $d $c (GTransp $A $P $a $b $p $x))
   (GTransp (shift $d $c $A) (shift $d $c $P) (shift $d $c $a) (shift $d $c $b) (shift $d $c $p) (shift $d $c $x)))
(= (shift $d $c (Bad $e)) (Bad $e))
(= (shift-cases $d $c CasesNil) CasesNil)
(= (shift-cases $d $c (Cases (Case $ctor $body) $rest))
   (Cases (Case $ctor (shift $d $c $body)) (shift-cases $d $c $rest)))

(= (subst $j $s (Var $k)) (if (== $k $j) $s (if (> $k $j) (Var (- $k 1)) (Var $k))))
(= (subst $j $s (Srt $x)) (Srt $x))
(= (subst $j $s (Con $x)) (Con $x))
(= (subst $j $s (Def $x)) (Def $x))
(= (subst $j $s (App $f $a)) (App (subst $j $s $f) (subst $j $s $a)))
(= (subst $j $s (Pi  $A $B)) (Pi  (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $B)))
(= (subst $j $s (Lam $A $b)) (Lam (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $b)))
(= (subst $j $s (NatRec $P $zcase $scase $n))
   (NatRec (subst $j $s $P) (subst $j $s $zcase) (subst $j $s $scase) (subst $j $s $n)))
(= (subst $j $s (IndRec $ind $P $cases $n))
   (IndRec $ind (subst $j $s $P) (subst-cases $j $s $cases) (subst $j $s $n)))
(= (subst $j $s (GEq $A $a $b))
   (GEq (subst $j $s $A) (subst $j $s $a) (subst $j $s $b)))
(= (subst $j $s (GRfl $A $a))
   (GRfl (subst $j $s $A) (subst $j $s $a)))
(= (subst $j $s (Transp $P $a $b $p $x))
   (Transp (subst $j $s $P) (subst $j $s $a) (subst $j $s $b) (subst $j $s $p) (subst $j $s $x)))
(= (subst $j $s (GTransp $A $P $a $b $p $x))
   (GTransp (subst $j $s $A) (subst $j $s $P) (subst $j $s $a) (subst $j $s $b) (subst $j $s $p) (subst $j $s $x)))
(= (subst $j $s (Bad $e)) (Bad $e))
(= (subst-cases $j $s CasesNil) CasesNil)
(= (subst-cases $j $s (Cases (Case $ctor $body) $rest))
   (Cases (Case $ctor (subst $j $s $body)) (subst-cases $j $s $rest)))

(= (nf $sig (Var $k)) (Var $k))
(= (nf $sig (Srt $s)) (Srt $s))
(= (nf $sig (Con $x)) (Con $x))
(= (nf $sig (Def $x))
   (let $body (def-body-of $sig $x)
     (if (is-bad $body) (Bad unknown-definition) (nf $sig $body))))
(= (nf $sig (Pi  $A $B)) (Pi  (nf $sig $A) (nf $sig $B)))
(= (nf $sig (Lam $A $b)) (Lam (nf $sig $A) (nf $sig $b)))
(= (nf $sig (NatRec $P $zcase $scase $n))
   (nf-natrec $sig (nf $sig $P) (nf $sig $zcase) (nf $sig $scase) (nf $sig $n)))
(= (nf $sig (IndRec $ind $P $cases $n))
   (nf-indrec $sig $ind (nf $sig $P) (nf-cases $sig $cases) (nf $sig $n)))
(= (nf $sig (GEq $A $a $b))
   (GEq (nf $sig $A) (nf $sig $a) (nf $sig $b)))
(= (nf $sig (GRfl $A $a))
   (GRfl (nf $sig $A) (nf $sig $a)))
(= (nf $sig (Transp $P $a $b $p $x))
   (nf-transp $sig (nf $sig $P) (nf $sig $a) (nf $sig $b) (nf $sig $p) (nf $sig $x)))
(= (nf $sig (GTransp $A $P $a $b $p $x))
   (nf-gtransp $sig (nf $sig $A) (nf $sig $P) (nf $sig $a) (nf $sig $b) (nf $sig $p) (nf $sig $x)))
(= (nf $sig (Bad $e)) (Bad $e))
(= (nf-cases $sig CasesNil) CasesNil)
(= (nf-cases $sig (Cases (Case $ctor $body) $rest))
   (Cases (Case $ctor (nf $sig $body)) (nf-cases $sig $rest)))
(= (nf $sig (App $f $a)) (nf-app $sig (nf $sig $f) (nf $sig $a)))
(= (nf-app $sig $f $a) (unify $f (Lam $A $b) (nf $sig (subst 0 $a $b)) (App $f $a)))
(= (nf-natrec $sig $P $zcase $scase $n)
   (unify $n (Con z)
     $zcase
     (unify $n (App (Con s) $k)
       (nf $sig (App (App $scase $k) (NatRec $P $zcase $scase $k)))
       (NatRec $P $zcase $scase $n))))

(= (case-body-of CasesNil $ctor) (Bad missing-case))
(= (case-body-of (Cases (Case $c $body) $rest) $ctor)
   (if (== $c $ctor) $body (case-body-of $rest $ctor)))

(= (args-snoc ArgsNil $a) (ArgsCons $a ArgsNil))
(= (args-snoc (ArgsCons $x $xs) $a) (ArgsCons $x (args-snoc $xs $a)))

(= (app-head (Con $c)) $c)
(= (app-head (App $f $a)) (app-head $f))
(= (app-head (Var $k)) (Bad not-constructor-app))
(= (app-head (Srt $s)) (Bad not-constructor-app))
(= (app-head (Def $c)) (Bad not-constructor-app))
(= (app-head (Pi $A $B)) (Bad not-constructor-app))
(= (app-head (Lam $A $b)) (Bad not-constructor-app))
(= (app-head (NatRec $P $zcase $scase $n)) (Bad not-constructor-app))
(= (app-head (IndRec $ind $P $cases $n)) (Bad not-constructor-app))
(= (app-head (GEq $A $a $b)) (Bad not-constructor-app))
(= (app-head (GRfl $A $a)) (Bad not-constructor-app))
(= (app-head (Transp $P $a $b $p $x)) (Bad not-constructor-app))
(= (app-head (GTransp $A $P $a $b $p $x)) (Bad not-constructor-app))
(= (app-head (Bad $e)) (Bad not-constructor-app))

(= (app-args (Con $c)) ArgsNil)
(= (app-args (App $f $a)) (args-snoc (app-args $f) $a))
(= (app-args (Var $k)) ArgsNil)
(= (app-args (Srt $s)) ArgsNil)
(= (app-args (Def $c)) ArgsNil)
(= (app-args (Pi $A $B)) ArgsNil)
(= (app-args (Lam $A $b)) ArgsNil)
(= (app-args (NatRec $P $zcase $scase $n)) ArgsNil)
(= (app-args (IndRec $ind $P $cases $n)) ArgsNil)
(= (app-args (GEq $A $a $b)) ArgsNil)
(= (app-args (GRfl $A $a)) ArgsNil)
(= (app-args (Transp $P $a $b $p $x)) ArgsNil)
(= (app-args (GTransp $A $P $a $b $p $x)) ArgsNil)
(= (app-args (Bad $e)) ArgsNil)

(= (branch-apply $sig $ind $P $cases $body $CT $args)
   (unify $CT (Con $ind)
     (unify $args ArgsNil $body (Bad indrec-arity-mismatch))
     (unify $CT (Pi $A $B)
       (unify $args (ArgsCons $arg $rest)
         (branch-apply-arg $sig $ind $P $cases $body $A $B $arg $rest)
         (Bad indrec-missing-arg))
       (Bad unsupported-constructor-shape))))

(= (branch-apply-arg $sig $ind $P $cases $body $A $B $arg $rest)
   (unify $A (Con $ind)
     (branch-apply $sig $ind $P $cases
       (App (App $body $arg) (IndRec $ind $P $cases $arg))
       (subst 0 $arg $B)
       $rest)
     (branch-apply $sig $ind $P $cases
       (App $body $arg)
       (subst 0 $arg $B)
       $rest)))

(= (nf-indrec $sig $ind $P $cases $n)
   (let $ctor (app-head $n)
     (let $ctors (ind-ctors-of $sig $ind)
       (let $CT (ctor-type-of $ctors $ctor)
         (if (is-bad $CT)
           (IndRec $ind $P $cases $n)
           (let $body (case-body-of $cases $ctor)
             (if (is-bad $body)
               (IndRec $ind $P $cases $n)
               (let $redex (branch-apply $sig $ind $P $cases $body $CT (app-args $n))
                 (if (is-bad $redex)
                   (IndRec $ind $P $cases $n)
                   (nf $sig $redex))))))))))
(= (nf-transp $sig $P $a $b $p $x)
   (unify $p (App (Con rfl) $k)
     (if (== $a $k)
       (if (== $b $k) $x (Transp $P $a $b $p $x))
       (Transp $P $a $b $p $x))
     (Transp $P $a $b $p $x)))
(= (nf-gtransp $sig $A $P $a $b $p $x)
   (unify $p (GRfl $A0 $k)
     (if (== $A $A0)
       (if (== $a $k)
         (if (== $b $k) $x (GTransp $A $P $a $b $p $x))
         (GTransp $A $P $a $b $p $x))
       (GTransp $A $P $a $b $p $x))
     (GTransp $A $P $a $b $p $x)))

(= (conv $sig $x $y)
   (if (is-bad (nf $sig $x)) False
     (if (is-bad (nf $sig $y)) False
       (== (nf $sig $x) (nf $sig $y)))))

(= (ctx-nth $i CtxNil) (Bad var-out-of-range))
(= (ctx-nth $i (CtxCons $h $t)) (if (== $i 0) $h (ctx-nth (- $i 1) $t)))
(= (ctx-type $i $ctx) (shift (+ $i 1) 0 (ctx-nth $i $ctx)))

(= (pts-rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi-bad-codomain)))
     (Bad pi-domain-not-type)))

(= (infer $sig $ctx (Srt type)) (Srt kind))
(= (infer $sig $ctx (Srt kind)) (Bad kind-is-topsort))
(= (infer $sig $ctx (Bad $e)) (Bad $e))
(= (infer $sig $ctx (Var $i))  (ctx-type $i $ctx))
(= (infer $sig $ctx (Con $c))  (decl-type-of $sig $c))
(= (infer $sig $ctx (Def $c))  (decl-type-of $sig $c))
(= (infer $sig $ctx (Pi $A $B))
   (let $sA (nf $sig (infer $sig $ctx $A))
     (let $sB (nf $sig (infer $sig (CtxCons $A $ctx) $B)) (pts-rule $sA $sB))))
(= (infer-lam $sig $ctx $A $b)
   (let $sA (nf $sig (infer $sig $ctx $A))
     (unify $sA (Srt type)
        (let $tb (infer $sig (CtxCons $A $ctx) $b)
          (let $ntb (nf $sig $tb)
            (let $bad (is-bad $ntb)
              (if $bad (Bad lam-body-bad-type) (Pi $A $tb)))))
        (Bad lam-domain-not-a-type))))
(= (infer $sig $ctx (Lam $A $b)) (infer-lam $sig $ctx $A $b))
(= (infer-app $sig $ctx $f $a)
   (let $tf (nf $sig (infer $sig $ctx $f))
     (unify $tf (Pi $A $B)
        (if (conv $sig (infer $sig $ctx $a) $A) (subst 0 $a $B) (Bad arg-type-mismatch))
        (Bad applied-a-non-function))))
(= (infer $sig $ctx (App $f $a)) (infer-app $sig $ctx $f $a))
(= (natrec-step-type $P)
   (Pi (Con nat)
     (Pi (App (shift 1 0 $P) (Var 0))
       (App (shift 2 0 $P) (App (Con s) (Var 1))))))
(= (infer-natrec $sig $ctx $P $zcase $scase $n)
   (if (check-conv $sig $ctx $P (Pi (Con nat) (Srt type)))
     (if (check-conv $sig $ctx $zcase (App $P (Con z)))
       (if (check-conv $sig $ctx $scase (natrec-step-type $P))
         (if (check-conv $sig $ctx $n (Con nat))
           (App $P $n)
           (Bad natrec-scrutinee-not-nat))
         (Bad natrec-bad-step))
       (Bad natrec-bad-zero))
     (Bad natrec-bad-motive)))
(= (infer $sig $ctx (NatRec $P $zcase $scase $n)) (infer-natrec $sig $ctx $P $zcase $scase $n))

(= (rec-branch-type $ind $P $ctor $T)
   (rec-branch-type-go $ind $P (Con $ctor) $T))

(= (rec-branch-type-go $ind $P $ctorApp $T)
   (unify $T (Con $ind)
     (App $P $ctorApp)
     (unify $T (Pi $A $B)
       (unify $A (Con $ind)
         (Pi $A
           (Pi (App (shift 1 0 $P) (Var 0))
             (rec-branch-type-go
               $ind
               (shift 2 0 $P)
               (App (shift 2 0 $ctorApp) (Var 1))
               (shift 2 0 $B))))
         (if (term-occurs-name $ind $A)
           (Bad unsupported-constructor-shape)
           (Pi $A
             (rec-branch-type-go
               $ind
               (shift 1 0 $P)
               (App (shift 1 0 $ctorApp) (Var 0))
               (shift 1 0 $B)))))
       (Bad unsupported-constructor-shape))))

(= (case-remove CasesNil $ctor) (Bad missing-case))
(= (case-remove (Cases (Case $c $body) $rest) $ctor)
   (if (== $c $ctor)
     $rest
     (let $rest2 (case-remove $rest $ctor)
       (if (is-bad $rest2) (Bad missing-case) (Cases (Case $c $body) $rest2)))))

(= (cases-empty CasesNil) True)
(= (cases-empty (Cases (Case $c $body) $rest)) False)

(= (cases-check $sig $ctx $ind $P ICNil $cases) (cases-empty $cases))
(= (cases-check $sig $ctx $ind $P (ICtors (ICtor $ctor $CT) $rest) $cases)
   (let $body (case-body-of $cases $ctor)
     (if (is-bad $body) False
       (if (check-conv $sig $ctx $body (rec-branch-type $ind $P $ctor $CT))
         (let $cases2 (case-remove $cases $ctor)
           (if (is-bad $cases2) False (cases-check $sig $ctx $ind $P $rest $cases2)))
         False))))

(= (infer-indrec $sig $ctx $ind $P $cases $n)
   (let $ctors (ind-ctors-of $sig $ind)
     (if (is-bad $ctors)
       (Bad unknown-inductive)
       (if (check-conv $sig $ctx (Con $ind) (Srt type))
         (if (check-conv $sig $ctx $P (Pi (Con $ind) (Srt type)))
           (if (cases-check $sig $ctx $ind $P $ctors $cases)
             (if (check-conv $sig $ctx $n (Con $ind))
               (App $P $n)
               (Bad indrec-bad-scrutinee))
             (Bad indrec-bad-cases))
           (Bad indrec-bad-motive))
         (Bad indrec-bad-carrier)))))
(= (infer $sig $ctx (IndRec $ind $P $cases $n)) (infer-indrec $sig $ctx $ind $P $cases $n))
(= (infer-geq $sig $ctx $A $a $b)
   (if (check-conv $sig $ctx $A (Srt type))
     (if (check-conv $sig $ctx $a $A)
       (if (check-conv $sig $ctx $b $A)
         (Srt type)
         (Bad geq-bad-right))
       (Bad geq-bad-left))
     (Bad geq-bad-carrier)))
(= (infer $sig $ctx (GEq $A $a $b)) (infer-geq $sig $ctx $A $a $b))
(= (infer-grfl $sig $ctx $A $a)
   (if (check-conv $sig $ctx $A (Srt type))
     (if (check-conv $sig $ctx $a $A)
       (GEq $A $a $a)
       (Bad grfl-bad-term))
     (Bad grfl-bad-carrier)))
(= (infer $sig $ctx (GRfl $A $a)) (infer-grfl $sig $ctx $A $a))
(= (infer-transp $sig $ctx $P $a $b $p $x)
   (if (check-conv $sig $ctx $P (Pi (Con nat) (Srt type)))
     (if (check-conv $sig $ctx $a (Con nat))
       (if (check-conv $sig $ctx $b (Con nat))
         (if (check-conv $sig $ctx $p (App (App (Con eqn) $a) $b))
           (if (check-conv $sig $ctx $x (App $P $a))
             (App $P $b)
             (Bad transp-bad-elem))
           (Bad transp-bad-proof))
         (Bad transp-bad-b))
       (Bad transp-bad-a))
     (Bad transp-bad-motive)))
(= (infer $sig $ctx (Transp $P $a $b $p $x)) (infer-transp $sig $ctx $P $a $b $p $x))
(= (infer-gtransp $sig $ctx $A $P $a $b $p $x)
   (if (check-conv $sig $ctx $A (Srt type))
     (if (check-conv $sig $ctx $P (Pi $A (Srt type)))
       (if (check-conv $sig $ctx $a $A)
         (if (check-conv $sig $ctx $b $A)
           (if (check-conv $sig $ctx $p (GEq $A $a $b))
             (if (check-conv $sig $ctx $x (App $P $a))
               (App $P $b)
               (Bad gtransp-bad-elem))
             (Bad gtransp-bad-proof))
           (Bad gtransp-bad-b))
         (Bad gtransp-bad-a))
       (Bad gtransp-bad-motive))
     (Bad gtransp-bad-carrier)))
(= (infer $sig $ctx (GTransp $A $P $a $b $p $x)) (infer-gtransp $sig $ctx $A $P $a $b $p $x))
(= (sort-ok $s)
   (unify $s (Srt type) True
     (unify $s (Srt kind) True False)))
(= (type-ok $sig $ctx $ty)
   (let $ITY (infer $sig $ctx $ty)
     (let $S (nf $sig $ITY) (sort-ok $S))))
(= (check-conv $sig $ctx $t $ty) (conv $sig (infer $sig $ctx $t) $ty))
(= (check $sig $ctx $t $ty)
   (let $okTy (type-ok $sig $ctx $ty)
     (if $okTy (check-conv $sig $ctx $t $ty) False)))
(= (check-result $sig $ctx $t $ty) (check $sig $ctx $t $ty))

; ---------- signature admission ---------------------------------------------
(= (term-occurs-name $n (Var $k)) False)
(= (term-occurs-name $n (Srt $s)) False)
(= (term-occurs-name $n (Con $c)) (== $n $c))
(= (term-occurs-name $n (Def $c)) (== $n $c))
(= (term-occurs-name $n (App $f $a))
   (if (term-occurs-name $n $f) True (term-occurs-name $n $a)))
(= (term-occurs-name $n (Pi $A $B))
   (if (term-occurs-name $n $A) True (term-occurs-name $n $B)))
(= (term-occurs-name $n (Lam $A $b))
   (if (term-occurs-name $n $A) True (term-occurs-name $n $b)))
(= (term-occurs-name $n (NatRec $P $zcase $scase $scrut)) True)
(= (term-occurs-name $n (IndRec $ind $P $cases $scrut)) True)
(= (term-occurs-name $n (GEq $A $a $b))
   (if (term-occurs-name $n $A) True (if (term-occurs-name $n $a) True (term-occurs-name $n $b))))
(= (term-occurs-name $n (GRfl $A $a))
   (if (term-occurs-name $n $A) True (term-occurs-name $n $a)))
(= (term-occurs-name $n (Transp $P $a $b $p $x)) True)
(= (term-occurs-name $n (GTransp $A $P $a $b $p $x)) True)
(= (term-occurs-name $n (Bad $e)) False)

(= (strict-pos-arg $ind $A)
   (unify $A (Con $ind)
     True
     (if (term-occurs-name $ind $A) False True)))
(= (strict-pos-ctor-type $ind $T)
   (unify $T (Con $ind)
     True
     (unify $T (Pi $A $B)
       (if (strict-pos-arg $ind $A) (strict-pos-ctor-type $ind $B) False)
       False)))
(= (ctors-strict-pos $ind ICNil) True)
(= (ctors-strict-pos $ind (ICtors (ICtor $c $T) $rest))
   (if (strict-pos-ctor-type $ind $T) (ctors-strict-pos $ind $rest) False))

(= (rec-supported-ctor-type $ind $T)
   (unify $T (Con $ind)
     True
     (unify $T (Pi $A $B)
       (unify $A (Con $ind)
         (rec-supported-ctor-type $ind $B)
         (if (term-occurs-name $ind $A) False (rec-supported-ctor-type $ind $B)))
       False)))
(= (ctors-rec-supported $ind ICNil) True)
(= (ctors-rec-supported $ind (ICtors (ICtor $c $T) $rest))
   (if (rec-supported-ctor-type $ind $T) (ctors-rec-supported $ind $rest) False))

(= (ctors-types-ok $prefix ICNil) True)
(= (ctors-types-ok $prefix (ICtors (ICtor $c $T) $rest))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT)
       (if (sort-ok $S) (ctors-types-ok $prefix $rest) False))))

(= (wf-decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT)
       (sort-ok $S))))
(= (wf-decl $prefix (DDef $n $T $body))
   (let $okT (wf-decl $prefix (DConst $n $T))
     (if $okT (check-conv $prefix CtxNil $body $T) False)))
(= (wf-decl $prefix (DAxiom $n $T)) (wf-decl $prefix (DConst $n $T)))
(= (wf-decl $prefix (DInd $n ParamsNil $ctors))
   (if (unique-ctors $ctors)
     (if (ctors-strict-pos $n $ctors)
       (if (ctors-rec-supported $n $ctors)
         (ctors-types-ok (SCons (DConst $n (Srt type)) $prefix) $ctors)
         False)
       False)
     False))

(= (wf-sig-prefix $prefix SNil) True)
(= (wf-sig-prefix $prefix (SCons $d $rest))
   (let $ok (wf-decl $prefix $d)
     (if $ok
       (wf-sig-prefix (SCons $d $prefix) $rest)
       False)))

(= (sig-admitted $sig)
   (let $u (unique-sig $sig)
     (if $u (wf-sig-prefix SNil $sig) False)))

; ---------- theorem provenance over checked proof terms ----------------------
(= (term-axioms $sig (Var $k)) ANil)
(= (term-axioms $sig (Srt $s)) ANil)
(= (term-axioms $sig (Con $c))
   (if (is-axiom-name $sig $c) (ACons $c ANil) ANil))
(= (term-axioms $sig (Def $c)) ANil)
(= (term-axioms $sig (Pi $A $B)) (ax-union (term-axioms $sig $A) (term-axioms $sig $B)))
(= (term-axioms $sig (Lam $A $b)) (ax-union (term-axioms $sig $A) (term-axioms $sig $b)))
(= (term-axioms $sig (App $f $a)) (ax-union (term-axioms $sig $f) (term-axioms $sig $a)))
(= (term-axioms $sig (NatRec $P $zcase $scase $n))
   (ax-union (term-axioms $sig $P)
     (ax-union (term-axioms $sig $zcase)
       (ax-union (term-axioms $sig $scase) (term-axioms $sig $n)))))
(= (term-axioms $sig (IndRec $ind $P $cases $n))
   (ax-union (term-axioms $sig $P)
     (ax-union (term-axioms-cases $sig $cases) (term-axioms $sig $n))))
(= (term-axioms-cases $sig CasesNil) ANil)
(= (term-axioms-cases $sig (Cases (Case $ctor $body) $rest))
   (ax-union (term-axioms $sig $body) (term-axioms-cases $sig $rest)))
(= (term-axioms $sig (GEq $A $a $b))
   (ax-union (term-axioms $sig $A)
     (ax-union (term-axioms $sig $a) (term-axioms $sig $b))))
(= (term-axioms $sig (GRfl $A $a))
   (ax-union (term-axioms $sig $A) (term-axioms $sig $a)))
(= (term-axioms $sig (Transp $P $a $b $p $x))
   (ax-union (term-axioms $sig $P)
     (ax-union (term-axioms $sig $a)
       (ax-union (term-axioms $sig $b)
         (ax-union (term-axioms $sig $p) (term-axioms $sig $x))))))
(= (term-axioms $sig (GTransp $A $P $a $b $p $x))
   (ax-union (term-axioms $sig $A)
     (ax-union (term-axioms $sig $P)
       (ax-union (term-axioms $sig $a)
         (ax-union (term-axioms $sig $b)
           (ax-union (term-axioms $sig $p) (term-axioms $sig $x)))))))
(= (term-axioms $sig (Bad $e)) ANil)

(= (kernel-check-checked $sig $term $type True)
   (let $uses (term-axioms $sig $term)
     (Ok (CheckedPrf $uses $term $type))))
(= (kernel-check-checked $sig $term $type False) (Err check-failed))
(= (kernel-check-admitted $sig $term $type True)
   (kernel-check-checked $sig $term $type (check-result $sig CtxNil $term $type)))
(= (kernel-check-admitted $sig $term $type False) (Err signature-not-admitted))
(= (kernel-check $sig $term $type)
   (case (sig-admitted $sig)
     ((True (kernel-check-checked $sig $term $type (check-result $sig CtxNil $term $type)))
      (False (Err signature-not-admitted)))))

; ---------- finite curriculum signature --------------------------------------
(= (good-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DConst imp (Pi (Con o) (Pi (Con o) (Con o))))
   (SCons (DConst impI
     (Pi (Con o) (Pi (Con o)
       (Pi (Pi (App (Con prf) (Var 1)) (App (Con prf) (Var 1)))
           (App (Con prf) (App (App (Con imp) (Var 2)) (Var 1)))))))
   (SCons (DConst impE
     (Pi (Con o) (Pi (Con o)
       (Pi (App (Con prf) (App (App (Con imp) (Var 1)) (Var 0)))
         (Pi (App (Con prf) (Var 2)) (App (Con prf) (Var 2)))))))
   (SCons (DConst A (Con o))
   (SCons (DConst B (Con o))
   (SCons (DDef holds (Pi (Con o) (Srt type)) (Lam (Con o) (App (Con prf) (Var 0))))
   (SCons (DInd nat ParamsNil
     (ICtors (ICtor z (Con nat))
       (ICtors (ICtor s (Pi (Con nat) (Con nat))) ICNil)))
   (SCons (DConst eqn (Pi (Con nat) (Pi (Con nat) (Srt type))))
   (SCons (DConst rfl (Pi (Con nat) (App (App (Con eqn) (Var 0)) (Var 0))))
   (SCons (DDef plus
     (Pi (Con nat) (Pi (Con nat) (Con nat)))
     (Lam (Con nat)
       (Lam (Con nat)
         (IndRec nat
           (Lam (Con nat) (Con nat))
           (Cases (Case z (Var 0))
             (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
           (Var 1)))))
   (SCons (DInd ibool ParamsNil
     (ICtors (ICtor tt (Con ibool))
       (ICtors (ICtor ff (Con ibool)) ICNil)))
   (SCons (DDef bnot
     (Pi (Con ibool) (Con ibool))
     (Lam (Con ibool)
       (IndRec ibool
         (Lam (Con ibool) (Con ibool))
         (Cases (Case tt (Con ff))
           (Cases (Case ff (Con tt)) CasesNil))
         (Var 0))))
   (SCons (DConst set (Srt type))
   (SCons (DConst In (Pi (Con set) (Pi (Con set) (Con o))))
   (SCons (DConst a (Con set))
   (SCons (DConst b (Con set))
   (SCons (DAxiom axMem (App (Con prf) (App (App (Con In) (Con a)) (Con b))))
   (SCons (DAxiom axSym
     (App (Con prf) (App (App (Con imp) (App (App (Con In) (Con a)) (Con b)))
                                        (App (App (Con In) (Con b)) (Con a)))))
          SNil)))))))))))))))))))))

(= (bad-def-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst A (Con o))
   (SCons (DConst falseP (Con o))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DDef defAsPrf (App (Con prf) (Con falseP)) (Con A))
          SNil))))))

(= (dup-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst o (Srt type))
          SNil)))

(= (forward-ref-sig)
   (SCons (DDef useLater (Con later) (Con later))
   (SCons (DConst later (Srt type))
          SNil)))

(= (inconsistent-ledger-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DConst falseP (Con o))
   (SCons (DConst B (Con o))
   (SCons (DConst falseE
     (Pi (App (Con prf) (Con falseP)) (Pi (Con o) (App (Con prf) (Var 0)))))
   (SCons (DAxiom boom (App (Con prf) (Con falseP)))
          SNil)))))))

; ---------- admission regressions -------------------------------------------
!(assertEqual (sig-admitted (good-sig)) True)
!(assertEqual (sig-admitted (bad-def-sig)) False)
!(assertEqual (sig-admitted (dup-sig)) False)
!(assertEqual (sig-admitted (forward-ref-sig)) False)
!(assertEqual (sig-admitted (inconsistent-ledger-sig)) True)

; Bad is not a type.
!(assertEqual (infer (good-sig) CtxNil (Lam (Srt type) (Var 0))) (Bad lam-domain-not-a-type))
!(assertEqual (check (good-sig) CtxNil (Lam (Con o) (Srt kind)) (Pi (Con o) (Bad kind-is-topsort))) False)

; Delta conversion through an admitted definition.
!(assertEqual (conv (good-sig) (App (Def holds) (Con A)) (App (Con prf) (Con A))) True)

; Entry examples: DTT rfl, HOL implication proofs, beta, HOTG axiom composition.
!(assertEqual
   (kernel-check (good-sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (Con z)))
   (Ok (CheckedPrf ANil (App (Con rfl) (Con z)) (App (App (Con eqn) (Con z)) (Con z)))))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))
   (Ok (CheckedPrf ANil
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (Con impI) (Con A)) (App (App (Con imp) (Con B)) (Con A)))
          (Lam (App (Con prf) (Con A))
               (App (App (App (Con impI) (Con B)) (Con A))
                    (Lam (App (Con prf) (Con B)) (Var 1)))))
     (App (Con prf) (App (App (Con imp) (Con A)) (App (App (Con imp) (Con B)) (Con A)))))
   (Ok (CheckedPrf ANil
     (App (App (App (Con impI) (Con A)) (App (App (Con imp) (Con B)) (Con A)))
          (Lam (App (Con prf) (Con A))
               (App (App (App (Con impI) (Con B)) (Con A))
                    (Lam (App (Con prf) (Con B)) (Var 1)))))
     (App (Con prf) (App (App (Con imp) (Con A)) (App (App (Con imp) (Con B)) (Con A)))))))

!(assertEqual
   (kernel-check (good-sig)
     (App (Lam (Con nat) (Var 0)) (Con z))
     (Con nat))
   (Ok (CheckedPrf ANil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))))

; NatRec is a real dependent eliminator, not an opaque constant.
!(assertEqual
   (infer (good-sig) CtxNil
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z)))
   (App (Lam (Con nat) (Con nat)) (Con z)))

; Iota at zero: NatRec P z s z reduces to the zero case.
!(assertEqual
   (conv (good-sig)
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z))
     (Con z))
   True)

; Iota at successor: NatRec P z s (s z) reduces by one successor step.
!(assertEqual
   (conv (good-sig)
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

; plus is admitted only because its body checks against nat -> nat -> nat.
!(assertEqual
   (conv (good-sig)
     (App (App (Def plus) (Con z)) (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

!(assertEqual
   (conv (good-sig)
     (App (App (Def plus) (App (Con s) (Con z))) (Con z))
     (App (Con s) (Con z)))
   True)

; The old Exp2 wall is closed for concrete plus-zero by computation: rfl now checks.
!(assertEqual
   (kernel-check (good-sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Def plus) (Con z)) (Con z))) (Con z)))
   (Ok (CheckedPrf ANil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Def plus) (Con z)) (Con z))) (Con z)))))

; Negative: the motive must be nat -> Type.
!(assertEqual
   (infer (good-sig) CtxNil
     (NatRec
       (Con nat)
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z)))
   (Bad natrec-bad-motive))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (App (Con impE) (App (App (Con In) (Con a)) (Con b)))
                                    (App (App (Con In) (Con b)) (Con a)))
               (Con axSym)) (Con axMem))
     (App (Con prf) (App (App (Con In) (Con b)) (Con a))))
   (Ok (CheckedPrf (ACons axSym (ACons axMem ANil))
     (App (App (App (App (Con impE) (App (App (Con In) (Con a)) (Con b)))
                                    (App (App (Con In) (Con b)) (Con a)))
               (Con axSym)) (Con axMem))
     (App (Con prf) (App (App (Con In) (Con b)) (Con a))))))

; Old break probes no longer break admitted signatures.
!(assertEqual
   (kernel-check (bad-def-sig) (Def defAsPrf) (App (Con prf) (Con falseP)))
   (Err signature-not-admitted))

!(assertEqual
   (kernel-check (inconsistent-ledger-sig)
     (App (App (Con falseE) (Con boom)) (Con B))
     (App (Con prf) (Con B)))
   (Ok (CheckedPrf (ACons boom ANil)
     (App (App (Con falseE) (Con boom)) (Con B))
     (App (Con prf) (Con B)))))

; Wrong proof targets still reject.
!(assertEqual
   (kernel-check (good-sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (App (Con s) (Con z))))
   (Err check-failed))

!(assertEqual
   (kernel-check (good-sig)
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con B))))
   (Err check-failed))


; ==================== GENERATED INDUCTIVE ADMISSION SLICE ===================
; Nat is no longer declared via DConst nat/z/s in good-sig.  DInd generates the
; carrier and constructor lookup, and IndRec checks using the generated recursor
; branch types.
!(assertEqual (decl-type-of (good-sig) nat) (Srt type))
!(assertEqual (decl-type-of (good-sig) z) (Con nat))
!(assertEqual (decl-type-of (good-sig) s) (Pi (Con nat) (Con nat)))

(= (bad-ind-sig)
   (SCons (DInd bad ParamsNil
     (ICtors (ICtor mkBad (Pi (Pi (Con bad) (Con bad)) (Con bad))) ICNil))
          SNil))
!(assertEqual (sig-admitted (bad-ind-sig)) False)

; Generic generated Nat recursor iota, zero and successor.
!(assertEqual
   (conv (good-sig)
     (IndRec nat
       (Lam (Con nat) (Con nat))
       (Cases (Case z (Con z))
         (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
       (Con z))
     (Con z))
   True)

!(assertEqual
   (conv (good-sig)
     (IndRec nat
       (Lam (Con nat) (Con nat))
       (Cases (Case z (Con z))
         (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
       (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

; New generated Bool inductive + generated recursor + worked proof:
; forall b:ibool. bnot (bnot b) = b, by IndRec over Bool.
!(assertEqual (decl-type-of (good-sig) ibool) (Srt type))
!(assertEqual (decl-type-of (good-sig) tt) (Con ibool))
!(assertEqual (conv (good-sig) (App (Def bnot) (Con tt)) (Con ff)) True)
!(assertEqual
   (kernel-check (good-sig)
     (Lam (Con ibool)
       (IndRec ibool
         (Lam (Con ibool)
           (GEq (Con ibool) (App (Def bnot) (App (Def bnot) (Var 0))) (Var 0)))
         (Cases (Case tt (GRfl (Con ibool) (Con tt)))
           (Cases (Case ff (GRfl (Con ibool) (Con ff))) CasesNil))
         (Var 0)))
     (Pi (Con ibool)
       (GEq (Con ibool) (App (Def bnot) (App (Def bnot) (Var 0))) (Var 0))))
   (Ok (CheckedPrf ANil
     (Lam (Con ibool)
       (IndRec ibool
         (Lam (Con ibool)
           (GEq (Con ibool) (App (Def bnot) (App (Def bnot) (Var 0))) (Var 0)))
         (Cases (Case tt (GRfl (Con ibool) (Con tt)))
           (Cases (Case ff (GRfl (Con ibool) (Con ff))) CasesNil))
         (Var 0)))
     (Pi (Con ibool)
       (GEq (Con ibool) (App (Def bnot) (App (Def bnot) (Var 0))) (Var 0))))))

; ==================== EQUALITY ELIMINATION (transport) ======================
; transport iota:  Transp P z z (rfl z) z  reduces to  z
!(assertEqual
   (conv (good-sig)
     (Transp (Lam (Con nat) (Con nat)) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z))
     (Con z))
   True)
; transport infers its result type  (App P b)
!(assertEqual
   (infer (good-sig) CtxNil
     (Transp (Lam (Con nat) (Con nat)) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z)))
   (App (Lam (Con nat) (Con nat)) (Con z)))
; cong-s : Pi a b. eqn a b -> eqn (s a) (s b)  -- DERIVED from transport (not ad hoc),
; checks at its declared type:
!(assertEqual
   (check (good-sig) CtxNil
     (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
       (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
               (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
     (Pi (Con nat) (Pi (Con nat) (Pi (App (App (Con eqn) (Var 1)) (Var 0))
       (App (App (Con eqn) (App (Con s) (Var 2))) (App (Con s) (Var 1)))))))
   True)
; negative: a WRONG congruence target is rejected (eqn (s a)(s b) is NOT eqn a b)
!(assertEqual
   (check (good-sig) CtxNil
     (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
       (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
               (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
     (Pi (Con nat) (Pi (Con nat) (Pi (App (App (Con eqn) (Var 1)) (Var 0))
       (App (App (Con eqn) (Var 2)) (Var 1))))))
   False)
; negative: malformed transport motive (P := nat, not nat -> Type) is rejected
!(assertEqual
   (infer (good-sig) CtxNil
     (Transp (Con nat) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z)))
   (Bad transp-bad-motive))

; negative: Transp iota fires only at matching rfl endpoints.
!(assertEqual
   (conv (good-sig)
     (Transp (Lam (Con nat) (Srt type))
             (Con z)
             (App (Con s) (Con z))
             (App (Con rfl) (Con z))
             (Con nat))
     (Con nat))
   False)

; negative: kernel-check refuses ill-formed expected types instead of normalizing
; them away.  This is the permanent regression probe for the old exploit.
!(assertEqual
   (kernel-check (good-sig)
     (Con z)
     (Transp (Lam (Con nat) (Srt type))
             (Con z)
             (App (Con s) (Con z))
             (App (Con rfl) (Con z))
             (Con nat)))
   (Err check-failed))

; ==================== GENERAL TRANSPORT (type-indexed identity) ==============
; GTransp generalizes transport from nat equality to any carrier A : Type.
!(assertEqual
   (kernel-check (good-sig)
     (GTransp (Con nat)
       (Lam (Con nat) (Con nat))
       (Con z) (Con z)
       (GRfl (Con nat) (Con z))
       (Con z))
     (Con nat))
   (Ok (CheckedPrf ANil
     (GTransp (Con nat)
       (Lam (Con nat) (Con nat))
       (Con z) (Con z)
       (GRfl (Con nat) (Con z))
       (Con z))
     (Con nat))))

; Same primitive over propositions: transporting an axiom proof along reflexive
; proposition equality keeps the axiom provenance visible.
!(assertEqual
   (kernel-check (good-sig)
     (GTransp (Con o)
       (Lam (Con o) (App (Con prf) (Var 0)))
       (App (App (Con In) (Con a)) (Con b))
       (App (App (Con In) (Con a)) (Con b))
       (GRfl (Con o) (App (App (Con In) (Con a)) (Con b)))
       (Con axMem))
     (App (Con prf) (App (App (Con In) (Con a)) (Con b))))
   (Ok (CheckedPrf (ACons axMem ANil)
     (GTransp (Con o)
       (Lam (Con o) (App (Con prf) (Var 0)))
       (App (App (Con In) (Con a)) (Con b))
       (App (App (Con In) (Con a)) (Con b))
       (GRfl (Con o) (App (App (Con In) (Con a)) (Con b)))
       (Con axMem))
     (App (Con prf) (App (App (Con In) (Con a)) (Con b))))))

; negative: general transport does not accept a reflexivity proof at mismatched
; endpoints.
!(assertEqual
   (kernel-check (good-sig)
     (GTransp (Con nat)
       (Lam (Con nat) (Con nat))
       (Con z) (App (Con s) (Con z))
       (GRfl (Con nat) (Con z))
       (Con z))
     (Con nat))
   (Err check-failed))

; ===== INDUCTION:  forall n. plus n z = n  (the curriculum plus_O_r shape) =====
; `plus` recurses on its FIRST arg, so `plus n z` is STUCK for variable n.
; This proof uses generated IndRec nat, not hard-coded NatRec.
(= (cong-s-term)
   (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
     (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
             (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2))))))))

(= (plus-O-r-type)
   (Pi (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))))

(= (plus-O-r-step)
   (Lam (Con nat)
     (Lam (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))
       (App (App (App (cong-s-term) (App (App (Def plus) (Var 1)) (Con z))) (Var 1)) (Var 0)))))

(= (plus-O-r-term)
   (Lam (Con nat)
     (IndRec nat
       (Lam (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0)))
       (Cases (Case z (App (Con rfl) (Con z)))
         (Cases (Case s (plus-O-r-step)) CasesNil))
       (Var 0))))

!(assertEqual
   (check (good-sig) CtxNil (plus-O-r-term) (plus-O-r-type))
   True)

; negative: the FALSE statement  forall n. plus n z = s n  does NOT check (base fails)
(= (false-plus-O-r-type)
   (Pi (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0)))))
(= (false-plus-O-r-term)
   (Lam (Con nat)
     (IndRec nat
       (Lam (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0))))
       (Cases (Case z (App (Con rfl) (Con z)))
         (Cases (Case s
           (Lam (Con nat)
             (Lam (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0)))
               (Var 0)))) CasesNil))
       (Var 0))))
!(assertEqual (check (good-sig) CtxNil (false-plus-O-r-term) (false-plus-O-r-type)) False)

; =============================================================================
; TELESCOPE CONSTRUCTOR PROBES
; =============================================================================
; v1 supports non-indexed constructor telescopes.  Recursive arguments are bare
; occurrences of the carrier; non-recursive arguments are passed to the branch
; without induction hypotheses.

(= (nat-list-base-sig)
   (SCons (DInd nat ParamsNil
     (ICtors (ICtor z (Con nat))
       (ICtors (ICtor s (Pi (Con nat) (Con nat))) ICNil)))
     (SCons (DInd lst ParamsNil
       (ICtors (ICtor lnil (Con lst))
         (ICtors (ICtor lcons (Pi (Con nat) (Pi (Con lst) (Con lst)))) ICNil)))
       SNil)))

!(assertEqual (ctors-strict-pos lst
  (ICtors (ICtor lnil (Con lst))
    (ICtors (ICtor lcons (Pi (Con nat) (Pi (Con lst) (Con lst)))) ICNil)))
  True)
!(assertEqual (ctors-rec-supported lst
  (ICtors (ICtor lnil (Con lst))
    (ICtors (ICtor lcons (Pi (Con nat) (Pi (Con lst) (Con lst)))) ICNil)))
  True)
!(assertEqual (sig-admitted (nat-list-base-sig)) True)

; Branch type for lcons : nat -> lst -> lst:
;   Pi n:nat. Pi xs:lst. Pi ih:P xs. P (lcons n xs)
!(assertEqual
   (rec-branch-type lst
     (Lam (Con lst) (Con nat))
     lcons
     (Pi (Con nat) (Pi (Con lst) (Con lst))))
   (Pi (Con nat)
     (Pi (Con lst)
       (Pi (App (shift 2 0 (Lam (Con lst) (Con nat))) (Var 0))
         (App (shift 3 0 (Lam (Con lst) (Con nat)))
           (App (App (Con lcons) (Var 2)) (Var 1)))))))

; A generated List length eliminator: length (lcons z lnil) computes to s z.
!(assertEqual
   (conv (nat-list-base-sig)
     (IndRec lst
       (Lam (Con lst) (Con nat))
       (Cases (Case lnil (Con z))
         (Cases (Case lcons
           (Lam (Con nat) (Lam (Con lst) (Lam (Con nat) (App (Con s) (Var 0))))))
           CasesNil))
       (App (App (Con lcons) (Con z)) (Con lnil)))
     (App (Con s) (Con z)))
   True)

; Exact case hygiene: an extra unused branch is rejected.
!(assertEqual
   (infer (nat-list-base-sig) CtxNil
     (IndRec lst
       (Lam (Con lst) (Con nat))
       (Cases (Case lnil (Con z))
         (Cases (Case lcons
           (Lam (Con nat) (Lam (Con lst) (Lam (Con nat) (App (Con s) (Var 0))))))
           (Cases (Case ghost (Con z)) CasesNil)))
       (Con lnil)))
   (Bad indrec-bad-cases))

(= (nat-tree-base-sig)
   (SCons (DInd nat ParamsNil
     (ICtors (ICtor z (Con nat))
       (ICtors (ICtor s (Pi (Con nat) (Con nat))) ICNil)))
     (SCons (DInd tree ParamsNil
       (ICtors (ICtor leaf (Pi (Con nat) (Con tree))) ICNil))
       SNil)))

!(assertEqual (ctors-strict-pos tree
  (ICtors (ICtor leaf (Pi (Con nat) (Con tree))) ICNil))
  True)
!(assertEqual (ctors-rec-supported tree
  (ICtors (ICtor leaf (Pi (Con nat) (Con tree))) ICNil))
  True)
!(assertEqual (sig-admitted (nat-tree-base-sig)) True)

; A generated Tree leaf eliminator: leaf carries a non-recursive Nat payload.
!(assertEqual
   (conv (nat-tree-base-sig)
     (IndRec tree
       (Lam (Con tree) (Con nat))
       (Cases (Case leaf (Lam (Con nat) (Var 0))) CasesNil)
       (App (Con leaf) (App (Con s) (Con z))))
     (App (Con s) (Con z)))
   True)
