!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; =============================================================================
; kernel_signature_lf_ind_v0.metta
;
; Runnable v0 inductive_family admission slice over kernel_signature_lf_eq_v0.metta.
;
; New admission form:
;   DInd name ParamsNil (ICtors (ICtor ctorName ctorType) ... ICNil)
;
; Generated/checked in this file:
;   * carrier lookup:      (Con name) : Type
;   * constructor lookup:  ctorName : ctorType
;   * strict positivity for non_parametric constructors
;   * generated recursor term: IndRec ind P cases scrut
;   * generated iota rules for:
;       - nullary constructors      c : I
;       - unary recursive constructor c : I -> I
;
; Demonstrated:
;   * Nat is admitted as DInd, not DConst nat/z/s.
;   * plus is a checked DDef whose body uses IndRec nat, not NatRec.
;   * plus z z = z by computation through generated IndRec.
;   * forall n. plus n z = n checks by generated IndRec induction.
;   * Bool is admitted as DInd with bnot, and forall b. bnot (bnot b) = b checks.
;   * A non_strictly_positive DInd is rejected at admission.
;
; Remaining obligation for the full requested generator:
;   GEq/GRfl/GTransp/Transp and indexed families (Id/J, Vec, parameters,
;   proof_dependent motives) are still hard_coded / not generated here.
;
; Run:
;   /home/aimama/aihub/hyperon/CeTTa/cetta kernel_signature_lf_ind_v0.metta
; =============================================================================

; ---------- list helpers -----------------------------------------------------
(= (is_bad $x) (unify $x (Bad $e) True False))

(= (decl_name (DConst $n $T)) $n)
(= (decl_name (DDef $n $T $body)) $n)
(= (decl_name (DAxiom $n $T)) $n)
(= (decl_name (DInd $n $params $ctors)) $n)

; Inductive_family declarations used in this v0 slice:
;   DInd name ParamsNil (ICtors (ICtor ctorName ctorType) ... ICNil)
; Supported generated recursors:
;   - nullary constructor:        c : I
;   - unary recursive constructor c : I -> I
; This is enough to rederive Nat and Bool without hard_coded NatRec in proofs.

(= (ctor_has_name $n ICNil) False)
(= (ctor_has_name $n (ICtors (ICtor $c $T) $rest))
   (if (== $n $c) True (ctor_has_name $n $rest)))

(= (unique_ctors ICNil) True)
(= (unique_ctors (ICtors (ICtor $c $T) $rest))
   (if (ctor_has_name $c $rest) False (unique_ctors $rest)))

(= (decl_has_name $n (DConst $c $T)) (== $n $c))
(= (decl_has_name $n (DDef $c $T $body)) (== $n $c))
(= (decl_has_name $n (DAxiom $c $T)) (== $n $c))
(= (decl_has_name $n (DInd $i $params $ctors))
   (if (== $n $i) True (ctor_has_name $n $ctors)))

(= (sig_has_name $n SNil) False)
(= (sig_has_name $n (SCons $d $rest))
   (if (decl_has_name $n $d) True (sig_has_name $n $rest)))

(= (decl_names_disjoint_rest (DConst $n $T) $rest) (if (sig_has_name $n $rest) False True))
(= (decl_names_disjoint_rest (DDef $n $T $body) $rest) (if (sig_has_name $n $rest) False True))
(= (decl_names_disjoint_rest (DAxiom $n $T) $rest) (if (sig_has_name $n $rest) False True))
(= (ctors_disjoint_rest ICNil $rest) True)
(= (ctors_disjoint_rest (ICtors (ICtor $c $T) $cs) $rest)
   (if (sig_has_name $c $rest) False (ctors_disjoint_rest $cs $rest)))
(= (decl_names_disjoint_rest (DInd $n $params $ctors) $rest)
   (if (sig_has_name $n $rest) False
     (if (unique_ctors $ctors) (ctors_disjoint_rest $ctors $rest) False)))

(= (unique_sig SNil) True)
(= (unique_sig (SCons $d $rest))
   (if (decl_names_disjoint_rest $d $rest) (unique_sig $rest) False))

(= (ax_union ANil $ys) $ys)
(= (ax_union (ACons $x $xs) $ys) (ACons $x (ax_union $xs $ys)))

; ---------- finite signature lookup -----------------------------------------
; Declarations:
;   DConst name type    -- checked constant/constructor
;   DDef   name type body -- checked definition, unfolds during normalization
;   DAxiom name type    -- unchecked postulate, visible in theorem provenance

(= (ctor_type_of ICNil $x) (Bad unknown_constructor))
(= (ctor_type_of (ICtors (ICtor $c $T) $rest) $x)
   (if (== $x $c) $T (ctor_type_of $rest $x)))

(= (ind_ctors_of SNil $x) (Bad unknown_inductive))
(= (ind_ctors_of (SCons (DInd $i $params $ctors) $rest) $x)
   (if (== $x $i) $ctors (ind_ctors_of $rest $x)))
(= (ind_ctors_of (SCons (DConst $c $T) $rest) $x) (ind_ctors_of $rest $x))
(= (ind_ctors_of (SCons (DDef $c $T $body) $rest) $x) (ind_ctors_of $rest $x))
(= (ind_ctors_of (SCons (DAxiom $c $T) $rest) $x) (ind_ctors_of $rest $x))

(= (decl_type_of SNil $c) (Bad unknown_declaration))
(= (decl_type_of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (decl_type_of $rest $x)))
(= (decl_type_of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (decl_type_of $rest $x)))
(= (decl_type_of (SCons (DAxiom $c $T) $rest) $x)
   (if (== $x $c) $T (decl_type_of $rest $x)))
(= (decl_type_of (SCons (DInd $i $params ICNil) $rest) $x)
   (if (== $x $i) (Srt type) (decl_type_of $rest $x)))
(= (decl_type_of (SCons (DInd $i $params (ICtors (ICtor $c $T) $ctors)) $rest) $x)
   (if (== $x $i) (Srt type)
     (if (== $x $c) $T
       (decl_type_of (SCons (DInd $i $params $ctors) $rest) $x))))

(= (def_body_of SNil $c) (Bad unknown_definition))
(= (def_body_of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $body (def_body_of $rest $x)))
(= (def_body_of (SCons (DConst $c $T) $rest) $x) (def_body_of $rest $x))
(= (def_body_of (SCons (DAxiom $c $T) $rest) $x) (def_body_of $rest $x))
(= (def_body_of (SCons (DInd $i $params $ctors) $rest) $x) (def_body_of $rest $x))

(= (is_axiom_name SNil $x) False)
(= (is_axiom_name (SCons (DAxiom $a $T) $rest) $x)
   (if (== $x $a) True (is_axiom_name $rest $x)))
(= (is_axiom_name (SCons (DConst $c $T) $rest) $x) (is_axiom_name $rest $x))
(= (is_axiom_name (SCons (DDef $c $T $body) $rest) $x) (is_axiom_name $rest $x))
(= (is_axiom_name (SCons (DInd $i $params $ctors) $rest) $x) (is_axiom_name $rest $x))

; ---------- lambda_Pi term machinery ----------------------------------------
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
   (IndRec $ind (shift $d $c $P) (shift_cases $d $c $cases) (shift $d $c $n)))
(= (shift $d $c (GEq $A $a $b))
   (GEq (shift $d $c $A) (shift $d $c $a) (shift $d $c $b)))
(= (shift $d $c (GRfl $A $a))
   (GRfl (shift $d $c $A) (shift $d $c $a)))
(= (shift $d $c (Transp $P $a $b $p $x))
   (Transp (shift $d $c $P) (shift $d $c $a) (shift $d $c $b) (shift $d $c $p) (shift $d $c $x)))
(= (shift $d $c (GTransp $A $P $a $b $p $x))
   (GTransp (shift $d $c $A) (shift $d $c $P) (shift $d $c $a) (shift $d $c $b) (shift $d $c $p) (shift $d $c $x)))
(= (shift $d $c (Bad $e)) (Bad $e))
(= (shift_cases $d $c CasesNil) CasesNil)
(= (shift_cases $d $c (Cases (Case $ctor $body) $rest))
   (Cases (Case $ctor (shift $d $c $body)) (shift_cases $d $c $rest)))

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
   (IndRec $ind (subst $j $s $P) (subst_cases $j $s $cases) (subst $j $s $n)))
(= (subst $j $s (GEq $A $a $b))
   (GEq (subst $j $s $A) (subst $j $s $a) (subst $j $s $b)))
(= (subst $j $s (GRfl $A $a))
   (GRfl (subst $j $s $A) (subst $j $s $a)))
(= (subst $j $s (Transp $P $a $b $p $x))
   (Transp (subst $j $s $P) (subst $j $s $a) (subst $j $s $b) (subst $j $s $p) (subst $j $s $x)))
(= (subst $j $s (GTransp $A $P $a $b $p $x))
   (GTransp (subst $j $s $A) (subst $j $s $P) (subst $j $s $a) (subst $j $s $b) (subst $j $s $p) (subst $j $s $x)))
(= (subst $j $s (Bad $e)) (Bad $e))
(= (subst_cases $j $s CasesNil) CasesNil)
(= (subst_cases $j $s (Cases (Case $ctor $body) $rest))
   (Cases (Case $ctor (subst $j $s $body)) (subst_cases $j $s $rest)))

(= (nf $sig (Var $k)) (Var $k))
(= (nf $sig (Srt $s)) (Srt $s))
(= (nf $sig (Con $x)) (Con $x))
(= (nf $sig (Def $x))
   (let $body (def_body_of $sig $x)
     (if (is_bad $body) (Bad unknown_definition) (nf $sig $body))))
(= (nf $sig (Pi  $A $B)) (Pi  (nf $sig $A) (nf $sig $B)))
(= (nf $sig (Lam $A $b)) (Lam (nf $sig $A) (nf $sig $b)))
(= (nf $sig (NatRec $P $zcase $scase $n))
   (nf_natrec $sig (nf $sig $P) (nf $sig $zcase) (nf $sig $scase) (nf $sig $n)))
(= (nf $sig (IndRec $ind $P $cases $n))
   (nf_indrec $sig $ind (nf $sig $P) (nf_cases $sig $cases) (nf $sig $n)))
(= (nf $sig (GEq $A $a $b))
   (GEq (nf $sig $A) (nf $sig $a) (nf $sig $b)))
(= (nf $sig (GRfl $A $a))
   (GRfl (nf $sig $A) (nf $sig $a)))
(= (nf $sig (Transp $P $a $b $p $x))
   (nf_transp $sig (nf $sig $P) (nf $sig $a) (nf $sig $b) (nf $sig $p) (nf $sig $x)))
(= (nf $sig (GTransp $A $P $a $b $p $x))
   (nf_gtransp $sig (nf $sig $A) (nf $sig $P) (nf $sig $a) (nf $sig $b) (nf $sig $p) (nf $sig $x)))
(= (nf $sig (Bad $e)) (Bad $e))
(= (nf_cases $sig CasesNil) CasesNil)
(= (nf_cases $sig (Cases (Case $ctor $body) $rest))
   (Cases (Case $ctor (nf $sig $body)) (nf_cases $sig $rest)))
(= (nf $sig (App $f $a)) (nf_app $sig (nf $sig $f) (nf $sig $a)))
(= (nf_app $sig $f $a) (unify $f (Lam $A $b) (nf $sig (subst 0 $a $b)) (App $f $a)))
(= (nf_natrec $sig $P $zcase $scase $n)
   (unify $n (Con z)
     $zcase
     (unify $n (App (Con s) $k)
       (nf $sig (App (App $scase $k) (NatRec $P $zcase $scase $k)))
       (NatRec $P $zcase $scase $n))))

(= (case_body_of CasesNil $ctor) (Bad missing_case))
(= (case_body_of (Cases (Case $c $body) $rest) $ctor)
   (if (== $c $ctor) $body (case_body_of $rest $ctor)))

(= (nf_indrec $sig $ind $P $cases $n)
   (unify $n (Con $ctor)
     (let $ctors (ind_ctors_of $sig $ind)
       (let $CT (ctor_type_of $ctors $ctor)
         (unify $CT (Con $ind)
           (case_body_of $cases $ctor)
           (IndRec $ind $P $cases $n))))
     (unify $n (App (Con $ctor) $k)
       (let $ctors (ind_ctors_of $sig $ind)
         (let $CT (ctor_type_of $ctors $ctor)
           (unify $CT (Pi (Con $ind) (Con $ind))
             (nf $sig (App (App (case_body_of $cases $ctor) $k) (IndRec $ind $P $cases $k)))
             (IndRec $ind $P $cases $n))))
       (IndRec $ind $P $cases $n))))
(= (nf_transp $sig $P $a $b $p $x)
   (unify $p (App (Con rfl) $k)
     (if (== $a $k)
       (if (== $b $k) $x (Transp $P $a $b $p $x))
       (Transp $P $a $b $p $x))
     (Transp $P $a $b $p $x)))
(= (nf_gtransp $sig $A $P $a $b $p $x)
   (unify $p (GRfl $A0 $k)
     (if (== $A $A0)
       (if (== $a $k)
         (if (== $b $k) $x (GTransp $A $P $a $b $p $x))
         (GTransp $A $P $a $b $p $x))
       (GTransp $A $P $a $b $p $x))
     (GTransp $A $P $a $b $p $x)))

(= (conv $sig $x $y)
   (if (is_bad (nf $sig $x)) False
     (if (is_bad (nf $sig $y)) False
       (== (nf $sig $x) (nf $sig $y)))))

(= (ctx_nth $i CtxNil) (Bad var_out_of_range))
(= (ctx_nth $i (CtxCons $h $t)) (if (== $i 0) $h (ctx_nth (- $i 1) $t)))
(= (ctx_type $i $ctx) (shift (+ $i 1) 0 (ctx_nth $i $ctx)))

(= (pts_rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi_bad_codomain)))
     (Bad pi_domain_not_type)))

(= (infer $sig $ctx (Srt type)) (Srt kind))
(= (infer $sig $ctx (Srt kind)) (Bad kind_is_topsort))
(= (infer $sig $ctx (Bad $e)) (Bad $e))
(= (infer $sig $ctx (Var $i))  (ctx_type $i $ctx))
(= (infer $sig $ctx (Con $c))  (decl_type_of $sig $c))
(= (infer $sig $ctx (Def $c))  (decl_type_of $sig $c))
(= (infer $sig $ctx (Pi $A $B))
   (let $sA (nf $sig (infer $sig $ctx $A))
     (let $sB (nf $sig (infer $sig (CtxCons $A $ctx) $B)) (pts_rule $sA $sB))))
(= (infer_lam $sig $ctx $A $b)
   (let $sA (nf $sig (infer $sig $ctx $A))
     (unify $sA (Srt type)
        (let $tb (infer $sig (CtxCons $A $ctx) $b)
          (let $ntb (nf $sig $tb)
            (let $bad (is_bad $ntb)
              (if $bad (Bad lam_body_bad_type) (Pi $A $tb)))))
        (Bad lam_domain_not_a_type))))
(= (infer $sig $ctx (Lam $A $b)) (infer_lam $sig $ctx $A $b))
(= (infer_app $sig $ctx $f $a)
   (let $tf (nf $sig (infer $sig $ctx $f))
     (unify $tf (Pi $A $B)
        (if (conv $sig (infer $sig $ctx $a) $A) (subst 0 $a $B) (Bad arg_type_mismatch))
        (Bad applied_a_non_function))))
(= (infer $sig $ctx (App $f $a)) (infer_app $sig $ctx $f $a))
(= (natrec_step_type $P)
   (Pi (Con nat)
     (Pi (App (shift 1 0 $P) (Var 0))
       (App (shift 2 0 $P) (App (Con s) (Var 1))))))
(= (infer_natrec $sig $ctx $P $zcase $scase $n)
   (if (check_conv $sig $ctx $P (Pi (Con nat) (Srt type)))
     (if (check_conv $sig $ctx $zcase (App $P (Con z)))
       (if (check_conv $sig $ctx $scase (natrec_step_type $P))
         (if (check_conv $sig $ctx $n (Con nat))
           (App $P $n)
           (Bad natrec_scrutinee_not_nat))
         (Bad natrec_bad_step))
       (Bad natrec_bad_zero))
     (Bad natrec_bad_motive)))
(= (infer $sig $ctx (NatRec $P $zcase $scase $n)) (infer_natrec $sig $ctx $P $zcase $scase $n))

(= (rec_branch_type $ind $P $ctor $T)
   (unify $T (Con $ind)
     (App $P (Con $ctor))
     (unify $T (Pi (Con $ind) (Con $ind))
       (Pi (Con $ind)
         (Pi (App (shift 1 0 $P) (Var 0))
           (App (shift 2 0 $P) (App (Con $ctor) (Var 1)))))
       (Bad unsupported_constructor_shape))))

(= (cases_check $sig $ctx $ind $P ICNil $cases) True)
(= (cases_check $sig $ctx $ind $P (ICtors (ICtor $ctor $CT) $rest) $cases)
   (let $body (case_body_of $cases $ctor)
     (if (is_bad $body) False
       (if (check_conv $sig $ctx $body (rec_branch_type $ind $P $ctor $CT))
         (cases_check $sig $ctx $ind $P $rest $cases)
         False))))

(= (infer_indrec $sig $ctx $ind $P $cases $n)
   (let $ctors (ind_ctors_of $sig $ind)
     (if (is_bad $ctors)
       (Bad unknown_inductive)
       (if (check_conv $sig $ctx (Con $ind) (Srt type))
         (if (check_conv $sig $ctx $P (Pi (Con $ind) (Srt type)))
           (if (cases_check $sig $ctx $ind $P $ctors $cases)
             (if (check_conv $sig $ctx $n (Con $ind))
               (App $P $n)
               (Bad indrec_bad_scrutinee))
             (Bad indrec_bad_cases))
           (Bad indrec_bad_motive))
         (Bad indrec_bad_carrier)))))
(= (infer $sig $ctx (IndRec $ind $P $cases $n)) (infer_indrec $sig $ctx $ind $P $cases $n))
(= (infer_geq $sig $ctx $A $a $b)
   (if (check_conv $sig $ctx $A (Srt type))
     (if (check_conv $sig $ctx $a $A)
       (if (check_conv $sig $ctx $b $A)
         (Srt type)
         (Bad geq_bad_right))
       (Bad geq_bad_left))
     (Bad geq_bad_carrier)))
(= (infer $sig $ctx (GEq $A $a $b)) (infer_geq $sig $ctx $A $a $b))
(= (infer_grfl $sig $ctx $A $a)
   (if (check_conv $sig $ctx $A (Srt type))
     (if (check_conv $sig $ctx $a $A)
       (GEq $A $a $a)
       (Bad grfl_bad_term))
     (Bad grfl_bad_carrier)))
(= (infer $sig $ctx (GRfl $A $a)) (infer_grfl $sig $ctx $A $a))
(= (infer_transp $sig $ctx $P $a $b $p $x)
   (if (check_conv $sig $ctx $P (Pi (Con nat) (Srt type)))
     (if (check_conv $sig $ctx $a (Con nat))
       (if (check_conv $sig $ctx $b (Con nat))
         (if (check_conv $sig $ctx $p (App (App (Con eqn) $a) $b))
           (if (check_conv $sig $ctx $x (App $P $a))
             (App $P $b)
             (Bad transp_bad_elem))
           (Bad transp_bad_proof))
         (Bad transp_bad_b))
       (Bad transp_bad_a))
     (Bad transp_bad_motive)))
(= (infer $sig $ctx (Transp $P $a $b $p $x)) (infer_transp $sig $ctx $P $a $b $p $x))
(= (infer_gtransp $sig $ctx $A $P $a $b $p $x)
   (if (check_conv $sig $ctx $A (Srt type))
     (if (check_conv $sig $ctx $P (Pi $A (Srt type)))
       (if (check_conv $sig $ctx $a $A)
         (if (check_conv $sig $ctx $b $A)
           (if (check_conv $sig $ctx $p (GEq $A $a $b))
             (if (check_conv $sig $ctx $x (App $P $a))
               (App $P $b)
               (Bad gtransp_bad_elem))
             (Bad gtransp_bad_proof))
           (Bad gtransp_bad_b))
         (Bad gtransp_bad_a))
       (Bad gtransp_bad_motive))
     (Bad gtransp_bad_carrier)))
(= (infer $sig $ctx (GTransp $A $P $a $b $p $x)) (infer_gtransp $sig $ctx $A $P $a $b $p $x))
(= (sort_ok $s)
   (unify $s (Srt type) True
     (unify $s (Srt kind) True False)))
(= (type_ok $sig $ctx $ty)
   (let $ITY (infer $sig $ctx $ty)
     (let $S (nf $sig $ITY) (sort_ok $S))))
(= (check_conv $sig $ctx $t $ty) (conv $sig (infer $sig $ctx $t) $ty))
(= (check $sig $ctx $t $ty)
   (let $okTy (type_ok $sig $ctx $ty)
     (if $okTy (check_conv $sig $ctx $t $ty) False)))
(= (check_result $sig $ctx $t $ty) (check $sig $ctx $t $ty))

; ---------- signature admission ---------------------------------------------
(= (term_occurs_name $n (Var $k)) False)
(= (term_occurs_name $n (Srt $s)) False)
(= (term_occurs_name $n (Con $c)) (== $n $c))
(= (term_occurs_name $n (Def $c)) (== $n $c))
(= (term_occurs_name $n (App $f $a))
   (if (term_occurs_name $n $f) True (term_occurs_name $n $a)))
(= (term_occurs_name $n (Pi $A $B))
   (if (term_occurs_name $n $A) True (term_occurs_name $n $B)))
(= (term_occurs_name $n (Lam $A $b))
   (if (term_occurs_name $n $A) True (term_occurs_name $n $b)))
(= (term_occurs_name $n (NatRec $P $zcase $scase $scrut)) True)
(= (term_occurs_name $n (IndRec $ind $P $cases $scrut)) True)
(= (term_occurs_name $n (GEq $A $a $b))
   (if (term_occurs_name $n $A) True (if (term_occurs_name $n $a) True (term_occurs_name $n $b))))
(= (term_occurs_name $n (GRfl $A $a))
   (if (term_occurs_name $n $A) True (term_occurs_name $n $a)))
(= (term_occurs_name $n (Transp $P $a $b $p $x)) True)
(= (term_occurs_name $n (GTransp $A $P $a $b $p $x)) True)
(= (term_occurs_name $n (Bad $e)) False)

(= (strict_pos_arg $ind $A)
   (unify $A (Con $ind)
     True
     (if (term_occurs_name $ind $A) False True)))
(= (strict_pos_ctor_type $ind $T)
   (unify $T (Con $ind)
     True
     (unify $T (Pi $A $B)
       (if (strict_pos_arg $ind $A) (strict_pos_ctor_type $ind $B) False)
       False)))
(= (ctors_strict_pos $ind ICNil) True)
(= (ctors_strict_pos $ind (ICtors (ICtor $c $T) $rest))
   (if (strict_pos_ctor_type $ind $T) (ctors_strict_pos $ind $rest) False))

; v0 recursor coverage: admission and elimination must agree.  Until the
; generator supports more shapes, admit only constructors whose branch/iota
; schema exists in rec_branch_type/nf_indrec.
(= (rec_supported_ctor_type $ind $T)
   (unify $T (Con $ind)
     True
     (unify $T (Pi (Con $ind) (Con $ind)) True False)))
(= (ctors_rec_supported $ind ICNil) True)
(= (ctors_rec_supported $ind (ICtors (ICtor $c $T) $rest))
   (if (rec_supported_ctor_type $ind $T) (ctors_rec_supported $ind $rest) False))

(= (ctors_types_ok $prefix ICNil) True)
(= (ctors_types_ok $prefix (ICtors (ICtor $c $T) $rest))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT)
       (if (sort_ok $S) (ctors_types_ok $prefix $rest) False))))

(= (wf_decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT)
       (sort_ok $S))))
(= (wf_decl $prefix (DDef $n $T $body))
   (let $okT (wf_decl $prefix (DConst $n $T))
     (if $okT (check_conv $prefix CtxNil $body $T) False)))
(= (wf_decl $prefix (DAxiom $n $T)) (wf_decl $prefix (DConst $n $T)))
(= (wf_decl $prefix (DInd $n ParamsNil $ctors))
   (if (unique_ctors $ctors)
     (if (ctors_strict_pos $n $ctors)
       (if (ctors_rec_supported $n $ctors)
         (ctors_types_ok (SCons (DConst $n (Srt type)) $prefix) $ctors)
         False)
       False)
     False))

(= (wf_sig_prefix $prefix SNil) True)
(= (wf_sig_prefix $prefix (SCons $d $rest))
   (let $ok (wf_decl $prefix $d)
     (if $ok
       (wf_sig_prefix (SCons $d $prefix) $rest)
       False)))

(= (sig_admitted $sig)
   (let $u (unique_sig $sig)
     (if $u (wf_sig_prefix SNil $sig) False)))

; ---------- theorem provenance over checked proof terms ----------------------
(= (term_axioms $sig (Var $k)) ANil)
(= (term_axioms $sig (Srt $s)) ANil)
(= (term_axioms $sig (Con $c))
   (if (is_axiom_name $sig $c) (ACons $c ANil) ANil))
(= (term_axioms $sig (Def $c)) ANil)
(= (term_axioms $sig (Pi $A $B)) (ax_union (term_axioms $sig $A) (term_axioms $sig $B)))
(= (term_axioms $sig (Lam $A $b)) (ax_union (term_axioms $sig $A) (term_axioms $sig $b)))
(= (term_axioms $sig (App $f $a)) (ax_union (term_axioms $sig $f) (term_axioms $sig $a)))
(= (term_axioms $sig (NatRec $P $zcase $scase $n))
   (ax_union (term_axioms $sig $P)
     (ax_union (term_axioms $sig $zcase)
       (ax_union (term_axioms $sig $scase) (term_axioms $sig $n)))))
(= (term_axioms $sig (IndRec $ind $P $cases $n))
   (ax_union (term_axioms $sig $P)
     (ax_union (term_axioms_cases $sig $cases) (term_axioms $sig $n))))
(= (term_axioms_cases $sig CasesNil) ANil)
(= (term_axioms_cases $sig (Cases (Case $ctor $body) $rest))
   (ax_union (term_axioms $sig $body) (term_axioms_cases $sig $rest)))
(= (term_axioms $sig (GEq $A $a $b))
   (ax_union (term_axioms $sig $A)
     (ax_union (term_axioms $sig $a) (term_axioms $sig $b))))
(= (term_axioms $sig (GRfl $A $a))
   (ax_union (term_axioms $sig $A) (term_axioms $sig $a)))
(= (term_axioms $sig (Transp $P $a $b $p $x))
   (ax_union (term_axioms $sig $P)
     (ax_union (term_axioms $sig $a)
       (ax_union (term_axioms $sig $b)
         (ax_union (term_axioms $sig $p) (term_axioms $sig $x))))))
(= (term_axioms $sig (GTransp $A $P $a $b $p $x))
   (ax_union (term_axioms $sig $A)
     (ax_union (term_axioms $sig $P)
       (ax_union (term_axioms $sig $a)
         (ax_union (term_axioms $sig $b)
           (ax_union (term_axioms $sig $p) (term_axioms $sig $x)))))))
(= (term_axioms $sig (Bad $e)) ANil)

(= (kernel_check_checked $sig $term $type True)
   (let $uses (term_axioms $sig $term)
     (Ok (CheckedPrf $uses $term $type))))
(= (kernel_check_checked $sig $term $type False) (Err check_failed))
(= (kernel_check_admitted $sig $term $type True)
   (kernel_check_checked $sig $term $type (check_result $sig CtxNil $term $type)))
(= (kernel_check_admitted $sig $term $type False) (Err signature_not_admitted))
(= (kernel_check $sig $term $type)
   (case (sig_admitted $sig)
     ((True (kernel_check_checked $sig $term $type (check_result $sig CtxNil $term $type)))
      (False (Err signature_not_admitted)))))

; ---------- finite curriculum signature --------------------------------------
(= (good_sig)
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

(= (bad_def_sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst A (Con o))
   (SCons (DConst falseP (Con o))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DDef defAsPrf (App (Con prf) (Con falseP)) (Con A))
          SNil))))))

(= (dup_sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst o (Srt type))
          SNil)))

(= (forward_ref_sig)
   (SCons (DDef useLater (Con later) (Con later))
   (SCons (DConst later (Srt type))
          SNil)))

(= (inconsistent_ledger_sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DConst falseP (Con o))
   (SCons (DConst B (Con o))
   (SCons (DConst falseE
     (Pi (App (Con prf) (Con falseP)) (Pi (Con o) (App (Con prf) (Var 0)))))
   (SCons (DAxiom boom (App (Con prf) (Con falseP)))
          SNil)))))))

; ---------- admission regressions -------------------------------------------
!(test (sig_admitted (good_sig)) True)
!(test (sig_admitted (bad_def_sig)) False)
!(test (sig_admitted (dup_sig)) False)
!(test (sig_admitted (forward_ref_sig)) False)
!(test (sig_admitted (inconsistent_ledger_sig)) True)

; Bad is not a type.
!(test (infer (good_sig) CtxNil (Lam (Srt type) (Var 0))) (Bad lam_domain_not_a_type))
!(test (check (good_sig) CtxNil (Lam (Con o) (Srt kind)) (Pi (Con o) (Bad kind_is_topsort))) False)

; Delta conversion through an admitted definition.
!(test (conv (good_sig) (App (Def holds) (Con A)) (App (Con prf) (Con A))) True)

; Entry examples: DTT rfl, HOL implication proofs, beta, HOTG axiom composition.
!(test
   (kernel_check (good_sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (Con z)))
   (Ok (CheckedPrf ANil (App (Con rfl) (Con z)) (App (App (Con eqn) (Con z)) (Con z)))))

!(test
   (kernel_check (good_sig)
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))
   (Ok (CheckedPrf ANil
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))))

!(test
   (kernel_check (good_sig)
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

!(test
   (kernel_check (good_sig)
     (App (Lam (Con nat) (Var 0)) (Con z))
     (Con nat))
   (Ok (CheckedPrf ANil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))))

; NatRec is a real dependent eliminator, not an opaque constant.
!(test
   (infer (good_sig) CtxNil
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z)))
   (App (Lam (Con nat) (Con nat)) (Con z)))

; Iota at zero: NatRec P z s z reduces to the zero case.
!(test
   (conv (good_sig)
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z))
     (Con z))
   True)

; Iota at successor: NatRec P z s (s z) reduces by one successor step.
!(test
   (conv (good_sig)
     (NatRec
       (Lam (Con nat) (Con nat))
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

; plus is admitted only because its body checks against nat -> nat -> nat.
!(test
   (conv (good_sig)
     (App (App (Def plus) (Con z)) (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

!(test
   (conv (good_sig)
     (App (App (Def plus) (App (Con s) (Con z))) (Con z))
     (App (Con s) (Con z)))
   True)

; The old Exp2 wall is closed for concrete plus_zero by computation: rfl now checks.
!(test
   (kernel_check (good_sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Def plus) (Con z)) (Con z))) (Con z)))
   (Ok (CheckedPrf ANil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Def plus) (Con z)) (Con z))) (Con z)))))

; Negative: the motive must be nat -> Type.
!(test
   (infer (good_sig) CtxNil
     (NatRec
       (Con nat)
       (Con z)
       (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
       (Con z)))
   (Bad natrec_bad_motive))

!(test
   (kernel_check (good_sig)
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
!(test
   (kernel_check (bad_def_sig) (Def defAsPrf) (App (Con prf) (Con falseP)))
   (Err signature_not_admitted))

!(test
   (kernel_check (inconsistent_ledger_sig)
     (App (App (Con falseE) (Con boom)) (Con B))
     (App (Con prf) (Con B)))
   (Ok (CheckedPrf (ACons boom ANil)
     (App (App (Con falseE) (Con boom)) (Con B))
     (App (Con prf) (Con B)))))

; Wrong proof targets still reject.
!(test
   (kernel_check (good_sig)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (App (Con s) (Con z))))
   (Err check_failed))

!(test
   (kernel_check (good_sig)
     (App (App (App (Con impI) (Con A)) (Con A)) (Lam (App (Con prf) (Con A)) (Var 0)))
     (App (Con prf) (App (App (Con imp) (Con A)) (Con B))))
   (Err check_failed))


; ==================== GENERATED INDUCTIVE ADMISSION SLICE ===================
; Nat is no longer declared via DConst nat/z/s in good_sig.  DInd generates the
; carrier and constructor lookup, and IndRec checks using the generated recursor
; branch types.
!(test (decl_type_of (good_sig) nat) (Srt type))
!(test (decl_type_of (good_sig) z) (Con nat))
!(test (decl_type_of (good_sig) s) (Pi (Con nat) (Con nat)))

(= (bad_ind_sig)
   (SCons (DInd bad ParamsNil
     (ICtors (ICtor mkBad (Pi (Pi (Con bad) (Con bad)) (Con bad))) ICNil))
          SNil))
!(test (sig_admitted (bad_ind_sig)) False)

; Generic generated Nat recursor iota, zero and successor.
!(test
   (conv (good_sig)
     (IndRec nat
       (Lam (Con nat) (Con nat))
       (Cases (Case z (Con z))
         (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
       (Con z))
     (Con z))
   True)

!(test
   (conv (good_sig)
     (IndRec nat
       (Lam (Con nat) (Con nat))
       (Cases (Case z (Con z))
         (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
       (App (Con s) (Con z)))
     (App (Con s) (Con z)))
   True)

; New generated Bool inductive + generated recursor + worked proof:
; forall b:ibool. bnot (bnot b) = b, by IndRec over Bool.
!(test (decl_type_of (good_sig) ibool) (Srt type))
!(test (decl_type_of (good_sig) tt) (Con ibool))
!(test (conv (good_sig) (App (Def bnot) (Con tt)) (Con ff)) True)
!(test
   (kernel_check (good_sig)
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
!(test
   (conv (good_sig)
     (Transp (Lam (Con nat) (Con nat)) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z))
     (Con z))
   True)
; transport infers its result type  (App P b)
!(test
   (infer (good_sig) CtxNil
     (Transp (Lam (Con nat) (Con nat)) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z)))
   (App (Lam (Con nat) (Con nat)) (Con z)))
; cong_s : Pi a b. eqn a b -> eqn (s a) (s b)  -- DERIVED from transport (not ad hoc),
; checks at its declared type:
!(test
   (check (good_sig) CtxNil
     (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
       (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
               (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
     (Pi (Con nat) (Pi (Con nat) (Pi (App (App (Con eqn) (Var 1)) (Var 0))
       (App (App (Con eqn) (App (Con s) (Var 2))) (App (Con s) (Var 1)))))))
   True)
; negative: a WRONG congruence target is rejected (eqn (s a)(s b) is NOT eqn a b)
!(test
   (check (good_sig) CtxNil
     (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
       (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
               (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2)))))))
     (Pi (Con nat) (Pi (Con nat) (Pi (App (App (Con eqn) (Var 1)) (Var 0))
       (App (App (Con eqn) (Var 2)) (Var 1))))))
   False)
; negative: malformed transport motive (P := nat, not nat -> Type) is rejected
!(test
   (infer (good_sig) CtxNil
     (Transp (Con nat) (Con z) (Con z) (App (Con rfl) (Con z)) (Con z)))
   (Bad transp_bad_motive))

; negative: Transp iota fires only at matching rfl endpoints.
!(test
   (conv (good_sig)
     (Transp (Lam (Con nat) (Srt type))
             (Con z)
             (App (Con s) (Con z))
             (App (Con rfl) (Con z))
             (Con nat))
     (Con nat))
   False)

; negative: kernel_check refuses ill_formed expected types instead of normalizing
; them away.  This is the permanent regression probe for the old exploit.
!(test
   (kernel_check (good_sig)
     (Con z)
     (Transp (Lam (Con nat) (Srt type))
             (Con z)
             (App (Con s) (Con z))
             (App (Con rfl) (Con z))
             (Con nat)))
   (Err check_failed))

; ==================== GENERAL TRANSPORT (type_indexed identity) ==============
; GTransp generalizes transport from nat equality to any carrier A : Type.
!(test
   (kernel_check (good_sig)
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
!(test
   (kernel_check (good_sig)
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
!(test
   (kernel_check (good_sig)
     (GTransp (Con nat)
       (Lam (Con nat) (Con nat))
       (Con z) (App (Con s) (Con z))
       (GRfl (Con nat) (Con z))
       (Con z))
     (Con nat))
   (Err check_failed))

; ===== INDUCTION:  forall n. plus n z = n  (the curriculum plus_O_r shape) =====
; `plus` recurses on its FIRST arg, so `plus n z` is STUCK for variable n.
; This proof uses generated IndRec nat, not hard_coded NatRec.
(= (cong_s_term)
   (Lam (Con nat) (Lam (Con nat) (Lam (App (App (Con eqn) (Var 1)) (Var 0))
     (Transp (Lam (Con nat) (App (App (Con eqn) (App (Con s) (Var 3))) (App (Con s) (Var 0))))
             (Var 2) (Var 1) (Var 0) (App (Con rfl) (App (Con s) (Var 2))))))))

(= (plus_O_r_type)
   (Pi (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))))

(= (plus_O_r_step)
   (Lam (Con nat)
     (Lam (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0))
       (App (App (App (cong_s_term) (App (App (Def plus) (Var 1)) (Con z))) (Var 1)) (Var 0)))))

(= (plus_O_r_term)
   (Lam (Con nat)
     (IndRec nat
       (Lam (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (Var 0)))
       (Cases (Case z (App (Con rfl) (Con z)))
         (Cases (Case s (plus_O_r_step)) CasesNil))
       (Var 0))))

!(test
   (check (good_sig) CtxNil (plus_O_r_term) (plus_O_r_type))
   True)

; negative: the FALSE statement  forall n. plus n z = s n  does NOT check (base fails)
(= (false_plus_O_r_type)
   (Pi (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0)))))
(= (false_plus_O_r_term)
   (Lam (Con nat)
     (IndRec nat
       (Lam (Con nat) (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0))))
       (Cases (Case z (App (Con rfl) (Con z)))
         (Cases (Case s
           (Lam (Con nat)
             (Lam (App (App (Con eqn) (App (App (Def plus) (Var 0)) (Con z))) (App (Con s) (Var 0)))
               (Var 0)))) CasesNil))
       (Var 0))))
!(test (check (good_sig) CtxNil (false_plus_O_r_term) (false_plus_O_r_type)) False)

; =============================================================================
; ADMISSION/ELIMINATOR LOCKSTEP PROBES
; =============================================================================
; v0 supports exactly nullary and unary_recursive constructors.  Strictly
; positive inductives outside that fragment must not be marked admitted until
; the recursor generator can eliminate them.

(= (nat_list_base_sig)
   (SCons (DInd nat ParamsNil
     (ICtors (ICtor z (Con nat))
       (ICtors (ICtor s (Pi (Con nat) (Con nat))) ICNil)))
     (SCons (DInd lst ParamsNil
       (ICtors (ICtor lnil (Con lst))
         (ICtors (ICtor lcons (Pi (Con nat) (Pi (Con lst) (Con lst)))) ICNil)))
       SNil)))

!(test (ctors_strict_pos lst
  (ICtors (ICtor lnil (Con lst))
    (ICtors (ICtor lcons (Pi (Con nat) (Pi (Con lst) (Con lst)))) ICNil)))
  True)
!(test (ctors_rec_supported lst
  (ICtors (ICtor lnil (Con lst))
    (ICtors (ICtor lcons (Pi (Con nat) (Pi (Con lst) (Con lst)))) ICNil)))
  False)
!(test (sig_admitted (nat_list_base_sig)) False)

(= (nat_tree_base_sig)
   (SCons (DInd nat ParamsNil
     (ICtors (ICtor z (Con nat))
       (ICtors (ICtor s (Pi (Con nat) (Con nat))) ICNil)))
     (SCons (DInd tree ParamsNil
       (ICtors (ICtor leaf (Pi (Con nat) (Con tree))) ICNil))
       SNil)))

!(test (ctors_strict_pos tree
  (ICtors (ICtor leaf (Pi (Con nat) (Con tree))) ICNil))
  True)
!(test (ctors_rec_supported tree
  (ICtors (ICtor leaf (Pi (Con nat) (Con tree))) ICNil))
  False)
!(test (sig_admitted (nat_tree_base_sig)) False)
