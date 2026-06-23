; =============================================================================
; exp3_hotg_both_ways.metta
;
; WebClaude Experiment 3: encode one tiny HO-Set fragment two ways.
;
;   1. Sequent/admitted-signature style: explicit certificates over propositions.
;   2. Lambda-Pi/admitted-signature style: proof terms inhabiting (prf phi).
;
; Same object fragment both ways:
;   set, membership In, two sets a b, axMem : In a b,
;   axSym : In a b -> In b a, and an extensionality-shaped axiom
;   axExtAB : SameMembersAB -> SetEq a b.
;
; This does NOT prove HOTG.  It tests where the tiny fragment is cleaner and
; whether either style hides trust.  Both styles keep axiom provenance visible.
;
; Run:
;   /home/aimama/aihub/hyperon/CeTTa/cetta exp3_hotg_both_ways.metta
; =============================================================================

; =============================================================================
; 1. Sequent/admitted-signature kernel fragment
; =============================================================================

(= (s_is_bad $x) (unify $x (Bad $e) True False))
(= (s_ax_union ANil $ys) $ys)
(= (s_ax_union (ACons $x $xs) $ys) (ACons $x (s_ax_union $xs $ys)))
(= (s_hyp_union HNil $ys) $ys)
(= (s_hyp_union (HCons $x $xs) $ys) (HCons $x (s_hyp_union $xs $ys)))

(= (s_wf_ty $T)
   (unify $T set True
     (unify $T prop True False)))

(= (s_decl_name (DConst $n $T)) $n)
(= (s_decl_name (DAxiom $n $p)) $n)
(= (s_sig_has_name $n SNil) False)
(= (s_sig_has_name $n (SCons $d $rest))
   (if (== $n (s_decl_name $d)) True (s_sig_has_name $n $rest)))
(= (s_unique_sig SNil) True)
(= (s_unique_sig (SCons $d $rest))
   (if (s_sig_has_name (s_decl_name $d) $rest) False (s_unique_sig $rest)))

(= (s_term_type_of SNil $c) (Bad unknown_constant))
(= (s_term_type_of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (s_term_type_of $rest $x)))
(= (s_term_type_of (SCons (DAxiom $a $p) $rest) $x)
   (s_term_type_of $rest $x))

(= (s_axiom_prop_of SNil $ax) (Bad unknown_axiom))
(= (s_axiom_prop_of (SCons (DAxiom $a $p) $rest) $x)
   (if (== $x $a) $p (s_axiom_prop_of $rest $x)))
(= (s_axiom_prop_of (SCons (DConst $c $T) $rest) $x)
   (s_axiom_prop_of $rest $x))

(= (s_infer_tm $sig (Cst $c)) (s_term_type_of $sig $c))
(= (s_tm_check $sig $t $T)
   (if (s_wf_ty $T)
       (let $IT (s_infer_tm $sig $t)
         (if (s_is_bad $IT) False (== $IT $T)))
       False))

(= (s_wf_prop $sig $p)
   (unify $p (Atom $name) True
     (unify $p (Imp $a $b)
       (if (s_wf_prop $sig $a) (s_wf_prop $sig $b) False)
       (unify $p (Eq $t $u)
         (let $TT (s_infer_tm $sig $t)
           (if (s_is_bad $TT) False (s_tm_check $sig $u $TT)))
         (unify $p (In $x $y)
           (if (s_tm_check $sig $x set) (s_tm_check $sig $y set) False)
           False)))))

(= (s_wf_decl $prefix (DConst $n $T)) (s_wf_ty $T))
(= (s_wf_decl $prefix (DAxiom $n $p)) (s_wf_prop $prefix $p))
(= (s_wf_sig_prefix $prefix SNil) True)
(= (s_wf_sig_prefix $prefix (SCons $d $rest))
   (if (s_wf_decl $prefix $d)
       (s_wf_sig_prefix (SCons $d $prefix) $rest)
       False))
(= (s_sig_admitted $sig)
   (if (s_unique_sig $sig) (s_wf_sig_prefix SNil $sig) False))

(= (s_kernel_check $sig $cert)
   (if (s_sig_admitted $sig)
       (s_kernel_check_admitted $sig $cert)
       (Err signature_not_admitted)))
(= (s_kernel_check_admitted $sig $cert)
   (unify $cert (CUseAxiom $ax)
     (let $p (s_axiom_prop_of $sig $ax)
       (if (s_is_bad $p)
           (Err unknown_axiom)
           (Ok (CheckedThm (ACons $ax ANil) (Seq HNil $p)))))
     (unify $cert (CMP $c1 $c2)
       (let $R1 (s_kernel_check_admitted $sig $c1)
         (let $R2 (s_kernel_check_admitted $sig $c2)
           (unify $R1 (Ok (CheckedThm $u1 (Seq $G1 (Imp $p $q))))
             (unify $R2 (Ok (CheckedThm $u2 (Seq $G2 $p2)))
               (if (== $p $p2)
                   (Ok (CheckedThm (s_ax_union $u1 $u2) (Seq (s_hyp_union $G1 $G2) $q)))
                   (Err mp_antecedent_mismatch))
               $R2)
             $R1)))
       (Err unknown_certificate))))

(= (seq_hotg_sig)
   (SCons (DConst a set)
   (SCons (DConst b set)
   (SCons (DAxiom axMem (In (Cst a) (Cst b)))
   (SCons (DAxiom axSym (Imp (In (Cst a) (Cst b)) (In (Cst b) (Cst a))))
   (SCons (DAxiom axExtAB (Imp (Atom SameMembersAB) (Eq (Cst a) (Cst b))))
          SNil))))))

(= (seq_hotg_member_cert) (CMP (CUseAxiom axSym) (CUseAxiom axMem)))
(= (seq_hotg_member_expected)
   (Ok (CheckedThm (ACons axSym (ACons axMem ANil))
     (Seq HNil (In (Cst b) (Cst a))))))
(= (seq_hotg_bad_cert) (CMP (CUseAxiom axSym) (CUseAxiom axExtAB)))

!(assertEqual (s_sig_admitted (seq_hotg_sig)) True)
!(assertEqual (s_kernel_check (seq_hotg_sig) (seq_hotg_member_cert)) (seq_hotg_member_expected))
!(assertEqual (s_kernel_check (seq_hotg_sig) (seq_hotg_bad_cert)) (Err mp_antecedent_mismatch))

; =============================================================================
; 2. Lambda-Pi/admitted-signature kernel fragment
; =============================================================================

(= (l_is_bad $x) (unify $x (Bad $e) True False))
(= (l_decl_name (DConst $n $T)) $n)
(= (l_decl_name (DDef $n $T $body)) $n)
(= (l_decl_name (DAxiom $n $T)) $n)
(= (l_sig_has_name $n SNil) False)
(= (l_sig_has_name $n (SCons $d $rest))
   (if (== $n (l_decl_name $d)) True (l_sig_has_name $n $rest)))
(= (l_unique_sig SNil) True)
(= (l_unique_sig (SCons $d $rest))
   (if (l_sig_has_name (l_decl_name $d) $rest) False (l_unique_sig $rest)))
(= (l_ax_union ANil $ys) $ys)
(= (l_ax_union (ACons $x $xs) $ys) (ACons $x (l_ax_union $xs $ys)))

(= (l_decl_type_of SNil $c) (Bad unknown_declaration))
(= (l_decl_type_of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (l_decl_type_of $rest $x)))
(= (l_decl_type_of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (l_decl_type_of $rest $x)))
(= (l_decl_type_of (SCons (DAxiom $c $T) $rest) $x)
   (if (== $x $c) $T (l_decl_type_of $rest $x)))
(= (l_def_body_of SNil $c) (Bad unknown_definition))
(= (l_def_body_of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $body (l_def_body_of $rest $x)))
(= (l_def_body_of (SCons (DConst $c $T) $rest) $x) (l_def_body_of $rest $x))
(= (l_def_body_of (SCons (DAxiom $c $T) $rest) $x) (l_def_body_of $rest $x))
(= (l_is_axiom_name SNil $x) False)
(= (l_is_axiom_name (SCons (DAxiom $a $T) $rest) $x)
   (if (== $x $a) True (l_is_axiom_name $rest $x)))
(= (l_is_axiom_name (SCons (DConst $c $T) $rest) $x)
   (l_is_axiom_name $rest $x))
(= (l_is_axiom_name (SCons (DDef $c $T $body) $rest) $x)
   (l_is_axiom_name $rest $x))

(= (l_shift $d $c (Var $k)) (if (< $k $c) (Var $k) (Var (+ $k $d))))
(= (l_shift $d $c (Srt $s)) (Srt $s))
(= (l_shift $d $c (Con $x)) (Con $x))
(= (l_shift $d $c (Def $x)) (Def $x))
(= (l_shift $d $c (App $f $a)) (App (l_shift $d $c $f) (l_shift $d $c $a)))
(= (l_shift $d $c (Pi $A $B)) (Pi (l_shift $d $c $A) (l_shift $d (+ $c 1) $B)))
(= (l_shift $d $c (Lam $A $b)) (Lam (l_shift $d $c $A) (l_shift $d (+ $c 1) $b)))
(= (l_shift $d $c (Bad $e)) (Bad $e))

(= (l_subst $j $s (Var $k)) (if (== $k $j) $s (if (> $k $j) (Var (- $k 1)) (Var $k))))
(= (l_subst $j $s (Srt $x)) (Srt $x))
(= (l_subst $j $s (Con $x)) (Con $x))
(= (l_subst $j $s (Def $x)) (Def $x))
(= (l_subst $j $s (App $f $a)) (App (l_subst $j $s $f) (l_subst $j $s $a)))
(= (l_subst $j $s (Pi $A $B)) (Pi (l_subst $j $s $A) (l_subst (+ $j 1) (l_shift 1 0 $s) $B)))
(= (l_subst $j $s (Lam $A $b)) (Lam (l_subst $j $s $A) (l_subst (+ $j 1) (l_shift 1 0 $s) $b)))
(= (l_subst $j $s (Bad $e)) (Bad $e))

(= (l_nf $sig (Var $k)) (Var $k))
(= (l_nf $sig (Srt $s)) (Srt $s))
(= (l_nf $sig (Con $x)) (Con $x))
(= (l_nf $sig (Def $x))
   (let $body (l_def_body_of $sig $x)
     (if (l_is_bad $body) (Bad unknown_definition) (l_nf $sig $body))))
(= (l_nf $sig (Pi $A $B)) (Pi (l_nf $sig $A) (l_nf $sig $B)))
(= (l_nf $sig (Lam $A $b)) (Lam (l_nf $sig $A) (l_nf $sig $b)))
(= (l_nf $sig (Bad $e)) (Bad $e))
(= (l_nf $sig (App $f $a)) (l_nf_app $sig (l_nf $sig $f) (l_nf $sig $a)))
(= (l_nf_app $sig $f $a) (unify $f (Lam $A $b) (l_nf $sig (l_subst 0 $a $b)) (App $f $a)))
(= (l_conv $sig $x $y)
   (if (l_is_bad (l_nf $sig $x)) False
     (if (l_is_bad (l_nf $sig $y)) False
       (== (l_nf $sig $x) (l_nf $sig $y)))))

(= (l_ctx_nth $i CtxNil) (Bad var_out_of_range))
(= (l_ctx_nth $i (CtxCons $h $t)) (if (== $i 0) $h (l_ctx_nth (- $i 1) $t)))
(= (l_ctx_type $i $ctx) (l_shift (+ $i 1) 0 (l_ctx_nth $i $ctx)))
(= (l_pts_rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi_bad_codomain)))
     (Bad pi_domain_not_type)))

(= (l_infer $sig $ctx (Srt type)) (Srt kind))
(= (l_infer $sig $ctx (Srt kind)) (Bad kind_is_topsort))
(= (l_infer $sig $ctx (Var $i)) (l_ctx_type $i $ctx))
(= (l_infer $sig $ctx (Con $c)) (l_decl_type_of $sig $c))
(= (l_infer $sig $ctx (Def $c)) (l_decl_type_of $sig $c))
(= (l_infer $sig $ctx (Pi $A $B))
   (let $sA (l_nf $sig (l_infer $sig $ctx $A))
     (let $sB (l_nf $sig (l_infer $sig (CtxCons $A $ctx) $B)) (l_pts_rule $sA $sB))))
(= (l_infer_lam $sig $ctx $A $b)
   (let $sA (l_nf $sig (l_infer $sig $ctx $A))
     (unify $sA (Srt type)
        (let $tb (l_infer $sig (CtxCons $A $ctx) $b)
          (if (l_is_bad (l_nf $sig $tb)) (Bad lam_body_bad_type) (Pi $A $tb)))
        (Bad lam_domain_not_a_type))))
(= (l_infer $sig $ctx (Lam $A $b)) (l_infer_lam $sig $ctx $A $b))
(= (l_infer_app $sig $ctx $f $a)
   (let $tf (l_nf $sig (l_infer $sig $ctx $f))
     (unify $tf (Pi $A $B)
        (if (l_conv $sig (l_infer $sig $ctx $a) $A) (l_subst 0 $a $B) (Bad arg_type_mismatch))
        (Bad applied_a_non_function))))
(= (l_infer $sig $ctx (App $f $a)) (l_infer_app $sig $ctx $f $a))
(= (l_check $sig $ctx $t $ty) (l_conv $sig (l_infer $sig $ctx $t) $ty))

(= (l_sort_ok $s) (unify $s (Srt type) True (unify $s (Srt kind) True False)))
(= (l_wf_decl $prefix (DConst $n $T))
   (let $IT (l_infer $prefix CtxNil $T)
     (let $S (l_nf $prefix $IT) (l_sort_ok $S))))
(= (l_wf_decl $prefix (DDef $n $T $body))
   (if (l_wf_decl $prefix (DConst $n $T)) (l_check $prefix CtxNil $body $T) False))
(= (l_wf_decl $prefix (DAxiom $n $T)) (l_wf_decl $prefix (DConst $n $T)))
(= (l_wf_sig_prefix $prefix SNil) True)
(= (l_wf_sig_prefix $prefix (SCons $d $rest))
   (let $ok (l_wf_decl $prefix $d)
     (if $ok (l_wf_sig_prefix (SCons $d $prefix) $rest) False)))
(= (l_sig_admitted $sig)
   (if (l_unique_sig $sig) (l_wf_sig_prefix SNil $sig) False))

(= (l_term_axioms $sig (Var $k)) ANil)
(= (l_term_axioms $sig (Srt $s)) ANil)
(= (l_term_axioms $sig (Con $c))
   (if (l_is_axiom_name $sig $c) (ACons $c ANil) ANil))
(= (l_term_axioms $sig (Def $c)) ANil)
(= (l_term_axioms $sig (Pi $A $B)) (l_ax_union (l_term_axioms $sig $A) (l_term_axioms $sig $B)))
(= (l_term_axioms $sig (Lam $A $b)) (l_ax_union (l_term_axioms $sig $A) (l_term_axioms $sig $b)))
(= (l_term_axioms $sig (App $f $a)) (l_ax_union (l_term_axioms $sig $f) (l_term_axioms $sig $a)))
(= (l_term_axioms $sig (Bad $e)) ANil)
(= (l_kernel_check_checked $sig $term $type True)
   (Ok (CheckedPrf (l_term_axioms $sig $term) $term $type)))
(= (l_kernel_check_checked $sig $term $type False) (Err check_failed))
(= (l_check_result $sig $ctx $term $type) (l_check $sig $ctx $term $type))
(= (l_kernel_check $sig $term $type)
   (case (l_sig_admitted $sig)
     ((True (l_kernel_check_checked $sig $term $type (l_check_result $sig CtxNil $term $type)))
      (False (Err signature_not_admitted)))))

(= (lf_hotg_sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DConst imp (Pi (Con o) (Pi (Con o) (Con o))))
   (SCons (DConst impE
     (Pi (Con o) (Pi (Con o)
       (Pi (App (Con prf) (App (App (Con imp) (Var 1)) (Var 0)))
         (Pi (App (Con prf) (Var 2)) (App (Con prf) (Var 2)))))))
   (SCons (DConst set (Srt type))
   (SCons (DConst In (Pi (Con set) (Pi (Con set) (Con o))))
   (SCons (DConst setEq (Pi (Con set) (Pi (Con set) (Con o))))
   (SCons (DConst SameMembersAB (Con o))
   (SCons (DConst a (Con set))
   (SCons (DConst b (Con set))
   (SCons (DAxiom axMem (App (Con prf) (App (App (Con In) (Con a)) (Con b))))
   (SCons (DAxiom axSym
     (App (Con prf)
       (App (App (Con imp) (App (App (Con In) (Con a)) (Con b)))
                         (App (App (Con In) (Con b)) (Con a)))))
   (SCons (DAxiom axExtAB
     (App (Con prf)
       (App (App (Con imp) (Con SameMembersAB))
            (App (App (Con setEq) (Con a)) (Con b)))))
          SNil))))))))))))))

(= (lf_hotg_member_term)
   (App (App (App (App (Con impE)
     (App (App (Con In) (Con a)) (Con b)))
     (App (App (Con In) (Con b)) (Con a)))
     (Con axSym))
     (Con axMem)))
(= (lf_hotg_member_type)
   (App (Con prf) (App (App (Con In) (Con b)) (Con a))))
(= (lf_hotg_member_expected)
   (Ok (CheckedPrf (ACons axSym (ACons axMem ANil))
     (lf_hotg_member_term)
     (lf_hotg_member_type))))
(= (lf_hotg_ext_type)
   (App (Con prf)
     (App (App (Con imp) (Con SameMembersAB))
          (App (App (Con setEq) (Con a)) (Con b)))))

(= (lf_hotg_member_check)
   (l_kernel_check (lf_hotg_sig)
     (App (App (App (App (Con impE)
       (App (App (Con In) (Con a)) (Con b)))
       (App (App (Con In) (Con b)) (Con a)))
       (Con axSym))
       (Con axMem))
     (App (Con prf) (App (App (Con In) (Con b)) (Con a)))))
(= (lf_hotg_ext_check)
   (l_kernel_check (lf_hotg_sig)
     (Con axExtAB)
     (App (Con prf)
       (App (App (Con imp) (Con SameMembersAB))
            (App (App (Con setEq) (Con a)) (Con b))))))
(= (lf_hotg_ext_bad_check)
   (l_kernel_check (lf_hotg_sig)
     (Con axExtAB)
     (App (Con prf) (App (App (Con In) (Con b)) (Con a)))))

!(assertEqual (l_sig_admitted (lf_hotg_sig)) True)
!(assertEqual (lf_hotg_member_check) (lf_hotg_member_expected))
!(assertEqual
   (lf_hotg_ext_check)
   (Ok (CheckedPrf (ACons axExtAB ANil) (Con axExtAB) (lf_hotg_ext_type))))
!(assertEqual
   (lf_hotg_ext_bad_check)
   (Err check_failed))

; =============================================================================
; Report term: stable symbolic comparison for the architectural matrix.
; =============================================================================

(= (exp3_hotg_matrix)
   (Matrix
     (SequentStyle
       (ProofShape (CMP (CUseAxiom axSym) (CUseAxiom axMem)))
       (Provenance (ACons axSym (ACons axMem ANil)))
       (Strength short_classical_certificate)
       (Weakness nominal_checkedthm_boundary))
     (LambdaPiStyle
       (ProofShape impE_proof_term)
       (Provenance (ACons axSym (ACons axMem ANil)))
       (Strength dependent_signature_scales_to_dtt)
       (Weakness more_verbose_object_encoding))
     (Conclusion hotg_clean_both_ways_prefer_lambda_pi_as_unified_waist_keep_sequent_as_reference_profile)))

!(assertEqual
   (exp3_hotg_matrix)
   (Matrix
     (SequentStyle
       (ProofShape (CMP (CUseAxiom axSym) (CUseAxiom axMem)))
       (Provenance (ACons axSym (ACons axMem ANil)))
       (Strength short_classical_certificate)
       (Weakness nominal_checkedthm_boundary))
     (LambdaPiStyle
       (ProofShape impE_proof_term)
       (Provenance (ACons axSym (ACons axMem ANil)))
       (Strength dependent_signature_scales_to_dtt)
       (Weakness more_verbose_object_encoding))
     (Conclusion hotg_clean_both_ways_prefer_lambda_pi_as_unified_waist_keep_sequent_as_reference_profile)))
