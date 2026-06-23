!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; =============================================================================
; kernel_signature_lf_v0.metta
;
; A finite-admitted-signature lambda-Pi-modulo kernel seed with the first real
; DTT eliminator: dependent natural-number recursion plus its iota rules.
;
; This merges the two previous good halves:
;   * lambda-Pi dependent checking from curriculum_lf_demo.metta
;   * finite prefix admission + axiom provenance from kernel_signature_v0.metta
;   * NatRec P z s n : P n, with computation at z and s n
;
; The checker does NOT trust ambient sigT / defBody equations.  Constants,
; definitions, and axioms live in an explicit finite signature.  Definitions are
; admitted only when their body checks against their declared type.  Axioms are
; permitted only as explicit ledger entries, and proof terms are reported with
; the axioms they use.
;
; Run:
;   /home/aimama/aihub/hyperon/CeTTa/cetta kernel_signature_lf_v0.metta
; =============================================================================

; ---------- list helpers -----------------------------------------------------
(= (is_bad $x) (unify $x (Bad $e) True False))

(= (decl_name (DConst $n $T)) $n)
(= (decl_name (DDef $n $T $body)) $n)
(= (decl_name (DAxiom $n $T)) $n)

(= (sig_has_name $n SNil) False)
(= (sig_has_name $n (SCons $d $rest))
   (if (== $n (decl_name $d)) True (sig_has_name $n $rest)))

(= (unique_sig SNil) True)
(= (unique_sig (SCons $d $rest))
   (let $hit (sig_has_name (decl_name $d) $rest)
     (if $hit False (unique_sig $rest))))

(= (ax_union ANil $ys) $ys)
(= (ax_union (ACons $x $xs) $ys) (ACons $x (ax_union $xs $ys)))

; ---------- finite signature lookup -----------------------------------------
; Declarations:
;   DConst name type    -- checked constant/constructor
;   DDef   name type body -- checked definition, unfolds during normalization
;   DAxiom name type    -- unchecked postulate, visible in theorem provenance

(= (decl_type_of SNil $c) (Bad unknown_declaration))
(= (decl_type_of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (decl_type_of $rest $x)))
(= (decl_type_of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (decl_type_of $rest $x)))
(= (decl_type_of (SCons (DAxiom $c $T) $rest) $x)
   (if (== $x $c) $T (decl_type_of $rest $x)))

(= (def_body_of SNil $c) (Bad unknown_definition))
(= (def_body_of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $body (def_body_of $rest $x)))
(= (def_body_of (SCons (DConst $c $T) $rest) $x) (def_body_of $rest $x))
(= (def_body_of (SCons (DAxiom $c $T) $rest) $x) (def_body_of $rest $x))

(= (is_axiom_name SNil $x) False)
(= (is_axiom_name (SCons (DAxiom $a $T) $rest) $x)
   (if (== $x $a) True (is_axiom_name $rest $x)))
(= (is_axiom_name (SCons (DConst $c $T) $rest) $x) (is_axiom_name $rest $x))
(= (is_axiom_name (SCons (DDef $c $T $body) $rest) $x) (is_axiom_name $rest $x))

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
(= (shift $d $c (Bad $e)) (Bad $e))

(= (subst $j $s (Var $k)) (if (== $k $j) $s (if (> $k $j) (Var (- $k 1)) (Var $k))))
(= (subst $j $s (Srt $x)) (Srt $x))
(= (subst $j $s (Con $x)) (Con $x))
(= (subst $j $s (Def $x)) (Def $x))
(= (subst $j $s (App $f $a)) (App (subst $j $s $f) (subst $j $s $a)))
(= (subst $j $s (Pi  $A $B)) (Pi  (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $B)))
(= (subst $j $s (Lam $A $b)) (Lam (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $b)))
(= (subst $j $s (NatRec $P $zcase $scase $n))
   (NatRec (subst $j $s $P) (subst $j $s $zcase) (subst $j $s $scase) (subst $j $s $n)))
(= (subst $j $s (Bad $e)) (Bad $e))

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
(= (nf $sig (Bad $e)) (Bad $e))
(= (nf $sig (App $f $a)) (nf_app $sig (nf $sig $f) (nf $sig $a)))
(= (nf_app $sig $f $a) (unify $f (Lam $A $b) (nf $sig (subst 0 $a $b)) (App $f $a)))
(= (nf_natrec $sig $P $zcase $scase $n)
   (unify $n (Con z)
     $zcase
     (unify $n (App (Con s) $k)
       (nf $sig (App (App $scase $k) (NatRec $P $zcase $scase $k)))
       (NatRec $P $zcase $scase $n))))

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
          (if (is_bad (nf $sig $tb)) (Bad lam_body_bad_type) (Pi $A $tb)))
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
   (if (check $sig $ctx $P (Pi (Con nat) (Srt type)))
     (if (check $sig $ctx $zcase (App $P (Con z)))
       (if (check $sig $ctx $scase (natrec_step_type $P))
         (if (check $sig $ctx $n (Con nat))
           (App $P $n)
           (Bad natrec_scrutinee_not_nat))
         (Bad natrec_bad_step))
       (Bad natrec_bad_zero))
     (Bad natrec_bad_motive)))
(= (infer $sig $ctx (NatRec $P $zcase $scase $n)) (infer_natrec $sig $ctx $P $zcase $scase $n))
(= (check $sig $ctx $t $ty) (conv $sig (infer $sig $ctx $t) $ty))
(= (check_result $sig $ctx $t $ty) (check $sig $ctx $t $ty))

; ---------- signature admission ---------------------------------------------
(= (sort_ok $s)
   (unify $s (Srt type) True
     (unify $s (Srt kind) True False)))

(= (wf_decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT)
       (sort_ok $S))))
(= (wf_decl $prefix (DDef $n $T $body))
   (if (wf_decl $prefix (DConst $n $T))
       (check $prefix CtxNil $body $T)
       False))
(= (wf_decl $prefix (DAxiom $n $T)) (wf_decl $prefix (DConst $n $T)))

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
   (SCons (DConst nat (Srt type))
   (SCons (DConst z (Con nat))
   (SCons (DConst s (Pi (Con nat) (Con nat)))
   (SCons (DConst eqn (Pi (Con nat) (Pi (Con nat) (Srt type))))
   (SCons (DConst rfl (Pi (Con nat) (App (App (Con eqn) (Var 0)) (Var 0))))
   (SCons (DDef plus
     (Pi (Con nat) (Pi (Con nat) (Con nat)))
     (Lam (Con nat)
       (Lam (Con nat)
         (NatRec
           (Lam (Con nat) (Con nat))
           (Var 0)
           (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))
           (Var 1)))))
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

; The old Exp2 wall is closed for concrete plus-zero by computation: rfl now checks.
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
