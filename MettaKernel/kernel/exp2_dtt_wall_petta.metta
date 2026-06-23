!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; =============================================================================
; exp2_dtt_wall.metta
;
; WebClaude Experiment 2: localize the DTT/conversion wall in the current
; admitted lambda-Pi seed, without faking recursors or induction.
;
; Result under test:
;   * beta works.
;   * delta through admitted definitions works.
;   * rfl/equality-introduction works for the opaque identity family.
;   * the first real DTT wall is recursor/iota computation and induction:
;       Nat recursors are not in the kernel/signature yet, so plus-zero and
;       plus_O_r cannot be obtained by computation or induction.
;
; Run:
;   /home/aimama/aihub/hyperon/CeTTa/cetta exp2_dtt_wall.metta
; =============================================================================

; ---------- admitted lambda-Pi kernel core -----------------------------------
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

(= (shift $d $c (Var $k)) (if (< $k $c) (Var $k) (Var (+ $k $d))))
(= (shift $d $c (Srt $s)) (Srt $s))
(= (shift $d $c (Con $x)) (Con $x))
(= (shift $d $c (Def $x)) (Def $x))
(= (shift $d $c (App $f $a)) (App (shift $d $c $f) (shift $d $c $a)))
(= (shift $d $c (Pi $A $B)) (Pi (shift $d $c $A) (shift $d (+ $c 1) $B)))
(= (shift $d $c (Lam $A $b)) (Lam (shift $d $c $A) (shift $d (+ $c 1) $b)))
(= (shift $d $c (Bad $e)) (Bad $e))

(= (subst $j $s (Var $k)) (if (== $k $j) $s (if (> $k $j) (Var (- $k 1)) (Var $k))))
(= (subst $j $s (Srt $x)) (Srt $x))
(= (subst $j $s (Con $x)) (Con $x))
(= (subst $j $s (Def $x)) (Def $x))
(= (subst $j $s (App $f $a)) (App (subst $j $s $f) (subst $j $s $a)))
(= (subst $j $s (Pi $A $B)) (Pi (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $B)))
(= (subst $j $s (Lam $A $b)) (Lam (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $b)))
(= (subst $j $s (Bad $e)) (Bad $e))

(= (nf $sig (Var $k)) (Var $k))
(= (nf $sig (Srt $s)) (Srt $s))
(= (nf $sig (Con $x)) (Con $x))
(= (nf $sig (Def $x))
   (let $body (def_body_of $sig $x)
     (if (is_bad $body) (Bad unknown_definition) (nf $sig $body))))
(= (nf $sig (Pi $A $B)) (Pi (nf $sig $A) (nf $sig $B)))
(= (nf $sig (Lam $A $b)) (Lam (nf $sig $A) (nf $sig $b)))
(= (nf $sig (Bad $e)) (Bad $e))
(= (nf $sig (App $f $a)) (nf_app $sig (nf $sig $f) (nf $sig $a)))
(= (nf_app $sig $f $a) (unify $f (Lam $A $b) (nf $sig (subst 0 $a $b)) (App $f $a)))
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
(= (infer $sig $ctx (Var $i)) (ctx_type $i $ctx))
(= (infer $sig $ctx (Con $c)) (decl_type_of $sig $c))
(= (infer $sig $ctx (Def $c)) (decl_type_of $sig $c))
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
(= (check $sig $ctx $t $ty) (conv $sig (infer $sig $ctx $t) $ty))

(= (sort_ok $s) (unify $s (Srt type) True (unify $s (Srt kind) True False)))
(= (wf_decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T)
     (let $S (nf $prefix $IT) (sort_ok $S))))
(= (wf_decl $prefix (DDef $n $T $body))
   (if (wf_decl $prefix (DConst $n $T)) (check $prefix CtxNil $body $T) False))
(= (wf_decl $prefix (DAxiom $n $T)) (wf_decl $prefix (DConst $n $T)))
(= (wf_sig_prefix $prefix SNil) True)
(= (wf_sig_prefix $prefix (SCons $d $rest))
   (let $ok (wf_decl $prefix $d)
     (if $ok (wf_sig_prefix (SCons $d $prefix) $rest) False)))
(= (sig_admitted $sig)
   (let $u (unique_sig $sig)
     (if $u (wf_sig_prefix SNil $sig) False)))

; ---------- DTT probe signature ---------------------------------------------
(= (dtt_probe_sig)
   (SCons (DConst nat (Srt type))
   (SCons (DConst z (Con nat))
   (SCons (DConst s (Pi (Con nat) (Con nat)))
   (SCons (DConst eqn (Pi (Con nat) (Pi (Con nat) (Srt type))))
   (SCons (DConst rfl (Pi (Con nat) (App (App (Con eqn) (Var 0)) (Var 0))))
   (SCons (DDef idNat (Pi (Con nat) (Con nat)) (Lam (Con nat) (Var 0)))
   (SCons (DConst plus (Pi (Con nat) (Pi (Con nat) (Con nat))))
   (SCons (DConst natRec
     (Pi (Con nat)
       (Pi (Pi (Con nat) (Con nat))
         (Pi (Con nat) (Con nat)))))
          SNil)))))))))

; ---------- positives: what the current seed genuinely has ------------------
!(test (sig_admitted (dtt_probe_sig)) True)

; beta: ((fun x => x) z) : nat and normalizes to z
!(test (check (dtt_probe_sig) CtxNil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat)) True)
!(test (conv (dtt_probe_sig) (App (Lam (Con nat) (Var 0)) (Con z)) (Con z)) True)

; delta: admitted definition idNat unfolds, then beta reduces
!(test (check (dtt_probe_sig) CtxNil (App (Def idNat) (Con z)) (Con nat)) True)
!(test (conv (dtt_probe_sig) (App (Def idNat) (Con z)) (Con z)) True)

; rfl: opaque equality family can be introduced at reflexive endpoints
!(test
   (check (dtt_probe_sig) CtxNil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (Con z)))
   True)

; ---------- negatives: first real wall ---------------------------------------
; plus is only an opaque constant, so plus z z does NOT iota-reduce to z.
!(test
   (conv (dtt_probe_sig)
     (App (App (Con plus) (Con z)) (Con z))
     (Con z))
   False)

; natRec is only an opaque constant, so no recursor/iota computation exists.
!(test
   (conv (dtt_probe_sig)
     (App (App (App (Con natRec) (Con z)) (Lam (Con nat) (Con z))) (Con z))
     (Con z))
   False)

; Therefore a computational proof of plus z z = z by rfl is unavailable.
!(test
   (check (dtt_probe_sig) CtxNil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (App (App (Con plus) (Con z)) (Con z))) (Con z)))
   False)

; Final classification for the report.
(= (dtt_wall) (Wall recursor_iota_and_induction_missing))

!(test
   (dtt_wall)
   (Wall recursor_iota_and_induction_missing))
