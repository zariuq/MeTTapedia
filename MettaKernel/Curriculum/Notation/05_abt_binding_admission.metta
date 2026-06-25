; ============================================================================
; ABT-style binding admission for LanguageDef notation.
;
; Purpose: a source-backed binding oracle for notation-as-LanguageDef:
;   * one table carries both concrete forms and binding shapes
;   * named concrete syntax forms parse to raw named terms
;   * raw terms lower deterministically to canonical de Bruijn kernel ASTs
;   * canonical ASTs print back with deterministic capture-free names
;
; This is L0/LanguageDef adequacy infrastructure.  The parser is not trusted.
; The separate `03_lf_concrete_syntax_hook.metta` file owns parse-to-kernel-check tests;
; this file focuses on the ABT binding table and shared binding waist.
; ============================================================================

!(import! &self ../../kernel/kernel_binding_waist_v1.metta)

; ---------- list/name helpers ------------------------------------------------
(= (abt-append Nil $ys) $ys)
(= (abt-append (Cons $x $xs) $ys) (Cons $x (abt-append $xs $ys)))
(= (abt-len Nil) 0)
(= (abt-len (Cons $x $xs)) (let $n (abt-len $xs) (+ 1 $n)))
(= (abt-nth $k Nil) ERR)
(= (abt-nth $k (Cons $x $xs))
   (if (== $k 0) $x (let $k1 (- $k 1) (abt-nth $k1 $xs))))
(= (abt-idx $x Nil $i) NF)
(= (abt-idx $x (Cons $y $ys) $i)
   (if (== $x $y) $i (let $i1 (+ $i 1) (abt-idx $x $ys $i1))))
(= (abtvn 0) a0)
(= (abtvn 1) a1)
(= (abtvn 2) a2)
(= (abtvn 3) a3)

; ---------- LanguageDef table: concrete form + binding shape -----------------
; Bind0 = no binder.  Bind1 body = the constructor binds one concrete syntax name in
; the body position.  This is the ABT-style declaration the parser/lowerer reads.
(= (abt-tbl)
   (Cons (AbtNote LamF (LamForm lp lam colon dot rp) (Bind1 body))
    (Cons (AbtNote AppF (AppForm lp app rp) Bind0)
     (Cons (AbtNote RflF (RflForm lp rfl rp) Bind0) Nil))))

(= (abt-note-form (AbtNote $c $f $b)) $f)
(= (abt-note-bind (AbtNote $c $f $b)) $b)

(= (abt-scan $c Nil) NOFORM)
(= (abt-scan $c (Cons (AbtNote $d $f $b) $r))
   (if (== $c $d) (AbtNote $d $f $b) (abt-scan $c $r)))
(= (abt-note-of $c) (abt-scan $c (abt-tbl)))
(= (abt-form-of $c) (let $n (abt-note-of $c) (unify $n (AbtNote $d $f $b) $f NOFORM)))
(= (abt-bind-of $c) (let $n (abt-note-of $c) (unify $n (AbtNote $d $f $b) $b NOBIND)))

(= (abt-lp) (let $f (abt-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $lp ERR)))
(= (abt-lam) (let $f (abt-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $lam ERR)))
(= (abt-colon) (let $f (abt-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $colon ERR)))
(= (abt-dot) (let $f (abt-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $dot ERR)))
(= (abt-rp) (let $f (abt-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $rp ERR)))
(= (abt-app) (let $f (abt-form-of AppF) (unify $f (AppForm $lp $app $rp) $app ERR)))
(= (abt-rfl) (let $f (abt-form-of RflF) (unify $f (RflForm $lp $rfl $rp) $rfl ERR)))

; Admission checks table integrity: concrete syntax forms are injective and binder
; declarations match the forms this tiny LanguageDef knows how to lower.
(= (abt-dup-form $f Nil) False)
(= (abt-dup-form $f (Cons (AbtNote $c $g $b) $r))
   (if (== $f $g) True (abt-dup-form $f $r)))
(= (abt-bind-ok $c $b)
   (if (== $c LamF)
     (== $b (Bind1 body))
     (if (== $c AppF)
       (== $b Bind0)
       (if (== $c RflF) (== $b Bind0) False))))
(= (abt-admit Nil) True)
(= (abt-admit (Cons (AbtNote $c $f $b) $r))
   (if (abt-dup-form $f $r)
     False
     (if (abt-bind-ok $c $b) (abt-admit $r) False)))

(= (abt-bad-dup)
   (Cons (AbtNote LamF (LamForm lp lam colon dot rp) (Bind1 body))
    (Cons (AbtNote Lam2F (LamForm lp lam colon dot rp) (Bind1 body)) Nil)))
(= (abt-bad-bind)
   (Cons (AbtNote LamF (LamForm lp lam colon dot rp) Bind0)
    (Cons (AbtNote AppF (AppForm lp app rp) Bind0)
     (Cons (AbtNote RflF (RflForm lp rfl rp) Bind0) Nil))))

; ---------- parser: concrete tokens -> raw named terms -----------------------
; Raw AST: RName/RLam/RApp/RRfl.  Lowering decides bound Var vs free Con.
(= (abt-prsT $toks)
   (let $r (abt-prs $toks)
     (unify $r (Ok $raw $rest) (unify $rest Nil $raw (Err extra)) $r)))

(= (abt-prs Nil) (Err empty))
(= (abt-prs (Cons $t $rest))
   (if (== $t (abt-lp)) (abt-prs-paren $rest) (Ok (RName $t) $rest)))

(= (abt-prs-paren Nil) (Err empty-paren))
(= (abt-prs-paren (Cons $tag $rest))
   (if (== $tag (abt-lam))
     (abt-prs-lam $rest)
     (if (== $tag (abt-app))
       (abt-prs-app $rest)
       (if (== $tag (abt-rfl)) (abt-prs-rfl $rest) (Err bad-head)))))

(= (abt-prs-lam (Cons $nm (Cons $colon $rest0)))
   (if (== $colon (abt-colon))
     (let $ra (abt-prs $rest0)
       (unify $ra (Ok $A (Cons $dot $rest1))
         (if (== $dot (abt-dot))
           (let $rb (abt-prs $rest1)
             (unify $rb (Ok $body (Cons $rpt $rest2))
               (if (== $rpt (abt-rp)) (Ok (RLam $nm $A $body) $rest2) (Err noRP))
               (Err body-parse)))
           (Err noDot))
         (Err type-parse)))
     (Err noColon)))

(= (abt-prs-app $rest0)
   (let $rf (abt-prs $rest0)
     (unify $rf (Ok $f $rest1)
       (let $ra (abt-prs $rest1)
         (unify $ra (Ok $a (Cons $rpt $rest2))
           (if (== $rpt (abt-rp)) (Ok (RApp $f $a) $rest2) (Err noRP))
           (Err arg-parse)))
       (Err fun-parse))))

(= (abt-prs-rfl $rest0)
   (let $ra (abt-prs $rest0)
     (unify $ra (Ok $a (Cons $rpt $rest1))
       (if (== $rpt (abt-rp)) (Ok (RRfl $a) $rest1) (Err noRP))
       (Err rfl-arg-parse))))

; ---------- lowering: raw named terms -> canonical de Bruijn kernel AST -------
(= (abt-lower $ctx (RName $x))
   (let $i (abt-idx $x $ctx 0)
     (if (== $i NF) (Con $x) (Var $i))))
(= (abt-lower $ctx (RLam $nm $A $body))
   (let $bind (abt-bind-of LamF)
     (if (== $bind (Bind1 body))
       (let $A0 (abt-lower $ctx $A)
         (let $b0 (abt-lower (Cons $nm $ctx) $body)
           (Lam $A0 $b0)))
       (Err bad-bind-shape))))
(= (abt-lower $ctx (RApp $f $a))
   (let $f0 (abt-lower $ctx $f)
     (let $a0 (abt-lower $ctx $a)
       (App $f0 $a0))))
(= (abt-lower $ctx (RRfl $a))
   (let $a0 (abt-lower $ctx $a)
     (App (Con rfl) $a0)))
(= (abt-lower $ctx (Err $e)) (Err $e))
(= (abt-lowerT $toks) (abt-lower Nil (abt-prsT $toks)))

; ---------- canonical printer: de Bruijn kernel AST -> concrete tokens --------
(= (abt-pr $ctx (Con $x)) (Cons $x Nil))
(= (abt-pr $ctx (Var $k)) (Cons (abt-nth $k $ctx) Nil))
(= (abt-pr $ctx (Lam $A $body))
   (let $n (abt-len $ctx)
     (let $nm (abtvn $n)
       (let $lp0 (abt-lp)
         (let $lam0 (abt-lam)
           (let $colon0 (abt-colon)
             (let $dot0 (abt-dot)
               (let $rp0 (abt-rp)
                 (let $Atoks (abt-pr $ctx $A)
                   (let $ctx1 (Cons $nm $ctx)
                     (let $btoks (abt-pr $ctx1 $body)
                       (abt-append
                         (Cons $lp0 (Cons $lam0 (Cons $nm (Cons $colon0 Nil))))
                         (abt-append $Atoks
                           (abt-append (Cons $dot0 Nil)
                             (abt-append $btoks (Cons $rp0 Nil))))))))))))))))
(= (abt-pr $ctx (App (Con rfl) $a))
   (let $lp0 (abt-lp)
     (let $rfl0 (abt-rfl)
       (let $rp0 (abt-rp)
         (let $atoks (abt-pr $ctx $a)
           (abt-append (Cons $lp0 (Cons $rfl0 Nil))
             (abt-append $atoks (Cons $rp0 Nil))))))))
(= (abt-pr $ctx (App $f $a))
   (let $lp0 (abt-lp)
     (let $app0 (abt-app)
       (let $rp0 (abt-rp)
         (let $ftoks (abt-pr $ctx $f)
           (let $atoks (abt-pr $ctx $a)
             (abt-append (Cons $lp0 (Cons $app0 Nil))
               (abt-append $ftoks
                 (abt-append $atoks (Cons $rp0 Nil))))))))))
(= (abt-prT $ast) (abt-pr Nil $ast))
(= (abt-round $ast) (let $toks (abt-prT $ast) (abt-lowerT $toks)))

; Notation binding client: concrete syntax ABT lowering uses the shared kernel waist.
(= (abt-shift $d $c $t) (bind-shift $d $c $t))
(= (abt-subst $j $s $t) (bind-subst $j $s $t))

; ---------- representative concrete syntax forms --------------------------------
(= (abt-lam-concrete-syntax $nm $A_toks $body_toks)
   (abt-append
     (Cons lp (Cons lam (Cons $nm (Cons colon Nil))))
     (abt-append $A_toks
       (abt-append (Cons dot Nil)
         (abt-append $body_toks (Cons rp Nil))))))

(= (abt-idnat-concrete-syntax)
   (abt-lam-concrete-syntax x (Cons nat Nil) (Cons x Nil)))

(= (abt-idnat-q-concrete-syntax)
   (abt-lam-concrete-syntax q (Cons nat Nil) (Cons q Nil)))

(= (abt-shadow-concrete-syntax)
   (let $inner (abt-lam-concrete-syntax x (Cons nat Nil) (Cons x Nil))
     (abt-lam-concrete-syntax x (Cons nat Nil) $inner)))

(= (abt-free-under-binder-concrete-syntax)
   (let $inner (abt-lam-concrete-syntax y (Cons nat Nil) (Cons x Nil))
     (abt-lam-concrete-syntax x (Cons nat Nil) $inner)))

(= (abt-idnat-app-z-concrete-syntax)
   (Cons lp (Cons app
     (abt-append (abt-idnat-concrete-syntax) (Cons z (Cons rp Nil))))))

(= (abt-rfl-z-concrete-syntax)
   (Cons lp (Cons rfl (Cons z (Cons rp Nil)))))

(= (abt-bad-app-concrete-syntax)
   (Cons lp (Cons app (Cons z (Cons z (Cons rp Nil))))))

(= (abt-printed-nested-free-concrete-syntax)
   (let $inner (abt-pr (Cons a0 Nil) (Lam (Con nat) (Var 1)))
     (abt-lam-concrete-syntax a0 (Cons nat Nil) $inner)))

(= (abt-printed-app-under-binder-concrete-syntax)
   (let $body (abt-pr (Cons a0 Nil) (App (Var 0) (Con z)))
     (abt-lam-concrete-syntax a0 (Cons nat Nil) $body)))

; ============================ CHECKS =========================================
; Admission: good table accepted; malformed binding/table data rejected.
!(assertEqual (abt-admit (abt-tbl)) True)
!(assertEqual (abt-admit (abt-bad-dup)) False)
!(assertEqual (abt-admit (abt-bad-bind)) False)

; Named concrete syntax forms lower deterministically to canonical de Bruijn AST.
!(assertEqual (abt-bind-of LamF) (Bind1 body))
!(assertEqual (abt-prsT (abt-idnat-concrete-syntax)) (RLam x (RName nat) (RName x)))
!(assertEqual (abt-lowerT (abt-idnat-concrete-syntax)) (Lam (Con nat) (Var 0)))
!(assertEqual (abt-lowerT (abt-idnat-q-concrete-syntax)) (Lam (Con nat) (Var 0)))
!(assertEqual (abt-lowerT (abt-shadow-concrete-syntax)) (Lam (Con nat) (Lam (Con nat) (Var 0))))
!(assertEqual (abt-lowerT (abt-free-under-binder-concrete-syntax)) (Lam (Con nat) (Lam (Con nat) (Var 1))))

; Canonical printer is deterministic and capture-free; parse(print t) = t.
!(assertEqual (abt-prT (Con nat)) (Cons nat Nil))
!(assertEqual (abt-len (Cons a0 Nil)) 1)
!(assertEqual (abtvn (abt-len (Cons a0 Nil))) a1)
!(assertEqual (abt-nth 1 (Cons a1 (Cons a0 Nil))) a0)
!(assertEqual
  (abt-prT (Lam (Con nat) (Var 0)))
  (Cons lp (Cons lam (Cons a0 (Cons colon (Cons nat (Cons dot (Cons a0 (Cons rp Nil)))))))))
!(assertEqual
  (abt-pr (Cons a0 Nil) (Lam (Con nat) (Var 1)))
  (Cons lp (Cons lam (Cons a1 (Cons colon (Cons nat (Cons dot (Cons a0 (Cons rp Nil)))))))))
!(assertEqual
  (abt-lowerT (abt-printed-nested-free-concrete-syntax))
  (Lam (Con nat) (Lam (Con nat) (Var 1))))
!(assertEqual
  (abt-lowerT (abt-printed-app-under-binder-concrete-syntax))
  (Lam (Con nat) (App (Var 0) (Con z))))

; Local shift/subst capture tests: these are the exact silent failures the
; mutation gate corrupts and expects CeTTa to catch.
!(assertEqual (abt-subst 0 (Var 0) (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 1)))
!(assertEqual (abt-subst 0 (Con z) (Var 1)) (Var 0))
