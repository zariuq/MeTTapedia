; ============================================================================
; ABT-lowered LF concrete syntax hook.
;
; Purpose: close NOTATION-021 by composing the ABT binding table discipline from
; 05 with the real LF checker hook from 03:
;
;   named LF concrete syntax -> raw named AST -> canonical de Bruijn kernel AST
;   -> imported kernel-check
;
; This file does not extend the kernel.  It demonstrates that an ABT-style
; LanguageDef concrete syntax can lower to the active LF kernel AST and then pass through
; the normal checker boundary.  The parser is not trusted.
; ============================================================================

!(import! &self ../../kernel/kernel_signature_lf_v0.metta)

; ---------- list/name helpers ------------------------------------------------
(= (alf-append Nil $ys) $ys)
(= (alf-append (Cons $x $xs) $ys) (Cons $x (alf-append $xs $ys)))
(= (alf-idx $x Nil $i) NF)
(= (alf-idx $x (Cons $y $ys) $i)
   (if (== $x $y) $i (let $i1 (+ $i 1) (alf-idx $x $ys $i1))))

; ---------- LanguageDef table: concrete form + ABT binding shape -------------
(= (alf-tbl)
   (Cons (AlfNote LamF (LamForm lp lam colon dot rp) (Bind1 body))
    (Cons (AlfNote AppF (AppForm lp app rp) Bind0)
     (Cons (AlfNote RflF (RflForm lp rfl rp) Bind0) Nil))))

(= (alf-bad-bind-tbl)
   (Cons (AlfNote LamF (LamForm lp lam colon dot rp) Bind0)
    (Cons (AlfNote AppF (AppForm lp app rp) Bind0)
     (Cons (AlfNote RflF (RflForm lp rfl rp) Bind0) Nil))))

(= (alf-bad-dup-tbl)
   (Cons (AlfNote LamF (LamForm lp lam colon dot rp) (Bind1 body))
    (Cons (AlfNote Lam2F (LamForm lp lam colon dot rp) (Bind1 body)) Nil)))

(= (alf-note-form (AlfNote $c $f $b)) $f)
(= (alf-note-bind (AlfNote $c $f $b)) $b)
(= (alf-scan $c Nil) NOFORM)
(= (alf-scan $c (Cons (AlfNote $d $f $b) $r))
   (if (== $c $d) (AlfNote $d $f $b) (alf-scan $c $r)))
(= (alf-note-of-in $tbl $c) (alf-scan $c $tbl))
(= (alf-note-of $c) (alf-note-of-in (alf-tbl) $c))
(= (alf-form-of $c)
   (let $n (alf-note-of $c)
     (unify $n (AlfNote $d $f $b) $f NOFORM)))
(= (alf-bind-of-in $tbl $c)
   (let $n (alf-note-of-in $tbl $c)
     (unify $n (AlfNote $d $f $b) $b NOBIND)))
(= (alf-bind-of $c) (alf-bind-of-in (alf-tbl) $c))

(= (alf-lp) (let $f (alf-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $lp ERR)))
(= (alf-lam) (let $f (alf-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $lam ERR)))
(= (alf-colon) (let $f (alf-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $colon ERR)))
(= (alf-dot) (let $f (alf-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $dot ERR)))
(= (alf-rp) (let $f (alf-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $rp ERR)))
(= (alf-app) (let $f (alf-form-of AppF) (unify $f (AppForm $lp $app $rp) $app ERR)))
(= (alf-rfl) (let $f (alf-form-of RflF) (unify $f (RflForm $lp $rfl $rp) $rfl ERR)))

(= (alf-dup-form $f Nil) False)
(= (alf-dup-form $f (Cons (AlfNote $c $g $b) $r))
   (if (== $f $g) True (alf-dup-form $f $r)))
(= (alf-bind-ok $c $b)
   (if (== $c LamF)
     (== $b (Bind1 body))
     (if (== $c AppF)
       (== $b Bind0)
       (if (== $c RflF) (== $b Bind0) False))))
(= (alf-admit Nil) True)
(= (alf-admit (Cons (AlfNote $c $f $b) $r))
   (if (alf-dup-form $f $r)
     False
     (if (alf-bind-ok $c $b) (alf-admit $r) False)))

; ---------- parser: concrete tokens -> raw named terms -----------------------
(= (alf-prsT $toks)
   (let $r (alf-prs $toks)
     (unify $r (Ok $raw $rest) (unify $rest Nil $raw (Err extra)) $r)))
(= (alf-prs Nil) (Err empty))
(= (alf-prs (Cons $t $rest))
   (if (== $t (alf-lp)) (alf-prs-paren $rest) (Ok (RName $t) $rest)))
(= (alf-prs-paren Nil) (Err empty-paren))
(= (alf-prs-paren (Cons $tag $rest))
   (if (== $tag (alf-lam))
     (alf-prs-lam $rest)
     (if (== $tag (alf-app))
       (alf-prs-app $rest)
       (if (== $tag (alf-rfl)) (alf-prs-rfl $rest) (Err bad-head)))))
(= (alf-prs-lam (Cons $nm (Cons $colon $rest0)))
   (if (== $colon (alf-colon))
     (let $ra (alf-prs $rest0)
       (unify $ra (Ok $A (Cons $dot $rest1))
         (if (== $dot (alf-dot))
           (let $rb (alf-prs $rest1)
             (unify $rb (Ok $body (Cons $rpt $rest2))
               (if (== $rpt (alf-rp)) (Ok (RLam $nm $A $body) $rest2) (Err noRP))
               (Err body-parse)))
           (Err noDot))
         (Err type-parse)))
     (Err noColon)))
(= (alf-prs-app $rest0)
   (let $rf (alf-prs $rest0)
     (unify $rf (Ok $f $rest1)
       (let $ra (alf-prs $rest1)
         (unify $ra (Ok $a (Cons $rpt $rest2))
           (if (== $rpt (alf-rp)) (Ok (RApp $f $a) $rest2) (Err noRP))
           (Err arg-parse)))
       (Err fun-parse))))
(= (alf-prs-rfl $rest0)
   (let $ra (alf-prs $rest0)
     (unify $ra (Ok $a (Cons $rpt $rest1))
       (if (== $rpt (alf-rp)) (Ok (RRfl $a) $rest1) (Err noRP))
       (Err rfl-arg-parse))))

; ---------- lowering: raw named terms -> canonical de Bruijn kernel AST -------
(= (alf-lower-in $tbl $ctx (RName $x))
   (let $i (alf-idx $x $ctx 0)
     (if (== $i NF) (Con $x) (Var $i))))
(= (alf-lower-in $tbl $ctx (RLam $nm $A $body))
   (let $bind (alf-bind-of-in $tbl LamF)
     (if (== $bind (Bind1 body))
       (let $A0 (alf-lower-in $tbl $ctx $A)
         (let $b0 (alf-lower-in $tbl (Cons $nm $ctx) $body)
           (Lam $A0 $b0)))
       (Err bad-bind-shape))))
(= (alf-lower-in $tbl $ctx (RApp $f $a))
   (let $f0 (alf-lower-in $tbl $ctx $f)
     (let $a0 (alf-lower-in $tbl $ctx $a)
       (App $f0 $a0))))
(= (alf-lower-in $tbl $ctx (RRfl $a))
   (let $a0 (alf-lower-in $tbl $ctx $a)
     (App (Con rfl) $a0)))
(= (alf-lower-in $tbl $ctx (Err $e)) (Err $e))
(= (alf-lowerT-in $tbl $toks) (alf-lower-in $tbl Nil (alf-prsT $toks)))
(= (alf-lowerT $toks) (alf-lowerT-in (alf-tbl) $toks))

; ---------- checker hook -----------------------------------------------------
(= (alf-concrete-syntax-check $toks $ty)
   (kernel-check (good-sig) (alf-lowerT $toks) $ty))
(= (alf-kernel-gate)
   (kernel-check-batch-judgments (good-sig)
     (Cons (Accept (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))
     (Cons (Accept
              (App (Con rfl) (Con z))
              (App (App (Con eqn) (Con z)) (Con z)))
     (Cons (Reject (App (Con z) (Con z)) (Con nat))
     (Cons (Reject
              (App (Con rfl) (Con z))
              (App (App (Con eqn) (Con z)) (App (Con s) (Con z))))
           Nil))))))

; ---------- representative concrete syntax forms --------------------------------
(= (alf-lam-concrete-syntax $nm $A_toks $body_toks)
   (alf-append
     (Cons lp (Cons lam (Cons $nm (Cons colon Nil))))
     (alf-append $A_toks
       (alf-append (Cons dot Nil)
         (alf-append $body_toks (Cons rp Nil))))))
(= (alf-idnat-concrete-syntax)
   (alf-lam-concrete-syntax x (Cons nat Nil) (Cons x Nil)))
(= (alf-idnat-q-concrete-syntax)
   (alf-lam-concrete-syntax q (Cons nat Nil) (Cons q Nil)))
(= (alf-shadow-concrete-syntax)
   (let $inner (alf-lam-concrete-syntax x (Cons nat Nil) (Cons x Nil))
     (alf-lam-concrete-syntax x (Cons nat Nil) $inner)))
(= (alf-free-under-binder-concrete-syntax)
   (let $inner (alf-lam-concrete-syntax y (Cons nat Nil) (Cons x Nil))
     (alf-lam-concrete-syntax x (Cons nat Nil) $inner)))
(= (alf-idnat-app-z-concrete-syntax)
   (Cons lp (Cons app
     (alf-append (alf-idnat-concrete-syntax) (Cons z (Cons rp Nil))))))
(= (alf-rfl-z-concrete-syntax)
   (Cons lp (Cons rfl (Cons z (Cons rp Nil)))))
(= (alf-bad-app-concrete-syntax)
   (Cons lp (Cons app (Cons z (Cons z (Cons rp Nil))))))

; ============================ CHECKS =========================================
; ABT-lowered concrete syntax forms pass through the imported LF checker.  The compact batch
; checks both accept and reject judgments without retaining CheckedPrf payloads.
!(assertEqual (alf-kernel-gate) True)

; ABT table admission and named lowering.
!(assertEqual (alf-admit (alf-tbl)) True)
!(assertEqual (alf-admit (alf-bad-bind-tbl)) False)
!(assertEqual (alf-admit (alf-bad-dup-tbl)) False)
!(assertEqual (alf-bind-of LamF) (Bind1 body))
!(assertEqual (alf-prsT (alf-idnat-concrete-syntax)) (RLam x (RName nat) (RName x)))
!(assertEqual (alf-lowerT (alf-idnat-concrete-syntax)) (Lam (Con nat) (Var 0)))
!(assertEqual (alf-lowerT (alf-idnat-q-concrete-syntax)) (Lam (Con nat) (Var 0)))
!(assertEqual (alf-lowerT (alf-shadow-concrete-syntax)) (Lam (Con nat) (Lam (Con nat) (Var 0))))
!(assertEqual (alf-lowerT (alf-free-under-binder-concrete-syntax)) (Lam (Con nat) (Lam (Con nat) (Var 1))))
!(assertEqual (alf-lowerT-in (alf-bad-bind-tbl) (alf-idnat-concrete-syntax)) (Err bad-bind-shape))

; Negative concrete syntax lowers successfully while the kernel rejects the term.
!(assertEqual (alf-lowerT (alf-bad-app-concrete-syntax)) (App (Con z) (Con z)))
