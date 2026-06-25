; ============================================================================
; LF concrete syntax notation hook: concrete syntax -> kernel AST -> kernel check.
;
; This is the "parsing belongs inside a LanguageDef" adequacy step:
; a tiny notation table describes a lambda-Pi concrete syntax, the parser lowers it to
; the existing LF kernel AST, and the imported kernel checker accepts/rejects it.
;
; This file does not extend the kernel.  It demonstrates a concrete syntax layer for an
; already-defined calculus.
; ============================================================================

!(import! &self ../../kernel/kernel_signature_lf_v0.metta)

; ---------- list/name helpers ------------------------------------------------
(= (lfn-append Nil $ys) $ys)
(= (lfn-append (Cons $x $xs) $ys) (Cons $x (lfn-append $xs $ys)))
(= (lfn-idx $x Nil $i) NF)
(= (lfn-idx $x (Cons $y $ys) $i) (if (== $x $y) $i (lfn-idx $x $ys (+ $i 1))))

; ---------- notation table ---------------------------------------------------
; Forms are table data.  The parser below reads the literal tokens through these
; accessors rather than hard-coding every spelling in the parsing equations.
(= (lfn-tbl)
   (Cons (LfnNote LamF (LamForm lp lam colon dot rp))
    (Cons (LfnNote AppF (AppForm lp app rp))
     (Cons (LfnNote RflF (RflForm lp rfl rp)) Nil))))

(= (lfn-form-scan $c Nil) NOFORM)
(= (lfn-form-scan $c (Cons (LfnNote $d $f) $r))
   (if (== $c $d) $f (lfn-form-scan $c $r)))
(= (lfn-form-of $c) (lfn-form-scan $c (lfn-tbl)))

(= (lfn-lp)
   (let $f (lfn-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $lp ERR)))
(= (lfn-lam)
   (let $f (lfn-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $lam ERR)))
(= (lfn-colon)
   (let $f (lfn-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $colon ERR)))
(= (lfn-dot)
   (let $f (lfn-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $dot ERR)))
(= (lfn-rp)
   (let $f (lfn-form-of LamF) (unify $f (LamForm $lp $lam $colon $dot $rp) $rp ERR)))
(= (lfn-app)
   (let $f (lfn-form-of AppF) (unify $f (AppForm $lp $app $rp) $app ERR)))
(= (lfn-rfl)
   (let $f (lfn-form-of RflF) (unify $f (RflForm $lp $rfl $rp) $rfl ERR)))

; ---------- parser: LF concrete syntax -> imported LF kernel AST ------------
; Concrete syntax fragment:
;   x                         variable/constant
;   (lam x : A . t)           Lam A t
;   (app f a)                 App f a
;   (rfl t)                   App rfl t
(= (lfn-prsT $toks)
   (let $r (lfn-prs $toks Nil)
     (unify $r (Ok $ast $rest) (unify $rest Nil $ast (Err extra)) $r)))

(= (lfn-prs Nil $ctx) (Err empty))
(= (lfn-prs (Cons $t $rest) $ctx)
   (if (== $t (lfn-lp))
     (lfn-prs-paren $rest $ctx)
     (let $i (lfn-idx $t $ctx 0)
       (Ok (if (== $i NF) (Con $t) (Var $i)) $rest))))

(= (lfn-prs-paren Nil $ctx) (Err empty-paren))
(= (lfn-prs-paren (Cons $tag $rest) $ctx)
   (if (== $tag (lfn-lam))
     (lfn-prs-lam $rest $ctx)
     (if (== $tag (lfn-app))
       (lfn-prs-app $rest $ctx)
       (if (== $tag (lfn-rfl)) (lfn-prs-rfl $rest $ctx) (Err bad-head)))))

(= (lfn-prs-lam (Cons $nm (Cons $colon $rest0)) $ctx)
   (if (== $colon (lfn-colon))
     (let $ra (lfn-prs $rest0 $ctx)
       (unify $ra (Ok $A (Cons $dot $rest1))
         (if (== $dot (lfn-dot))
           (let $rb (lfn-prs $rest1 (Cons $nm $ctx))
             (unify $rb (Ok $body (Cons $rpt $rest2))
               (if (== $rpt (lfn-rp)) (Ok (Lam $A $body) $rest2) (Err noRP))
               (Err body-parse)))
           (Err noDot))
         (Err type-parse)))
     (Err noColon)))

(= (lfn-prs-app $rest0 $ctx)
   (let $rf (lfn-prs $rest0 $ctx)
     (unify $rf (Ok $f $rest1)
       (let $ra (lfn-prs $rest1 $ctx)
         (unify $ra (Ok $a (Cons $rpt $rest2))
           (if (== $rpt (lfn-rp)) (Ok (App $f $a) $rest2) (Err noRP))
           (Err arg-parse)))
       (Err fun-parse))))

(= (lfn-prs-rfl $rest0 $ctx)
   (let $ra (lfn-prs $rest0 $ctx)
     (unify $ra (Ok $a (Cons $rpt $rest1))
       (if (== $rpt (lfn-rp)) (Ok (App (Con rfl) $a) $rest1) (Err noRP))
       (Err rfl-arg-parse))))

; ---------- representative concrete syntax forms ------------------------------------------
(= (lfn-idnat-concrete-syntax)
   (Cons lp (Cons lam (Cons x (Cons colon (Cons nat (Cons dot (Cons x (Cons rp Nil)))))))))

(= (lfn-idnat-app-z-concrete-syntax)
   (Cons lp (Cons app
     (lfn-append (lfn-idnat-concrete-syntax) (Cons z (Cons rp Nil))))))

(= (lfn-rfl-z-concrete-syntax)
   (Cons lp (Cons rfl (Cons z (Cons rp Nil)))))

(= (lfn-bad-app-concrete-syntax)
   (Cons lp (Cons app (Cons z (Cons z (Cons rp Nil))))))

; ============================ CHECKS =========================================
; Parse-to-AST: concrete notation lowers to the imported LF kernel AST.
!(assertEqual (lfn-prsT (lfn-idnat-concrete-syntax)) (Lam (Con nat) (Var 0)))
!(assertEqual
  (lfn-prsT (lfn-idnat-app-z-concrete-syntax))
  (App (Lam (Con nat) (Var 0)) (Con z)))
!(assertEqual (lfn-prsT (lfn-rfl-z-concrete-syntax)) (App (Con rfl) (Con z)))

; Parse -> kernel type checking: the concrete syntax is not just printable syntax.
!(assertEqual
  (check (good-sig) CtxNil (lfn-prsT (lfn-idnat-concrete-syntax)) (Pi (Con nat) (Con nat)))
  True)
!(assertEqual
  (kernel-check (good-sig) (lfn-prsT (lfn-idnat-app-z-concrete-syntax)) (Con nat))
  (Ok (CheckedPrf ANil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))))
!(assertEqual
  (kernel-check (good-sig)
    (lfn-prsT (lfn-rfl-z-concrete-syntax))
    (App (App (Con eqn) (Con z)) (Con z)))
  (Ok (CheckedPrf ANil
    (App (Con rfl) (Con z))
    (App (App (Con eqn) (Con z)) (Con z)))))

; Negative: parsing can succeed while the kernel rejects the target.
!(assertEqual (lfn-prsT (lfn-bad-app-concrete-syntax)) (App (Con z) (Con z)))
!(assertEqual
  (kernel-check (good-sig) (lfn-prsT (lfn-bad-app-concrete-syntax)) (Con nat))
  (Err check-failed))
!(assertEqual
  (kernel-check (good-sig)
    (lfn-prsT (lfn-rfl-z-concrete-syntax))
    (App (App (Con eqn) (Con z)) (App (Con s) (Con z))))
  (Err check-failed))
