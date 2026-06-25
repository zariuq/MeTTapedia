; ============================================================================
; Invertible mixfix notation table over tiny HOTG-shaped forms.
;
; Purpose: first runnable curriculum seed for LanguageDef notation:
;   table-as-data -> generic printer + parser -> round-trip faithfulness
;   plus an admission negative for non-injective notation.
;
; AST uses de Bruijn binders:
;   (Atom a) | (Var k) | (Mem a b) | (Lam body) | (Sep body)
;
; This is an L0/LanguageDef adequacy oracle, not a trusted proof-kernel rule.
; ============================================================================

(= (app Nil $ys) $ys)
(= (app (Cons $x $xs) $ys) (Cons $x (app $xs $ys)))
(= (len Nil) 0)
(= (len (Cons $x $xs)) (+ 1 (len $xs)))
(= (nth $k Nil) ERR)
(= (nth $k (Cons $x $xs)) (if (== $k 0) $x (nth (- $k 1) $xs)))
(= (idx $x Nil $i) NF)
(= (idx $x (Cons $y $ys) $i) (if (== $x $y) $i (idx $x $ys (+ $i 1))))
(= (vn 0) a0)
(= (vn 1) a1)
(= (vn 2) a2)
(= (vn 3) a3)

; ---------- THE NOTATION TABLE (pure data) ----------
; One entry per constructor, carrying its literal concrete syntax symbols.
(= (tbl) (Cons (Note Mem (IN lp in rp))
          (Cons (Note Lam (LM lp lam dot rp))
           (Cons (Note Sep (SP lb bar rb)) Nil))))
(= (form-scan $c (Cons (Note $d $f) $r)) (if (== $c $d) $f (form-scan $c $r)))
(= (form-scan $c Nil) NOFORM)
(= (form-of $c) (form-scan $c (tbl)))

; Concrete syntax symbols are read from the table.  The let is intentional: CeTTa does
; not reduce the first argument of unify unless we pre-evaluate it here.
(= (s-lp) (let $f (form-of Mem) (unify $f (IN $a $s $b) $a ERR)))
(= (s-in) (let $f (form-of Mem) (unify $f (IN $a $s $b) $s ERR)))
(= (s-rp) (let $f (form-of Mem) (unify $f (IN $a $s $b) $b ERR)))
(= (k-lam) (let $f (form-of Lam) (unify $f (LM $a $k $d $b) $k ERR)))
(= (k-dot) (let $f (form-of Lam) (unify $f (LM $a $k $d $b) $d ERR)))
(= (s-lb) (let $f (form-of Sep) (unify $f (SP $x $y $z) $x ERR)))
(= (s-bar) (let $f (form-of Sep) (unify $f (SP $x $y $z) $y ERR)))
(= (s-rb) (let $f (form-of Sep) (unify $f (SP $x $y $z) $z ERR)))

; ---------- PRINT: AST -> tokens (de Bruijn -> fresh names) ----------
(= (pr $ctx (Atom $a)) (Cons $a Nil))
(= (pr $ctx (Var $k)) (Cons (nth $k $ctx) Nil))
(= (pr $ctx (Mem $a $b))
   (app (Cons (s-lp) Nil)
        (app (pr $ctx $a)
             (app (Cons (s-in) Nil)
                  (app (pr $ctx $b) (Cons (s-rp) Nil))))))
(= (pr $ctx (Lam $b))
   (let $nm (vn (len $ctx))
     (app (Cons (s-lp) (Cons (k-lam) (Cons $nm (Cons (k-dot) Nil))))
          (app (pr (Cons $nm $ctx) $b) (Cons (s-rp) Nil)))))
(= (pr $ctx (Sep $b))
   (let $nm (vn (len $ctx))
     (app (Cons (s-lb) (Cons $nm (Cons (s-bar) Nil)))
          (app (pr (Cons $nm $ctx) $b) (Cons (s-rb) Nil)))))
(= (prT $ast) (pr Nil $ast))

; ---------- PARSE: tokens -> AST (names -> de Bruijn; alpha quotient) ----------
; Use prs rather than parse to avoid colliding with Hyperon's grounded parse.
(= (lead-tag $t) (if (== $t (s-lp)) PAREN (if (== $t (s-lb)) SEP NAME)))
(= (prs Nil $ctx) (Err empty))
(= (prs (Cons $t $rest) $ctx) (prs-go (lead-tag $t) $t $rest $ctx))
(= (prs-go NAME  $t $rest $ctx)
   (let $i (idx $t $ctx 0) (Ok (if (== $i NF) (Atom $t) (Var $i)) $rest)))
(= (prs-go PAREN $t $rest $ctx) (prs-paren $rest $ctx))
(= (prs-go SEP   $t $rest $ctx) (prs-sep $rest $ctx))
(= (paren-tag $u) (if (== $u (k-lam)) LAM MEM))
(= (prs-paren (Cons $u $r) $ctx) (paren-go (paren-tag $u) $u $r $ctx))
(= (paren-go LAM $u $r $ctx) (prs-lam $r $ctx))
(= (paren-go MEM $u $r $ctx) (prs-mem (Cons $u $r) $ctx))
(= (prs-lam (Cons $nm (Cons $d $bt)) $ctx)
   (if (== $d (k-dot))
     (let $res (prs $bt (Cons $nm $ctx))
       (unify $res (Ok $body $r2)
         (unify $r2 (Cons $rpt $r3)
           (if (== $rpt (s-rp)) (Ok (Lam $body) $r3) (Err noRP))
           (Err noRPc))
         $res))
     (Err noDot)))
(= (prs-mem $toks $ctx)
   (let $r1 (prs $toks $ctx)
     (unify $r1 (Ok $a $e1)
       (unify $e1 (Cons $it $e1b)
         (if (== $it (s-in))
           (let $r2 (prs $e1b $ctx)
             (unify $r2 (Ok $b $e2)
               (unify $e2 (Cons $rpt $e3)
                 (if (== $rpt (s-rp)) (Ok (Mem $a $b) $e3) (Err noRP))
                 (Err noRPc))
               $r2))
           (Err noIn))
         (Err noInc))
       $r1)))
(= (prs-sep (Cons $nm (Cons $bt0 $bt)) $ctx)
   (if (== $bt0 (s-bar))
     (let $res (prs $bt (Cons $nm $ctx))
       (unify $res (Ok $body $r2)
         (unify $r2 (Cons $rbt $r3)
           (if (== $rbt (s-rb)) (Ok (Sep $body) $r3) (Err noRB))
           (Err noRBc))
         $res))
     (Err noBar)))
(= (prsT $toks)
   (let $r (prs $toks Nil) (unify $r (Ok $ast $rest) (unify $rest Nil $ast (Err extra)) $r)))

; ---------- ADMISSION: table must be injective on concrete syntax forms ----------
(= (dup-form $f Nil) False)
(= (dup-form $f (Cons (Note $c $g) $r)) (if (== $f $g) True (dup-form $f $r)))
(= (admit Nil) True)
(= (admit (Cons (Note $c $f) $r)) (if (dup-form $f $r) False (admit $r)))

; A non-injective table: Mem and Sub share the same concrete syntax form.
(= (bad) (Cons (Note Mem (IN lp in rp)) (Cons (Note Sub (IN lp in rp)) Nil)))

; ============================ CHECKS ============================
; Printer: de Bruijn -> capture-free names; free y stays y.
!(assertEqual (prT (Lam (Mem (Var 0) (Atom y))))
   (Cons lp (Cons lam (Cons a0 (Cons dot (Cons lp (Cons a0 (Cons in (Cons y (Cons rp (Cons rp Nil)))))))))))
!(assertEqual (prT (Sep (Mem (Var 0) (Var 0))))
   (Cons lb (Cons a0 (Cons bar (Cons lp (Cons a0 (Cons in (Cons a0 (Cons rp (Cons rb Nil))))))))))
!(assertEqual (prT (Lam (Lam (Mem (Var 1) (Var 0)))))
   (Cons lp (Cons lam (Cons a0 (Cons dot (Cons lp (Cons lam (Cons a1 (Cons dot (Cons lp (Cons a0 (Cons in (Cons a1 (Cons rp (Cons rp (Cons rp Nil))))))))))))))))
!(assertEqual (prT (Lam (Lam (Mem (Var 0) (Var 1)))))
   (Cons lp (Cons lam (Cons a0 (Cons dot (Cons lp (Cons lam (Cons a1 (Cons dot (Cons lp (Cons a1 (Cons in (Cons a0 (Cons rp (Cons rp (Cons rp Nil))))))))))))))))

; Round-trip faithfulness: parse(print t) = t.
!(assertEqual (prsT (prT (Lam (Mem (Var 0) (Atom y))))) (Lam (Mem (Var 0) (Atom y))))
!(assertEqual (prsT (prT (Sep (Mem (Var 0) (Var 0)))))  (Sep (Mem (Var 0) (Var 0))))
!(assertEqual (prsT (prT (Lam (Lam (Mem (Var 1) (Var 0)))))) (Lam (Lam (Mem (Var 1) (Var 0)))))

; Alpha quotient: different bound names -> identical AST.
!(assertEqual
   (prsT (Cons lp (Cons lam (Cons p (Cons dot (Cons lp (Cons p (Cons in (Cons y (Cons rp (Cons rp Nil)))))))))))
   (prsT (Cons lp (Cons lam (Cons q (Cons dot (Cons lp (Cons q (Cons in (Cons y (Cons rp (Cons rp Nil))))))))))))

; Shadowing is lexical: the inner x shadows the outer x.
!(assertEqual
   (prsT (Cons lp (Cons lam (Cons x (Cons dot (Cons lp (Cons lam (Cons x (Cons dot (Cons lp (Cons x (Cons in (Cons x (Cons rp (Cons rp (Cons rp Nil))))))))))))))))
   (Lam (Lam (Mem (Var 0) (Var 0)))))

; Free variables remain free under binders; outer bound variables keep their index.
!(assertEqual
   (prsT (Cons lp (Cons lam (Cons x (Cons dot (Cons lp (Cons lam (Cons y (Cons dot (Cons lp (Cons x (Cons in (Cons z (Cons rp (Cons rp (Cons rp Nil))))))))))))))))
   (Lam (Lam (Mem (Var 1) (Atom z)))))

; Free vs bound: outside any binder, x is free.
!(assertEqual (prsT (Cons lp (Cons x (Cons in (Cons y (Cons rp Nil)))))) (Mem (Atom x) (Atom y)))

; Admission: good table accepted; non-injective table rejected.
!(assertEqual (admit (tbl)) True)
!(assertEqual (admit (bad)) False)
