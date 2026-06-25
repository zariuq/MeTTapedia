; ============================================================================
; MeTTa concrete syntax LanguageDef seed.
;
; Purpose: promote the Web-Claude/GPT-Pro MeTTa-notation seed into the checked
; curriculum lane.  Native CeTTa `parse`/`repr` are the tiny bootstrap
; reader/writer; the LanguageDef layer adds table-driven, invertible sugar over
; the homoiconic core AST:
;
;   read  = desugar . parse
;   write = repr . resugar
;
; This is L0/LanguageDef adequacy infrastructure.  The parser is not trusted:
; parsed concrete syntax terms still go through the small checker/evaluator below.
; ============================================================================

; Grounded ops such as car-atom/cdr-atom/cons-atom do not evaluate their
; arguments; these shims force the needed evaluation before using them.
(= (ms-hd $e) (car-atom $e))
(= (ms-tl $e) (cdr-atom $e))
(= (ms-cns $x $y) (cons-atom $x $y))
(= (ms-expr? $e) (== (get-metatype $e) Expression))
(= (ms-elen $e) (if (== $e ()) 0 (+ 1 (ms-elen (ms-tl $e)))))

; ---------- notation table ---------------------------------------------------
; NNote head concrete syntax token fixity.  v1 keeps one binary infix sugar family.
(= (ms-ntbl) (Cons (NNote plus plus infix)
              (Cons (NNote in   in   infix) Nil)))

(= (ms-mem $x Nil) False)
(= (ms-mem $x (Cons $y $ys)) (if (== $x $y) True (ms-mem $x $ys)))

(= (ms-token (NNote $h $tok $fix)) $tok)
(= (ms-head  (NNote $h $tok $fix)) $h)
(= (ms-fix   (NNote $h $tok $fix)) $fix)

(= (ms-token-member? $tok Nil) False)
(= (ms-token-member? $tok (Cons $n $r))
   (if (== $tok (ms-token $n)) True (ms-token-member? $tok $r)))
(= (ms-head-member? $head Nil) False)
(= (ms-head-member? $head (Cons $n $r))
   (if (== $head (ms-head $n)) True (ms-head-member? $head $r)))

(= (ms-admit Nil) True)
(= (ms-admit (Cons $n $r))
   (if (ms-token-member? (ms-token $n) $r)
     False
     (if (ms-head-member? (ms-head $n) $r) False (ms-admit $r))))

(= (ms-bad-dup-token) (Cons (NNote plus plus infix) (Cons (NNote times plus infix) Nil)))
(= (ms-bad-ambig-head) (Cons (NNote plus plus infix) (Cons (NNote plus plus prefix) Nil)))

(= (ms-inf-head? $head Nil) False)
(= (ms-inf-head? $head (Cons $n $r))
   (if (== (ms-fix $n) infix)
     (if (== $head (ms-head $n)) True (ms-inf-head? $head $r))
     (ms-inf-head? $head $r)))
(= (ms-inf-token? $tok Nil) False)
(= (ms-inf-token? $tok (Cons $n $r))
   (if (== (ms-fix $n) infix)
     (if (== $tok (ms-token $n)) True (ms-inf-token? $tok $r))
     (ms-inf-token? $tok $r)))
(= (ms-is-inf-head $h) (ms-inf-head? $h (ms-ntbl)))
(= (ms-is-inf-token $t) (ms-inf-token? $t (ms-ntbl)))

; ---------- desugar / resugar ------------------------------------------------
; Desugar concrete syntax `(a plus b)` into canonical `(plus a b)` and recurse.
(= (ms-desugar $e) (if (ms-expr? $e) (ms-desugar-e $e) $e))
(= (ms-desugar-e $e) (if (== (ms-elen $e) 3) (ms-desugar-3 $e) (ms-map-de $e)))
(= (ms-desugar-3 $e)
   (let $op (ms-hd (ms-tl $e))
     (if (ms-is-inf-token $op)
       (ms-cns $op
         (ms-cns (ms-desugar (ms-hd $e))
           (ms-cns (ms-desugar (ms-hd (ms-tl (ms-tl $e)))) ())))
       (ms-map-de $e))))
(= (ms-map-de $e)
   (if (== $e ()) () (ms-cns (ms-desugar (ms-hd $e)) (ms-map-de (ms-tl $e)))))

; Resugar canonical `(plus a b)` into concrete syntax `(a plus b)` and recurse.
(= (ms-resugar $e) (if (ms-expr? $e) (ms-resugar-e $e) $e))
(= (ms-resugar-e $e) (if (== (ms-elen $e) 3) (ms-resugar-3 $e) (ms-map-re $e)))
(= (ms-resugar-3 $e)
   (let $op (ms-hd $e)
     (if (ms-is-inf-head $op)
       (ms-cns (ms-resugar (ms-hd (ms-tl $e)))
         (ms-cns $op
           (ms-cns (ms-resugar (ms-hd (ms-tl (ms-tl $e)))) ())))
       (ms-map-re $e))))
(= (ms-map-re $e)
   (if (== $e ()) () (ms-cns (ms-resugar (ms-hd $e)) (ms-map-re (ms-tl $e)))))

; ---------- read / write over real MeTTa text --------------------------------
(= (ms-rd $s) (ms-desugar (parse $s)))
(= (ms-wr $e) (let $s (ms-resugar $e) (repr $s)))

; ---------- tiny checked evaluator for parsed concrete syntax terms ------------------
; This deliberately small checker is the trust boundary for the concrete syntax seed:
; parsing/desugaring may succeed, but only checked nat-plus terms evaluate.
(= (ms-and True $y) $y)
(= (ms-and False $y) False)
(= (ms-nat? $e) (unify $e z True (unify $e (s $n) (ms-nat? $n) False)))
(= (ms-check $e)
   (unify $e (plus $a $b) (ms-and (ms-nat? $a) (ms-nat? $b)) False))
(= (ms-eval $e) (if (ms-check $e) (ms-eval-ok $e) (Err check-failed)))
(= (ms-eval-ok $e)
   (unify $e (plus z $b)
     $b
     (unify $e (plus (s $a) $b)
       (s (ms-eval-ok (plus $a $b)))
       (Err no-rule))))
(= (ms-concrete-syntax-eval $s) (ms-eval (ms-rd $s)))

; ============================ CHECKS =========================================
; Native bootstrap reads real MeTTa source unchanged.
!(assertEqual (parse "(= (f x) (g x))") (= (f x) (g x)))

; Read: infix concrete text desugars to canonical head-first MeTTa.
!(assertEqual (ms-rd "(a plus b)") (plus a b))
!(assertEqual (ms-rd "(f x y)") (f x y))
!(assertEqual (ms-rd "((a plus b) plus c)") (plus (plus a b) c))
!(assertEqual (ms-rd "(g (a plus b) c)") (g (plus a b) c))
!(assertEqual (ms-rd "(z plus (s z))") (plus z (s z)))

; Write: canonical head-first MeTTa prints with the declared sugar.
!(assertEqual (ms-wr (plus a b)) "(a plus b)")
!(assertEqual (ms-wr (g (plus a b) c)) "(g (a plus b) c)")

; Round-trip faithfulness on canonical core terms.
!(assertEqual (ms-rd (ms-wr (plus a b))) (plus a b))
!(assertEqual (ms-rd (ms-wr (plus (plus a b) c))) (plus (plus a b) c))
!(assertEqual (ms-rd (ms-wr (g (plus a b) c))) (g (plus a b) c))

; Admission rejects non-injective or ambiguous sugar tables.
!(assertEqual (ms-admit (ms-ntbl)) True)
!(assertEqual (ms-admit (ms-bad-dup-token)) False)
!(assertEqual (ms-admit (ms-bad-ambig-head)) False)

; Parsed terms are not trusted: they still pass through the checker/evaluator.
!(assertEqual (ms-check (ms-rd "(z plus (s z))")) True)
!(assertEqual (ms-concrete-syntax-eval "(z plus (s z))") (s z))
!(assertEqual (ms-rd "(z plus k)") (plus z k))
!(assertEqual (ms-check (ms-rd "(z plus k)")) False)
!(assertEqual (ms-concrete-syntax-eval "(z plus k)") (Err check-failed))
