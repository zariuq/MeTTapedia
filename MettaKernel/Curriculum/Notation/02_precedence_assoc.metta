; ============================================================================
; Invertible notation seed for precedence, associativity, and two concrete syntax forms.
;
; Purpose: checked L0/LanguageDef adequacy benchmark for:
;   * operator table admission (duplicate token / mixed associativity reject)
;   * precedence:        a plus b times c  ->  a plus (b times c)
;   * left associativity:  a minus b minus c -> (a minus b) minus c
;   * right associativity: a pow b pow c -> a pow (b pow c)
;   * two concrete syntax forms for one AST: infix tokens and s-expression tokens
;
; This is still L0 adequacy infrastructure.  It does not extend the proof kernel.
; ============================================================================

(= (app Nil $ys) $ys)
(= (app (Cons $x $xs) $ys) (Cons $x (app $xs $ys)))

; ---------- OPERATOR TABLE ----------
; Fix constructor token precedence associativity.
(= (fixTbl)
   (Cons (Fix Add plus 10 left)
    (Cons (Fix Sub minus 10 left)
     (Cons (Fix Mul times 20 left)
      (Cons (Fix Pow pow 30 right) Nil)))))

(= (tok-scan $c Nil) NOTOK)
(= (tok-scan $c (Cons (Fix $d $t $p $a) $r))
   (if (== $c $d) $t (tok-scan $c $r)))
(= (tok-of $c) (tok-scan $c (fixTbl)))

(= (sym-dup $s Nil) False)
(= (sym-dup $s (Cons (Fix $c $t $p $a) $r))
   (if (== $s $t) True (sym-dup $s $r)))

(= (assoc-conflict $p left Nil) False)
(= (assoc-conflict $p right Nil) False)
(= (assoc-conflict $p left (Cons (Fix $c $t $q right) $r))
   (if (== $p $q) True (assoc-conflict $p left $r)))
(= (assoc-conflict $p left (Cons (Fix $c $t $q left) $r))
   (assoc-conflict $p left $r))
(= (assoc-conflict $p right (Cons (Fix $c $t $q left) $r))
   (if (== $p $q) True (assoc-conflict $p right $r)))
(= (assoc-conflict $p right (Cons (Fix $c $t $q right) $r))
   (assoc-conflict $p right $r))

(= (admitFix Nil) True)
(= (admitFix (Cons (Fix $c $s $p $a) $r))
   (if (sym-dup $s $r)
     False
     (if (assoc-conflict $p $a $r) False (admitFix $r))))

; Two admission negatives:
;   same token for two constructors; mixed associativity at one precedence.
(= (badDup)
   (Cons (Fix Add plus 10 left)
    (Cons (Fix Join plus 40 left) Nil)))
(= (badMixedAssoc)
   (Cons (Fix Add plus 10 left)
    (Cons (Fix Cons cons 10 right) Nil)))

; ---------- INFIX PARSER ----------
; AST: (At a) | (Add a b) | (Sub a b) | (Mul a b) | (Pow a b)

(= (pxT $toks)
   (let $r (pxAdd $toks)
     (unify $r (Ok $ast $rest) (unify $rest Nil $ast (Err extra)) $r)))

(= (pxAdd $toks)
   (let $r (pxMul $toks)
     (unify $r (Ok $lhs $rest) (pxAddLoop $lhs $rest) $r)))
(= (pxAddLoop $lhs Nil) (Ok $lhs Nil))
(= (pxAddLoop $lhs (Cons $t $rest))
   (let $plus (tok-of Add)
     (if (== $t $plus)
       (let $r (pxMul $rest)
         (unify $r (Ok $rhs $tail) (pxAddLoop (Add $lhs $rhs) $tail) $r))
       (let $minus (tok-of Sub)
         (if (== $t $minus)
           (let $r (pxMul $rest)
             (unify $r (Ok $rhs $tail) (pxAddLoop (Sub $lhs $rhs) $tail) $r))
           (Ok $lhs (Cons $t $rest)))))))

(= (pxMul $toks)
   (let $r (pxPow $toks)
     (unify $r (Ok $lhs $rest) (pxMulLoop $lhs $rest) $r)))
(= (pxMulLoop $lhs Nil) (Ok $lhs Nil))
(= (pxMulLoop $lhs (Cons $t $rest))
   (let $times (tok-of Mul)
     (if (== $t $times)
       (let $r (pxPow $rest)
         (unify $r (Ok $rhs $tail) (pxMulLoop (Mul $lhs $rhs) $tail) $r))
       (Ok $lhs (Cons $t $rest)))))

; Right-associative exponentiation.
(= (pxPow $toks)
   (let $r (pxAtom $toks)
     (unify $r (Ok $lhs $rest) (pxPowTail $lhs $rest) $r)))
(= (pxPowTail $lhs Nil) (Ok $lhs Nil))
(= (pxPowTail $lhs (Cons $t $rest))
   (let $powtok (tok-of Pow)
     (if (== $t $powtok)
       (let $r (pxPow $rest)
         (unify $r (Ok $rhs $tail) (Ok (Pow $lhs $rhs) $tail) $r))
       (Ok $lhs (Cons $t $rest)))))

(= (pxAtom Nil) (Err empty))
(= (pxAtom (Cons $t $rest))
   (if (== $t lp)
     (let $r (pxAdd $rest)
       (unify $r (Ok $ast (Cons $rpt $tail))
         (if (== $rpt rp) (Ok $ast $tail) (Err noRP))
         (Err noRPc)))
     (Ok (At $t) $rest)))

; A full-parenthesis infix printer.  It is deliberately conservative: the parser
; tests precedence/associativity; print/parse round-trip tests invertibility.
(= (prI (At $a)) (Cons $a Nil))
(= (prI (Add $a $b))
   (app (Cons lp Nil)
     (app (prI $a)
       (app (Cons (tok-of Add) Nil)
         (app (prI $b) (Cons rp Nil))))))
(= (prI (Sub $a $b))
   (app (Cons lp Nil)
     (app (prI $a)
       (app (Cons (tok-of Sub) Nil)
         (app (prI $b) (Cons rp Nil))))))
(= (prI (Mul $a $b))
   (app (Cons lp Nil)
     (app (prI $a)
       (app (Cons (tok-of Mul) Nil)
         (app (prI $b) (Cons rp Nil))))))
(= (prI (Pow $a $b))
   (app (Cons lp Nil)
     (app (prI $a)
       (app (Cons (tok-of Pow) Nil)
         (app (prI $b) (Cons rp Nil))))))

; ---------- S-EXPRESSION CONCRETE SYNTAX ----------
(= (prsSxT $toks)
   (let $r (prsSx $toks)
     (unify $r (Ok $ast $rest) (unify $rest Nil $ast (Err extra)) $r)))
(= (prsSx Nil) (Err empty))
(= (prsSx (Cons $t $rest))
   (if (== $t sxlp) (prsSxOp $rest) (Ok (At $t) $rest)))
(= (sxop-tag $op)
   (if (== $op add) Add
     (if (== $op sub) Sub
       (if (== $op mul) Mul
         (if (== $op powop) Pow BadSxOp)))))
(= (prsSxOp Nil) (Err badSxOp))
(= (prsSxOp (Cons $op $rest))
   (let $tag (sxop-tag $op)
     (if (== $tag BadSxOp) (Err badSxOp) (prsSxBin $tag $rest))))

(= (mkbin Add $a $b) (Add $a $b))
(= (mkbin Sub $a $b) (Sub $a $b))
(= (mkbin Mul $a $b) (Mul $a $b))
(= (mkbin Pow $a $b) (Pow $a $b))
(= (prsSxBin $op $rest)
   (let $ra (prsSx $rest)
     (unify $ra (Ok $a $r1)
       (let $rb (prsSx $r1)
         (unify $rb (Ok $b (Cons $end $tail))
           (if (== $end sxrp) (Ok (mkbin $op $a $b) $tail) (Err noSxRP))
           (Err noSxRPc)))
       $ra)))

(= (prSx (At $a)) (Cons $a Nil))
(= (prSx (Add $a $b))
   (app (Cons sxlp (Cons add Nil)) (app (prSx $a) (app (prSx $b) (Cons sxrp Nil)))))
(= (prSx (Sub $a $b))
   (app (Cons sxlp (Cons sub Nil)) (app (prSx $a) (app (prSx $b) (Cons sxrp Nil)))))
(= (prSx (Mul $a $b))
   (app (Cons sxlp (Cons mul Nil)) (app (prSx $a) (app (prSx $b) (Cons sxrp Nil)))))
(= (prSx (Pow $a $b))
   (app (Cons sxlp (Cons powop Nil)) (app (prSx $a) (app (prSx $b) (Cons sxrp Nil)))))

; ============================ CHECKS ============================
; Admission positives and negatives.
!(assertEqual (admitFix (fixTbl)) True)
!(assertEqual (admitFix (badDup)) False)
!(assertEqual (admitFix (badMixedAssoc)) False)

; Precedence and associativity.
!(assertEqual
  (pxT (Cons a (Cons plus (Cons b (Cons times (Cons c Nil))))))
  (Add (At a) (Mul (At b) (At c))))
!(assertEqual
  (pxT (Cons a (Cons minus (Cons b (Cons minus (Cons c Nil))))))
  (Sub (Sub (At a) (At b)) (At c)))
!(assertEqual
  (pxT (Cons a (Cons pow (Cons b (Cons pow (Cons c Nil))))))
  (Pow (At a) (Pow (At b) (At c))))
!(assertEqual
  (pxT (Cons lp (Cons a (Cons plus (Cons b (Cons rp (Cons times (Cons c Nil))))))))
  (Mul (Add (At a) (At b)) (At c)))

; Infix printer/parser round-trip on representative ASTs.
!(assertEqual
  (pxT (prI (Add (At a) (Mul (At b) (At c)))))
  (Add (At a) (Mul (At b) (At c))))
!(assertEqual
  (pxT (prI (Sub (Sub (At a) (At b)) (At c))))
  (Sub (Sub (At a) (At b)) (At c)))
!(assertEqual
  (pxT (prI (Pow (At a) (Pow (At b) (At c)))))
  (Pow (At a) (Pow (At b) (At c))))

; Two concrete syntaxes: infix and s-expression forms parse to the same AST.
!(assertEqual
  (pxT (Cons a (Cons plus (Cons b (Cons times (Cons c Nil))))))
  (prsSxT (Cons sxlp (Cons add (Cons a (Cons sxlp (Cons mul (Cons b (Cons c (Cons sxrp (Cons sxrp Nil)))))))))))
!(assertEqual
  (prsSxT (prSx (Add (At a) (Mul (At b) (At c)))))
  (Add (At a) (Mul (At b) (At c))))
