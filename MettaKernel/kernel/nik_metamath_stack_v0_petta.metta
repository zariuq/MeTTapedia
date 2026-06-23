!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; =============================================================================
; nik_metamath_stack_v0.metta
;
; NIK-style Metamath checker with a rawer floating-hypothesis proof layer.
; This keeps the tiny checker from nik_metamath_checker.metta, but adds:
;   FH floating-label expr   -- accumulate a substitution binding
;   Use ax-label            -- check one axiom/theorem step under accumulated FHs
;
; It is still a small fragment, not a full set.mm parser/compressed-proof checker.
; =============================================================================

; ---------- expressions and substitutions ------------------------------------
(= (slook SNil $v) None)
(= (slook (Sub (B $w $e) $r) $v) (if (== $v $w) (Some $e) (slook $r $v)))
(= (sapp $s (Var $x)) (let $r (slook $s $x) (unify $r (Some $e) $e (Var $x))))
(= (sapp $s (wi $a $b)) (wi (sapp $s $a) (sapp $s $b)))

(= (vars (Var $x)) (Cons $x Nil))
(= (vars (wi $a $b)) (app2 (vars $a) (vars $b)))
(= (app2 Nil $ys) $ys)
(= (app2 (Cons $x $xs) $ys) (Cons $x (app2 $xs $ys)))
(= (memb $x Nil) False)
(= (memb $x (Cons $y $ys)) (if (== $x $y) True (memb $x $ys)))
(= (disj Nil $ys) True)
(= (disj (Cons $x $xs) $ys) (if (memb $x $ys) False (disj $xs $ys)))

!(test (sapp (Sub (B ph (wi (Var ph) (Var ph))) SNil) (wi (Var ph) (Var ps)))
              (wi (wi (Var ph) (Var ph)) (Var ps)))
!(test (disj (vars (wi (Var x) (Var z))) (vars (Var y))) True)
!(test (disj (vars (wi (Var x) (Var z))) (vars (Var x))) False)

; ---------- databases ---------------------------------------------------------
(= (fdb) (Cons (F wph ph) (Cons (F wps ps) (Cons (F wch ch) Nil))))
(= (find-f Nil $label) (Bad no-floating-label))
(= (find-f (Cons (F $l $v) $rest) $label)
   (if (== $l $label) (F $l $v) (find-f $rest $label)))

; (Ax label dvars ehyps concl)
(= (axdb) (Cons
   (Ax ax-1 Nil Nil (wi (Var ph) (wi (Var ps) (Var ph))))
   (Cons
   (Ax ax-2 Nil Nil (wi (wi (Var ph) (wi (Var ps) (Var ch)))
                        (wi (wi (Var ph) (Var ps)) (wi (Var ph) (Var ch)))))
   (Cons
   (Ax ax-mp Nil (Cons (Var ph) (Cons (wi (Var ph) (Var ps)) Nil)) (Var ps))
   (Cons
   (Ax dtest (Cons (Pair ph ps) Nil) Nil (wi (Var ph) (Var ps)))
   Nil)))))
(= (find-ax Nil $x) (Bad nolabel))
(= (find-ax (Cons (Ax $l $d $e $c) $r) $x)
   (if (== $x $l) (Ax $l $d $e $c) (find-ax $r $x)))

; ---------- checked proof list + provenance ----------------------------------
(= (pf-has Nil $e) False)
(= (pf-has (Cons (Pf $e2 $l) $r) $e) (if (== $e $e2) True (pf-has $r $e)))
(= (pf-led Nil $e) Nil)
(= (pf-led (Cons (Pf $e2 $l) $r) $e) (if (== $e $e2) $l (pf-led $r $e)))
(= (ehyps-ok $pv $s Nil) True)
(= (ehyps-ok $pv $s (Cons $h $hs)) (if (pf-has $pv (sapp $s $h)) (ehyps-ok $pv $s $hs) False))
(= (dv-ok $s Nil) True)
(= (dv-ok $s (Cons (Pair $x $y) $r))
   (if (disj (vars (sapp $s (Var $x))) (vars (sapp $s (Var $y)))) (dv-ok $s $r) False))
(= (lmerge Nil $ys) $ys)
(= (lmerge (Cons $x $xs) $ys) (if (memb $x $ys) (lmerge $xs $ys) (Cons $x (lmerge $xs $ys))))
(= (gather $pv $s Nil $acc) $acc)
(= (gather $pv $s (Cons $h $hs) $acc) (gather $pv $s $hs (lmerge (pf-led $pv (sapp $s $h)) $acc)))

(= (step $pv (St $label $s))
   (let $ax (find-ax (axdb) $label)
     (unify $ax (Ax $l $dv $eh $cc)
       (if (ehyps-ok $pv $s $eh)
           (if (dv-ok $s $dv)
               (Cons (Pf (sapp $s $cc) (lmerge (Cons $label Nil) (gather $pv $s $eh Nil))) $pv)
               (Bad dv-violation))
           (Bad ehyp-not-proven))
       (Bad nolabel))))

; ---------- floating-hypothesis proof layer ----------------------------------
; State current-substitution proven-list.
(= (fh-bind $subst $flabel $expr)
   (let $f (find-f (fdb) $flabel)
     (unify $f (F $l $v) (Sub (B $v $expr) $subst) (Bad no-floating-label))))
(= (stack-step (State $subst $pv) (FH $flabel $expr))
   (let $s2 (fh-bind $subst $flabel $expr)
     (unify $s2 (Bad $e) (Bad $e) (State $s2 $pv))))
(= (stack-step (State $subst $pv) (Use $label))
   (let $pv2 (step $pv (St $label $subst))
     (unify $pv2 (Bad $e) (Bad $e) (State SNil $pv2))))
(= (stack-run (State $subst $pv) Nil) (State $subst $pv))
(= (stack-run $state (Cons $st $rest))
   (let $s2 (stack-step $state $st)
     (unify $s2 (Bad $e) (Bad $e) (stack-run $s2 $rest))))
(= (state-pv (State $subst $pv)) $pv)
(= (top (Cons $x $r)) $x)
(= (pf-expr (Pf $e $l)) $e)
(= (pf-l (Pf $e $l)) $l)

; Proof of id : |- ph -> ph, now with FH/Use steps instead of St-with-subst.
(= (id-stack-proof) (Cons
  (FH wph (Var ph))
  (Cons (FH wps (wi (Var ph) (Var ph)))
  (Cons (Use ax-1)
  (Cons (FH wph (Var ph))
  (Cons (FH wps (wi (Var ph) (Var ph)))
  (Cons (FH wch (Var ph))
  (Cons (Use ax-2)
  (Cons (FH wph (wi (Var ph) (wi (wi (Var ph) (Var ph)) (Var ph))))
  (Cons (FH wps (wi (wi (Var ph) (wi (Var ph) (Var ph))) (wi (Var ph) (Var ph))))
  (Cons (Use ax-mp)
  (Cons (FH wph (Var ph))
  (Cons (FH wps (Var ph))
  (Cons (Use ax-1)
  (Cons (FH wph (wi (Var ph) (wi (Var ph) (Var ph))))
  (Cons (FH wps (wi (Var ph) (Var ph)))
  (Cons (Use ax-mp) Nil)))))))))))))))))

(= (id-stack-result) (stack-run (State SNil Nil) (id-stack-proof)))

!(test (pf-expr (top (state-pv (id-stack-result)))) (wi (Var ph) (Var ph)))
!(test (memb ax-1  (pf-l (top (state-pv (id-stack-result))))) True)
!(test (memb ax-2  (pf-l (top (state-pv (id-stack-result))))) True)
!(test (memb ax-mp (pf-l (top (state-pv (id-stack-result))))) True)
!(test (memb dtest (pf-l (top (state-pv (id-stack-result))))) False)

; Disjoint-variable rule still works through FH/Use.
!(test
  (pf-expr (top (state-pv (stack-run (State SNil Nil)
    (Cons (FH wph (Var x)) (Cons (FH wps (Var y)) (Cons (Use dtest) Nil)))))))
  (wi (Var x) (Var y)))
!(test
  (stack-run (State SNil Nil)
    (Cons (FH wph (wi (Var x) (Var z))) (Cons (FH wps (Var x)) (Cons (Use dtest) Nil))))
  (Bad dv-violation))

; Essential-hypothesis and floating-label failures are rejected.
!(test
  (stack-run (State SNil Nil)
    (Cons (FH wph (Var ph)) (Cons (FH wps (Var ps)) (Cons (Use ax-mp) Nil))))
  (Bad ehyp-not-proven))
!(test
  (stack-run (State SNil Nil)
    (Cons (FH noSuchFloating (Var ph)) Nil))
  (Bad no-floating-label))
