; =============================================================================
; nik_metamath_l0_v0.metta
;
; First L0 ingestion layer for the NIK-style Metamath profile.
;
; This file deliberately does not hand-parse raw .mm text.  It defines the
; canonical parsed-AST boundary that tree-sitter, mm-lean4, metamath-knife, or a
; CeTTa textual parser can target, then validates the invariants that the tiny
; checker relies on before lowering to the NIK database.
;
; L0 parsed statements:
;   L0F label type var
;   L0A label dvars ehyps concl
;   L0P label dvars ehyps concl proof
;
; The current NIK fragment supports wff variables and the implication grammar:
;   Expr ::= (Var name) | (wi Expr Expr)
; =============================================================================

; ---------- expressions, lists, substitutions --------------------------------
(= (slook SNil $v) None)
(= (slook (Sub (B $w $e) $r) $v) (if (== $v $w) (Some $e) (slook $r $v)))
(= (sapp $s (Var $x)) (let $r (slook $s $x) (unify $r (Some $e) $e (Var $x))))
(= (sapp $s (wi $a $b)) (wi (sapp $s $a) (sapp $s $b)))

(= (app2 Nil $ys) $ys)
(= (app2 (Cons $x $xs) $ys) (Cons $x (app2 $xs $ys)))
(= (memb $x Nil) False)
(= (memb $x (Cons $y $ys)) (if (== $x $y) True (memb $x $ys)))
(= (vars (Var $x)) (Cons $x Nil))
(= (vars (wi $a $b)) (app2 (vars $a) (vars $b)))
(= (disj Nil $ys) True)
(= (disj (Cons $x $xs) $ys) (if (memb $x $ys) False (disj $xs $ys)))

; ---------- database lookup ---------------------------------------------------
(= (find-f Nil $label) (Bad no-floating-label))
(= (find-f (Cons (F $l $v) $rest) $label)
   (if (== $l $label) (F $l $v) (find-f $rest $label)))
(= (find-ax Nil $x) (Bad nolabel))
(= (find-ax (Cons (Ax $l $d $e $c) $r) $x)
   (if (== $x $l) (Ax $l $d $e $c) (find-ax $r $x)))

(= (fvar-known Nil $v) False)
(= (fvar-known (Cons (F $l $w) $rest) $v)
   (if (== $v $w) True (fvar-known $rest $v)))

; ---------- NIK proof checking over an explicit database ---------------------
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

(= (step-db $axdb $pv (St $label $s))
   (let $ax (find-ax $axdb $label)
     (unify $ax (Ax $l $dv $eh $cc)
       (if (ehyps-ok $pv $s $eh)
           (if (dv-ok $s $dv)
               (Cons (Pf (sapp $s $cc) (lmerge (Cons $label Nil) (gather $pv $s $eh Nil))) $pv)
               (Bad dv-violation))
           (Bad ehyp-not-proven))
       (Bad nolabel))))

(= (fh-bind-db $fdb $subst $flabel $expr)
   (let $f (find-f $fdb $flabel)
     (unify $f (F $l $v) (Sub (B $v $expr) $subst) (Bad no-floating-label))))
(= (stack-step-db $fdb $axdb (State $subst $pv) (FH $flabel $expr))
   (let $s2 (fh-bind-db $fdb $subst $flabel $expr)
     (unify $s2 (Bad $e) (Bad $e) (State $s2 $pv))))
(= (stack-step-db $fdb $axdb (State $subst $pv) (Use $label))
   (let $pv2 (step-db $axdb $pv (St $label $subst))
     (unify $pv2 (Bad $e) (Bad $e) (State SNil $pv2))))
(= (stack-run-db $fdb $axdb $state Nil) $state)
(= (stack-run-db $fdb $axdb $state (Cons $st $rest))
   (let $s2 (stack-step-db $fdb $axdb $state $st)
     (unify $s2 (Bad $e) (Bad $e) (stack-run-db $fdb $axdb $s2 $rest))))

(= (state-pv (State $subst $pv)) $pv)
(= (top (Cons $x $r)) $x)
(= (pf-expr (Pf $e $l)) $e)
(= (pf-l (Pf $e $l)) $l)

; ---------- L0 parsed-AST invariant checking ---------------------------------
(= (vars-floated $fdb Nil) True)
(= (vars-floated $fdb (Cons $v $vs))
   (if (fvar-known $fdb $v) (vars-floated $fdb $vs) False))
(= (expr-floated $fdb $expr) (vars-floated $fdb (vars $expr)))
(= (exprs-floated $fdb Nil) True)
(= (exprs-floated $fdb (Cons $e $es))
   (if (expr-floated $fdb $e) (exprs-floated $fdb $es) False))
(= (dvars-floated $fdb Nil) True)
(= (dvars-floated $fdb (Cons (Pair $x $y) $rest))
   (if (fvar-known $fdb $x)
       (if (fvar-known $fdb $y) (dvars-floated $fdb $rest) False)
       False))

(= (fresh-label (Env $labels $fdb $axdb) $label)
   (if (memb $label $labels) False True))
(= (env-add-float (Env $labels $fdb $axdb) $label $var)
   (Env (Cons $label $labels) (Cons (F $label $var) $fdb) $axdb))
(= (env-add-assert (Env $labels $fdb $axdb) $label $dvars $ehyps $concl)
   (Env (Cons $label $labels) $fdb (Cons (Ax $label $dvars $ehyps $concl) $axdb)))

(= (wf-assert $fdb $dvars $ehyps $concl)
   (if (expr-floated $fdb $concl)
       (if (exprs-floated $fdb $ehyps)
           (dvars-floated $fdb $dvars)
           False)
       False))

(= (l0-check-proof-concl $fdb $axdb $concl $proof)
   (let $run (stack-run-db $fdb $axdb (State SNil Nil) $proof)
     (unify $run (State SNil (Cons (Pf $e $led) $rest))
       (if (== $e $concl) True False)
       False)))

(= (l0-step (Env $labels $fdb $axdb) (L0F $label $type $var))
   (if (fresh-label (Env $labels $fdb $axdb) $label)
       (if (== $type wff)
           (if (fvar-known $fdb $var)
               (Bad duplicate-floating-var)
               (Ok (env-add-float (Env $labels $fdb $axdb) $label $var)))
           (Bad unsupported-floating-type))
       (Bad duplicate-label)))

(= (l0-step (Env $labels $fdb $axdb) (L0A $label $dvars $ehyps $concl))
   (if (fresh-label (Env $labels $fdb $axdb) $label)
       (if (wf-assert $fdb $dvars $ehyps $concl)
           (Ok (env-add-assert (Env $labels $fdb $axdb) $label $dvars $ehyps $concl))
           (Bad malformed-assertion))
       (Bad duplicate-label)))

(= (l0-step (Env $labels $fdb $axdb) (L0P $label $dvars $ehyps $concl $proof))
   (if (fresh-label (Env $labels $fdb $axdb) $label)
       (if (wf-assert $fdb $dvars $ehyps $concl)
           (if (l0-check-proof-concl $fdb $axdb $concl $proof)
               (Ok (env-add-assert (Env $labels $fdb $axdb) $label $dvars $ehyps $concl))
               (Bad theorem-proof-rejected))
           (Bad malformed-assertion))
       (Bad duplicate-label)))

(= (l0-ingest-go $env Nil) (Ok $env))
(= (l0-ingest-go $env (Cons $stmt $rest))
   (let $r (l0-step $env $stmt)
     (unify $r (Ok $env2) (l0-ingest-go $env2 $rest) $r)))
(= (l0-ingest $stmts) (l0-ingest-go (Env Nil Nil Nil) $stmts))

(= (env-labels (Env $labels $fdb $axdb)) $labels)
(= (env-fdb (Env $labels $fdb $axdb)) $fdb)
(= (env-axdb (Env $labels $fdb $axdb)) $axdb)

; ---------- demo0-style parsed input -----------------------------------------
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

(= (l0-demo0-stmts) (Cons
  (L0F wph wff ph)
  (Cons (L0F wps wff ps)
  (Cons (L0F wch wff ch)
  (Cons (L0A ax-1 Nil Nil (wi (Var ph) (wi (Var ps) (Var ph))))
  (Cons (L0A ax-2 Nil Nil (wi (wi (Var ph) (wi (Var ps) (Var ch)))
                              (wi (wi (Var ph) (Var ps)) (wi (Var ph) (Var ch)))))
  (Cons (L0A ax-mp Nil (Cons (Var ph) (Cons (wi (Var ph) (Var ps)) Nil)) (Var ps))
  (Cons (L0A dtest (Cons (Pair ph ps) Nil) Nil (wi (Var ph) (Var ps)))
  (Cons (L0P id Nil Nil (wi (Var ph) (Var ph)) (id-stack-proof))
  Nil)))))))))

(= (l0-demo0-env)
   (let $r (l0-ingest (l0-demo0-stmts))
     (unify $r (Ok $env) $env $r)))

; ---------- positive checks ---------------------------------------------------
!(assertEqual (l0-ingest (l0-demo0-stmts))
              (Ok (l0-demo0-env)))
!(assertEqual (memb id (env-labels (l0-demo0-env))) True)
!(assertEqual (find-ax (env-axdb (l0-demo0-env)) id)
              (Ax id Nil Nil (wi (Var ph) (Var ph))))

!(assertEqual
  (pf-expr (top (state-pv (stack-run-db (env-fdb (l0-demo0-env))
                                        (env-axdb (l0-demo0-env))
                                        (State SNil Nil)
                                        (Cons (Use id) Nil)))))
  (wi (Var ph) (Var ph)))

!(assertEqual
  (pf-expr (top (state-pv (stack-run-db (env-fdb (l0-demo0-env))
                                        (env-axdb (l0-demo0-env))
                                        (State SNil Nil)
                                        (Cons (FH wph (Var x))
                                        (Cons (FH wps (Var y))
                                        (Cons (Use dtest) Nil)))))))
  (wi (Var x) (Var y)))

; ---------- L0 invariant negatives -------------------------------------------
!(assertEqual
  (l0-ingest (Cons (L0F wph wff ph) (Cons (L0F wph wff ps) Nil)))
  (Bad duplicate-label))

!(assertEqual
  (l0-ingest (Cons (L0F wph wff ph) (Cons (L0F wps wff ph) Nil)))
  (Bad duplicate-floating-var))

!(assertEqual
  (l0-ingest (Cons (L0F wph term ph) Nil))
  (Bad unsupported-floating-type))

!(assertEqual
  (l0-ingest (Cons (L0F wph wff ph)
             (Cons (L0A bad Nil Nil (wi (Var ph) (Var ps))) Nil)))
  (Bad malformed-assertion))

!(assertEqual
  (l0-ingest (Cons (L0F wph wff ph)
             (Cons (L0A bad (Cons (Pair ph ps) Nil) Nil (Var ph)) Nil)))
  (Bad malformed-assertion))

!(assertEqual
  (l0-ingest (Cons (L0F wph wff ph)
             (Cons (L0F wps wff ps)
             (Cons (L0A ax-1 Nil Nil (wi (Var ph) (wi (Var ps) (Var ph))))
             (Cons (L0P bad-thm Nil Nil (wi (Var ps) (Var ps))
                    (Cons (FH wph (Var ph))
                    (Cons (FH wps (wi (Var ph) (Var ph)))
                    (Cons (Use ax-1) Nil))))
             Nil)))))
  (Bad theorem-proof-rejected))

!(assertEqual
  (stack-run-db (env-fdb (l0-demo0-env)) (env-axdb (l0-demo0-env))
    (State SNil Nil)
    (Cons (FH wph (wi (Var x) (Var z))) (Cons (FH wps (Var x)) (Cons (Use dtest) Nil))))
  (Bad dv-violation))

!(assertEqual
  (stack-run-db (env-fdb (l0-demo0-env)) (env-axdb (l0-demo0-env))
    (State SNil Nil)
    (Cons (FH wph (Var ph)) (Cons (FH wps (Var ps)) (Cons (Use ax-mp) Nil))))
  (Bad ehyp-not-proven))
