; =============================================================================
; nik_metamath_l0_cetta_parse_smoke.metta
;
; CeTTa-only smoke bridge from an actual .mm file through CeTTa's textual
; Metamath parser into the NIK L0 parsed-AST admission layer.
;
; Run from this directory:
;   /home/aimama/aihub/hyperon/CeTTa/cetta nik_metamath_l0_cetta_parse_smoke.metta
; =============================================================================

!(import! &self metamath)
!(import! &self nik_metamath_l0_v0)

(= (mm-sym "wff") wff)
(= (mm-sym "ph") ph)
(= (mm-sym "ps") ps)
(= (mm-sym "wph") wph)
(= (mm-sym "wps") wps)
(= (mm-sym "ax-1") ax-1)
(= (mm-sym "th1") th1)

(= (lower-mm-wff "ph") (Var ph))
(= (lower-mm-wff "ps") (Var ps))
(= (lower-mm-wff ("(" $a "mm.->" "(" $b "mm.->" $c ")" ")"))
   (wi (lower-mm-wff $a) (wi (lower-mm-wff $b) (lower-mm-wff $c))))
(= (lower-mm-wff ("(" $a "mm.->" $b ")"))
   (wi (lower-mm-wff $a) (lower-mm-wff $b)))

(= (lower-mm-proof ("wph" "wps" "ax-1"))
   (Cons (FH wph (Var ph))
   (Cons (FH wps (Var ps))
   (Cons (Use ax-1) Nil))))

(= (tiny-cverify-dvars ("ph" "ps")) (Cons (Pair ph ps) Nil))

(= (tiny-cverify-l0 $stmts)
   (unify $stmts
      ((c $consts)
       (open_frame)
       (v $vars)
       (d $dvars)
       (f $fl1 $ty1 $v1)
       (f $fl2 $ty2 $v2)
       (a $ax "|-" $aform)
       (p $th "|-" $pform $proof)
       (close_frame))
      (Cons (L0F (mm-sym $fl1) (mm-sym $ty1) (mm-sym $v1))
      (Cons (L0F (mm-sym $fl2) (mm-sym $ty2) (mm-sym $v2))
      (Cons (L0A (mm-sym $ax) (tiny-cverify-dvars $dvars) Nil (lower-mm-wff $aform))
      (Cons (L0P (mm-sym $th) (tiny-cverify-dvars $dvars) Nil (lower-mm-wff $pform) (lower-mm-proof $proof))
      Nil))))
      (Bad unexpected-parser-shape)))

(= (tiny-cverify-parsed)
   (mm-parse-file-pverify "/home/aimama/aihub/hyperon/CeTTa/tests/support/metamath/tiny_cverify.mm"))
(= (tiny-cverify-env)
   (let $r (l0-ingest (tiny-cverify-l0 (tiny-cverify-parsed)))
     (unify $r (Ok $env) $env $r)))

!(assertEqual
  (tiny-cverify-l0 (tiny-cverify-parsed))
  (Cons (L0F wph wff ph)
  (Cons (L0F wps wff ps)
  (Cons (L0A ax-1 (Cons (Pair ph ps) Nil) Nil (wi (Var ph) (wi (Var ps) (Var ph))))
  (Cons (L0P th1 (Cons (Pair ph ps) Nil) Nil (wi (Var ph) (wi (Var ps) (Var ph)))
         (Cons (FH wph (Var ph)) (Cons (FH wps (Var ps)) (Cons (Use ax-1) Nil))))
  Nil)))))

!(assertEqual
  (l0-ingest (tiny-cverify-l0 (tiny-cverify-parsed)))
  (Ok (tiny-cverify-env)))

!(assertEqual
  (find-ax (env-axdb (tiny-cverify-env)) th1)
  (Ax th1 (Cons (Pair ph ps) Nil) Nil (wi (Var ph) (wi (Var ps) (Var ph)))))

!(assertEqual
  (pf-expr (top (state-pv (stack-run-db (env-fdb (tiny-cverify-env))
                                        (env-axdb (tiny-cverify-env))
                                        (State SNil Nil)
                                        (Cons (Use th1) Nil)))))
  (wi (Var ph) (wi (Var ps) (Var ph))))

!(assertEqual
  (tiny-cverify-l0 ((c ("wff"))))
  (Bad unexpected-parser-shape))

!(assertEqual
  (l0-ingest
    (Cons (L0F wph wff ph)
    (Cons (L0F wps wff ps)
    (Cons (L0A ax-1 (Cons (Pair ph ps) Nil) Nil (wi (Var ph) (wi (Var ps) (Var ph))))
    (Cons (L0P th1 (Cons (Pair ph ps) Nil) Nil (wi (Var ps) (wi (Var ph) (Var ps)))
           (Cons (FH wph (Var ph)) (Cons (FH wps (Var ps)) (Cons (Use ax-1) Nil))))
    Nil)))))
  (Bad theorem-proof-rejected))
