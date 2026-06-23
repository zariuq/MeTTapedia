; =============================================================================
; kernel_signature_lf_indexed_v0.metta
;
; PHASES 1+2+3+4 of the general indexed-inductive "telescope IR" engine.
; Introduces ONE declaration form `DIndG` beside the existing slices, with an
; explicit telescope IR, and implements:
;   * the family-kind generator        (Pi Delta. Pi Xi. Type)
;   * the constructor-type generator   (Pi Delta. Pi Gamma. (name Delta idx))
;   * signature lookup (decl-type-of) over DIndG
;   * declaration admission (unique ctors, family-kind well-formed,
;     each GENERATED ctor type well-formed, strict positivity)
;   * generated eliminator + branch TYPES
;   * strengthened `sig-admitted-with-elims` view: admitted signature plus every
;     DIndG's generated eliminator type typechecks
;   * generated constructor-headed iota: the (IndG ...) eliminator term computes
;     by reducing on a constructor; J for Id is the diagonal iota from the SAME
;     generic path (no special rule)
;   * typed IndG checking by applying the generated eliminator type as the single
;     specification (params, motive, cases, indices, scrutinee)
;   * CheckedPrf minting with axiom provenance over checked IndG terms
;   * retirement gate (proved via generated J, no GEq/GRfl/GTransp/Transp):
;     J diagonal; successor congruence; a checked `plus` DDef over the generated
;     recursor; and `forall n. plus n z = n` by generated Nat induction + cong-s
;
; v3 convergence status: the dedicated GEq/GRfl/GTransp/Transp and Id/J slices
; are retired to `retired_fixtures/`.  The remaining older inductive-family
; slices are still live compatibility/regression rows until the v4 slice-collapse
; milestone replays them through DIndG and retires them too.  A fully generic
; transport combinator remains future helper-factoring work; it is not a live
; primitive in this engine.
;
; Validation goal: the generated family/constructor/eliminator types MUST equal
; the hand-written types the current slices carry (Nat, List, Vec, Fin, Id) —
; so this is replay-before-retire for the remaining family slices.  For Id, the
; generated eliminator type is J and the dedicated Id/J slice has been retired.
;
; IR:
;   Tel    ::= TNil | (TCons <type> Tel)            -- each entry in ctx of priors
;   Args   ::= ArgsNil | (ArgsCons <term> Args)
;   GCtors ::= GCNil | (GCtors (GCtor <name> <argTel:Tel> <resultIdx:Args>) GCtors)
;   DIndG <name> <paramTel:Tel> <indexTel:Tel> <ctors:GCtors>
;     constructor result targets (name <paramVars> <resultIdx>), resultIdx written
;     in context paramTel ++ argTel.
; =============================================================================

(= (is-bad $x) (unify $x (Bad $e) True False))
(= (ax-union ANil $ys) $ys)
(= (ax-union (ACons $x $xs) $ys) (ACons $x (ax-union $xs $ys)))

; ---------- de Bruijn term machinery (base forms only — no recursor terms) ----
(= (shift $d $c (Var $k)) (if (< $k $c) (Var $k) (Var (+ $k $d))))
(= (shift $d $c (Srt $s)) (Srt $s))
(= (shift $d $c (Con $x)) (Con $x))
(= (shift $d $c (Def $x)) (Def $x))
(= (shift $d $c (App $f $a)) (App (shift $d $c $f) (shift $d $c $a)))
(= (shift $d $c (Pi  $A $B)) (Pi  (shift $d $c $A) (shift $d (+ $c 1) $B)))
(= (shift $d $c (Lam $A $b)) (Lam (shift $d $c $A) (shift $d (+ $c 1) $b)))
(= (shift $d $c (Bad $e)) (Bad $e))

(= (subst $j $s (Var $k)) (if (== $k $j) $s (if (> $k $j) (Var (- $k 1)) (Var $k))))
(= (subst $j $s (Srt $x)) (Srt $x))
(= (subst $j $s (Con $x)) (Con $x))
(= (subst $j $s (Def $x)) (Def $x))
(= (subst $j $s (App $f $a)) (App (subst $j $s $f) (subst $j $s $a)))
(= (subst $j $s (Pi  $A $B)) (Pi  (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $B)))
(= (subst $j $s (Lam $A $b)) (Lam (subst $j $s $A) (subst (+ $j 1) (shift 1 0 $s) $b)))
(= (subst $j $s (Bad $e)) (Bad $e))

(= (nf $sig (Var $k)) (Var $k))
(= (nf $sig (Srt $s)) (Srt $s))
(= (nf $sig (Con $x)) (Con $x))
(= (nf $sig (Def $x))
   (let $body (def-body-of $sig $x)
     (if (is-bad $body) (Bad unknown-definition) (nf $sig $body))))
(= (nf $sig (Pi  $A $B)) (Pi  (nf $sig $A) (nf $sig $B)))
(= (nf $sig (Lam $A $b)) (Lam (nf $sig $A) (nf $sig $b)))
(= (nf $sig (Bad $e)) (Bad $e))
(= (nf $sig (App $f $a)) (nf-app $sig (nf $sig $f) (nf $sig $a)))
(= (nf-app $sig $f $a) (unify $f (Lam $A $b) (nf $sig (subst 0 $a $b)) (App $f $a)))

(= (conv $sig $x $y)
   (let $nx (nf $sig $x)
     (let $ny (nf $sig $y)
       (if (is-bad $nx) False
         (if (is-bad $ny) False
           (== $nx $ny))))))

(= (ctx-nth $i CtxNil) (Bad var-out-of-range))
(= (ctx-nth $i (CtxCons $h $t)) (if (== $i 0) $h (ctx-nth (- $i 1) $t)))
(= (ctx-type $i $ctx) (shift (+ $i 1) 0 (ctx-nth $i $ctx)))

; Predicative-with-Type-parameters PTS (same rule the indexed slices use): a
; domain may be a type (sort type) or a type-former/Type (sort kind).
(= (pts-rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi-bad-codomain)))
     (unify $sA (Srt kind)
       (unify $sB (Srt type) (Srt kind)
         (unify $sB (Srt kind) (Srt kind) (Bad pi-bad-codomain)))
       (Bad pi-domain-not-type))))

(= (infer $sig $ctx (Srt type)) (Srt kind))
(= (infer $sig $ctx (Srt kind)) (Bad kind-is-topsort))
(= (infer $sig $ctx (Bad $e)) (Bad $e))
(= (infer $sig $ctx (Var $i))  (ctx-type $i $ctx))
(= (infer $sig $ctx (Con $c))  (decl-type-of $sig $c))
(= (infer $sig $ctx (Def $c))  (decl-type-of $sig $c))
(= (infer-pi $sig $ctx $A $B)
   (let $sA (nf $sig (infer $sig $ctx $A))
     (let $sB (nf $sig (infer $sig (CtxCons $A $ctx) $B)) (pts-rule $sA $sB))))
(= (infer $sig $ctx (Pi $A $B)) (infer-pi $sig $ctx $A $B))
(= (infer-lam $sig $ctx $A $b)
   (let $sA (nf $sig (infer $sig $ctx $A))
     (unify $sA (Srt type)
        (let $tb (infer $sig (CtxCons $A $ctx) $b)
          (let $ntb (nf $sig $tb)
            (if (is-bad $ntb) (Bad lam-body-bad-type) (Pi $A $tb))))
        (unify $sA (Srt kind)
          (let $tb (infer $sig (CtxCons $A $ctx) $b)
            (let $ntb (nf $sig $tb)
              (if (is-bad $ntb) (Bad lam-body-bad-type) (Pi $A $tb))))
          (Bad lam-domain-not-a-type)))))
(= (infer $sig $ctx (Lam $A $b)) (infer-lam $sig $ctx $A $b))
(= (infer-app $sig $ctx $f $a)
   (let $tf (nf $sig (infer $sig $ctx $f))
     (unify $tf (Pi $A $B)
        (if (conv $sig (infer $sig $ctx $a) $A) (subst 0 $a $B) (Bad arg-type-mismatch))
        (Bad applied-a-non-function))))
(= (infer $sig $ctx (App $f $a)) (infer-app $sig $ctx $f $a))

(= (sort-ok $s)
   (unify $s (Srt type) True
     (unify $s (Srt kind) True False)))
(= (check-conv $sig $ctx $t $ty) (conv $sig (infer $sig $ctx $t) $ty))
(= (type-ok $sig $ctx $ty)
   (let $ITY (infer $sig $ctx $ty)
     (sort-ok (nf $sig $ITY))))
(= (check $sig $ctx $t $ty)
   (let $ok (type-ok $sig $ctx $ty)
     (if $ok (check-conv $sig $ctx $t $ty) False)))

; ---------- application head (total, for positivity / target checks) ----------
(= (app-head (App $f $a)) (app-head $f))
(= (app-head (Con $c)) $c)
(= (app-head (Def $c)) $c)
(= (app-head (Var $k)) (NoHead var))
(= (app-head (Srt $s)) (NoHead srt))
(= (app-head (Pi $A $B)) (NoHead pi))
(= (app-head (Lam $A $b)) (NoHead lam))
(= (app-head (Bad $e)) (NoHead bad))

(= (term-occurs-name $n (Var $k)) False)
(= (term-occurs-name $n (Srt $s)) False)
(= (term-occurs-name $n (Con $c)) (== $n $c))
(= (term-occurs-name $n (Def $c)) (== $n $c))
(= (term-occurs-name $n (App $f $a))
   (if (term-occurs-name $n $f) True (term-occurs-name $n $a)))
(= (term-occurs-name $n (Pi $A $B))
   (if (term-occurs-name $n $A) True (term-occurs-name $n $B)))
(= (term-occurs-name $n (Lam $A $b))
   (if (term-occurs-name $n $A) True (term-occurs-name $n $b)))
(= (term-occurs-name $n (Bad $e)) False)

; If an argument type is a recursive occurrence headed by the family, its
; parameters/indices must not themselves contain the family.  This keeps
; List A / Vec A n / Fin n legal while rejecting shapes like
; bad ((bad A) -> A).
(= (recursive-head-args-ok $n (Con $c)) True)
(= (recursive-head-args-ok $n (App $f $a))
   (if (recursive-head-args-ok $n $f)
     (if (term-occurs-name $n $a) False True)
     False))
(= (recursive-head-args-ok $n (Var $k)) False)
(= (recursive-head-args-ok $n (Srt $s)) False)
(= (recursive-head-args-ok $n (Def $c)) False)
(= (recursive-head-args-ok $n (Pi $A $B)) False)
(= (recursive-head-args-ok $n (Lam $A $b)) False)
(= (recursive-head-args-ok $n (Bad $e)) False)

; ---------- signature representation + lookup --------------------------------
; Declarations: DConst name type | DDef name type body | DAxiom name type
;             | DIndG name paramTel indexTel ctors
(= (def-body-of SNil $c) (Bad unknown-definition))
(= (def-body-of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $body (def-body-of $rest $x)))
(= (def-body-of (SCons (DConst $c $T) $rest) $x) (def-body-of $rest $x))
(= (def-body-of (SCons (DAxiom $c $T) $rest) $x) (def-body-of $rest $x))
(= (def-body-of (SCons (DIndG $n $pT $iT $ctors) $rest) $x) (def-body-of $rest $x))

(= (decl-type-of SNil $c) (Bad unknown-declaration))
(= (decl-type-of (SCons (DConst $c $T) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DDef $c $T $body) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DAxiom $c $T) $rest) $x)
   (if (== $x $c) $T (decl-type-of $rest $x)))
(= (decl-type-of (SCons (DIndG $n $pT $iT $ctors) $rest) $x)
   (if (== $x $n)
     (dindg-family-kind $pT $iT)
     (let $ct (dindg-ctor-type-of $n $pT $ctors $x)
       (if (is-bad $ct) (decl-type-of $rest $x) $ct))))

(= (is-axiom-name SNil $x) False)
(= (is-axiom-name (SCons (DAxiom $a $T) $rest) $x)
   (if (== $x $a) True (is-axiom-name $rest $x)))
(= (is-axiom-name (SCons (DConst $c $T) $rest) $x) (is-axiom-name $rest $x))
(= (is-axiom-name (SCons (DDef $c $T $body) $rest) $x) (is-axiom-name $rest $x))
(= (is-axiom-name (SCons (DIndG $n $pT $iT $ctors) $rest) $x) (is-axiom-name $rest $x))

; ---------- telescope IR + generators ----------------------------------------
(= (tel-len TNil) 0)
(= (tel-len (TCons $A $r)) (+ 1 (tel-len $r)))
(= (tel-to-pi TNil $tail) $tail)
(= (tel-to-pi (TCons $A $r) $tail) (Pi $A (tel-to-pi $r $tail)))

(= (apply-args $f ArgsNil) $f)
(= (apply-args $f (ArgsCons $a $r)) (apply-args (App $f $a) $r))

(= (app-args-list (App $f $a)) (app-args-snoc (app-args-list $f) $a))
(= (app-args-list (Con $c)) ArgsNil)
(= (app-args-list (Def $c)) ArgsNil)
(= (app-args-list (Var $k)) ArgsNil)
(= (app-args-list (Srt $s)) ArgsNil)
(= (app-args-list (Pi $A $B)) ArgsNil)
(= (app-args-list (Lam $A $b)) ArgsNil)
(= (app-args-list (Bad $e)) ArgsNil)
(= (app-args-snoc ArgsNil $a) (ArgsCons $a ArgsNil))
(= (app-args-snoc (ArgsCons $x $r) $a) (ArgsCons $x (app-args-snoc $r $a)))

; de Bruijn refs to the params from inside ctx (params ++ args):
;   param j (0 = first/outermost declared) sits at Var (np + na - 1 - j)
(= (param-var-args $np $na) (param-var-args-go 0 $np $na))
(= (param-var-args-go $j $np $na)
   (if (== $j $np) ArgsNil
     (ArgsCons (Var (- (- (+ $np $na) 1) $j)) (param-var-args-go (+ $j 1) $np $na))))

(= (args-prefix-eq $k $args $expected)
   (if (== $k 0) True
     (unify $args (ArgsCons $a $ar)
       (unify $expected (ArgsCons $e $er)
         (if (== $a $e) (args-prefix-eq (- $k 1) $ar $er) False)
         False)
       False)))

(= (dindg-family-kind $paramTel $indexTel)
   (tel-to-pi $paramTel (tel-to-pi $indexTel (Srt type))))

(= (dindg-ctor-type $name $paramTel (GCtor $c $argTel $resultIdx))
   (let $np (tel-len $paramTel)
     (let $na (tel-len $argTel)
       (tel-to-pi $paramTel
         (tel-to-pi $argTel
           (apply-args (apply-args (Con $name) (param-var-args $np $na)) $resultIdx))))))

(= (dindg-ctor-type-of $name $paramTel GCNil $x) (Bad unknown-constructor))
(= (dindg-ctor-type-of $name $paramTel (GCtors (GCtor $c $aT $ri) $rest) $x)
   (if (== $x $c)
     (dindg-ctor-type $name $paramTel (GCtor $c $aT $ri))
     (dindg-ctor-type-of $name $paramTel $rest $x)))

; ---------- admission for DIndG ----------------------------------------------
(= (gctor-has-name $n GCNil) False)
(= (gctor-has-name $n (GCtors (GCtor $c $aT $ri) $rest))
   (if (== $n $c) True (gctor-has-name $n $rest)))
(= (unique-gctors GCNil) True)
(= (unique-gctors (GCtors (GCtor $c $aT $ri) $rest))
   (if (gctor-has-name $c $rest) False (unique-gctors $rest)))

; strict positivity: in each ctor arg type, the family head is allowed as the
; recursive position, but the family must not occur in any other position.
; Parameterized families also require uniform parameters in recursive
; occurrences: e.g. List A may recurse on List A, not List B.
(= (gctor-strict-pos-arg $n $np $na $A)
   (if (== (app-head $A) $n)
     (if (args-prefix-eq $np (app-args-list $A) (param-var-args $np $na))
       (recursive-head-args-ok $n $A)
       False)
     (if (term-occurs-name $n $A) False True)))
(= (gtel-strict-pos-go $n $np $na TNil) True)
(= (gtel-strict-pos-go $n $np $na (TCons $A $r))
   (if (gctor-strict-pos-arg $n $np $na $A)
     (gtel-strict-pos-go $n $np (+ $na 1) $r)
     False))
(= (gtel-strict-pos $n $np $tel) (gtel-strict-pos-go $n $np 0 $tel))
(= (gctors-strict-pos $n $np GCNil) True)
(= (gctors-strict-pos $n $np (GCtors (GCtor $c $aT $ri) $rest))
   (if (gtel-strict-pos $n $np $aT) (gctors-strict-pos $n $np $rest) False))

; each GENERATED constructor type must itself typecheck (infer to a sort) in the
; signature with the family declared — the "generated artifacts are checked" rule.
(= (gctors-types-ok $sig $name $pT GCNil) True)
(= (gctors-types-ok $sig $name $pT (GCtors (GCtor $c $aT $ri) $rest))
   (let $ct (dindg-ctor-type $name $pT (GCtor $c $aT $ri))
     (if (sort-ok (nf $sig (infer $sig CtxNil $ct)))
       (gctors-types-ok $sig $name $pT $rest)
       False)))

(= (wf-decl $prefix (DConst $n $T))
   (let $IT (infer $prefix CtxNil $T) (sort-ok (nf $prefix $IT))))
(= (wf-decl $prefix (DDef $n $T $body))
   (if (wf-decl $prefix (DConst $n $T)) (check-conv $prefix CtxNil $body $T) False))
(= (wf-decl $prefix (DAxiom $n $T)) (wf-decl $prefix (DConst $n $T)))
(= (wf-decl $prefix (DIndG $n $pT $iT $ctors))
   (let $fk (dindg-family-kind $pT $iT)
     (if (unique-gctors $ctors)
       (if (sort-ok (nf $prefix (infer $prefix CtxNil $fk)))
         (if (gctors-strict-pos $n (tel-len $pT) $ctors)
           (gctors-types-ok (SCons (DConst $n $fk) $prefix) $n $pT $ctors)
           False)
         False)
       False)))

; ---------- uniqueness of names across the signature -------------------------
(= (decl-has-name $n (DConst $c $T)) (== $n $c))
(= (decl-has-name $n (DDef $c $T $b)) (== $n $c))
(= (decl-has-name $n (DAxiom $c $T)) (== $n $c))
(= (decl-has-name $n (DIndG $i $pT $iT $ctors))
   (if (== $n $i) True (gctor-has-name $n $ctors)))
(= (sig-has-name $n SNil) False)
(= (sig-has-name $n (SCons $d $rest))
   (if (decl-has-name $n $d) True (sig-has-name $n $rest)))
(= (gctors-disjoint-rest GCNil $rest) True)
(= (gctors-disjoint-rest (GCtors (GCtor $c $aT $ri) $cs) $rest)
   (if (sig-has-name $c $rest) False (gctors-disjoint-rest $cs $rest)))
(= (decl-names-disjoint-rest (DConst $n $T) $rest) (if (sig-has-name $n $rest) False True))
(= (decl-names-disjoint-rest (DDef $n $T $b) $rest) (if (sig-has-name $n $rest) False True))
(= (decl-names-disjoint-rest (DAxiom $n $T) $rest) (if (sig-has-name $n $rest) False True))
(= (decl-names-disjoint-rest (DIndG $n $pT $iT $ctors) $rest)
   (if (sig-has-name $n $rest) False
     (if (unique-gctors $ctors) (gctors-disjoint-rest $ctors $rest) False)))
(= (unique-sig SNil) True)
(= (unique-sig (SCons $d $rest))
   (if (decl-names-disjoint-rest $d $rest) (unique-sig $rest) False))

(= (wf-sig-prefix $prefix SNil) True)
(= (wf-sig-prefix $prefix (SCons $d $rest))
   (if (wf-decl $prefix $d) (wf-sig-prefix (SCons $d $prefix) $rest) False))
(= (sig-admitted $sig)
   (if (unique-sig $sig) (wf-sig-prefix SNil $sig) False))

; =============================================================================
; good-sig-G : Nat, List, Vec, Fin, Id — all declared via the ONE DIndG form.
; (nat/lst must precede vec/fin because their index/arg types mention them.)
; =============================================================================
(= (good-sig-G)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG lst (TCons (Srt type) TNil) TNil
            (GCtors (GCtor lnil TNil ArgsNil)
              (GCtors (GCtor lcons
                        (TCons (Var 0) (TCons (App (Con lst) (Var 1)) TNil))
                        ArgsNil) GCNil)))
   (SCons (DIndG vec (TCons (Srt type) TNil) (TCons (Con nat) TNil)
            (GCtors (GCtor vnil TNil (ArgsCons (Con z) ArgsNil))
              (GCtors (GCtor vcons
                        (TCons (Con nat) (TCons (Var 1) (TCons (App (App (Con vec) (Var 2)) (Var 1)) TNil)))
                        (ArgsCons (App (Con s) (Var 2)) ArgsNil)) GCNil)))
   (SCons (DIndG fin TNil (TCons (Con nat) TNil)
            (GCtors (GCtor fz (TCons (Con nat) TNil) (ArgsCons (App (Con s) (Var 0)) ArgsNil))
              (GCtors (GCtor fs (TCons (Con nat) (TCons (App (Con fin) (Var 0)) TNil))
                        (ArgsCons (App (Con s) (Var 1)) ArgsNil)) GCNil)))
   (SCons (DIndG Id (TCons (Srt type) (TCons (Var 0) TNil)) (TCons (Var 1) TNil)
            (GCtors (GCtor refl TNil (ArgsCons (Var 0) ArgsNil)) GCNil))
          SNil))))))

; Pair stresses two uniform parameters and two non-recursive constructor args.
(= (pair-sig-G)
   (SCons (DIndG pair (TCons (Srt type) (TCons (Srt type) TNil)) TNil
            (GCtors (GCtor mkpair (TCons (Var 1) (TCons (Var 1) TNil)) ArgsNil) GCNil))
          SNil))

(= (pair-nat-sig-G)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG pair (TCons (Srt type) (TCons (Srt type) TNil)) TNil
            (GCtors (GCtor mkpair (TCons (Var 1) (TCons (Var 1) TNil)) ArgsNil) GCNil))
          SNil)))

(= (axiom-nat-sig-G)
   (SCons (DIndG nat TNil TNil
              (GCtors (GCtor z TNil ArgsNil)
                (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
     (SCons (DAxiom axN (Con nat))
            SNil)))

; ---------- generated family kinds match the slices' hand-written kinds -------
!(assertEqual (decl-type-of (good-sig-G) nat) (Srt type))
!(assertEqual (decl-type-of (good-sig-G) lst) (Pi (Srt type) (Srt type)))
!(assertEqual (decl-type-of (good-sig-G) vec) (Pi (Srt type) (Pi (Con nat) (Srt type))))
!(assertEqual (decl-type-of (good-sig-G) fin) (Pi (Con nat) (Srt type)))
!(assertEqual (decl-type-of (good-sig-G) Id) (Pi (Srt type) (Pi (Var 0) (Pi (Var 1) (Srt type)))))
!(assertEqual (decl-type-of (pair-sig-G) pair) (Pi (Srt type) (Pi (Srt type) (Srt type))))

; ---------- generated constructor types match the hand-written ones -----------
!(assertEqual (decl-type-of (good-sig-G) z) (Con nat))
!(assertEqual (decl-type-of (good-sig-G) s) (Pi (Con nat) (Con nat)))
!(assertEqual (decl-type-of (good-sig-G) lnil) (Pi (Srt type) (App (Con lst) (Var 0))))
!(assertEqual (decl-type-of (good-sig-G) lcons)
   (Pi (Srt type) (Pi (Var 0) (Pi (App (Con lst) (Var 1)) (App (Con lst) (Var 2))))))
!(assertEqual (decl-type-of (good-sig-G) vnil)
   (Pi (Srt type) (App (App (Con vec) (Var 0)) (Con z))))
!(assertEqual (decl-type-of (good-sig-G) vcons)
   (Pi (Srt type) (Pi (Con nat) (Pi (Var 1) (Pi (App (App (Con vec) (Var 2)) (Var 1))
     (App (App (Con vec) (Var 3)) (App (Con s) (Var 2))))))))
!(assertEqual (decl-type-of (good-sig-G) fz)
   (Pi (Con nat) (App (Con fin) (App (Con s) (Var 0)))))
!(assertEqual (decl-type-of (good-sig-G) fs)
   (Pi (Con nat) (Pi (App (Con fin) (Var 0)) (App (Con fin) (App (Con s) (Var 1))))))
!(assertEqual (decl-type-of (good-sig-G) refl)
   (Pi (Srt type) (Pi (Var 0) (App (App (App (Con Id) (Var 1)) (Var 0)) (Var 0)))))
!(assertEqual (decl-type-of (pair-sig-G) mkpair)
   (Pi (Srt type) (Pi (Srt type) (Pi (Var 1) (Pi (Var 1)
     (App (App (Con pair) (Var 3)) (Var 2)))))))

; ---------- the whole telescope signature is admitted -------------------------
!(assertEqual (sig-admitted (good-sig-G)) True)
!(assertEqual (sig-admitted (pair-sig-G)) True)
!(assertEqual (sig-admitted (pair-nat-sig-G)) True)
!(assertEqual (sig-admitted (axiom-nat-sig-G)) True)

; ---------- negatives ---------------------------------------------------------
; non-strictly-positive constructor (mkBad : (bad -> bad) -> bad) is rejected
(= (bad-pos-sig)
   (SCons (DIndG bad TNil TNil
            (GCtors (GCtor mkBad (TCons (Pi (Con bad) (Con bad)) TNil) ArgsNil) GCNil))
          SNil))
!(assertEqual (sig-admitted (bad-pos-sig)) False)

; A recursive occurrence headed by the family is allowed only when its
; parameters/indices are recursive-free.  This nested negative occurrence was
; the Phase-1 audit hole: mkBad : bad ((bad A) -> A) -> bad A.
(= (bad-nested-pos-sig)
   (SCons (DIndG bad (TCons (Srt type) TNil) TNil
            (GCtors (GCtor mkBad
              (TCons (App (Con bad) (Pi (App (Con bad) (Var 0)) (Var 1))) TNil)
              ArgsNil) GCNil))
          SNil))
!(assertEqual (sig-admitted (bad-nested-pos-sig)) False)

; Parameters are uniform: a family declared as w A may not recursively mention
; w at a different parameter, even if the occurrence is strictly positive.
(= (bad-param-change-sig)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG w (TCons (Srt type) TNil) TNil
            (GCtors (GCtor mkW (TCons (App (Con w) (Con nat)) TNil) ArgsNil) GCNil))
          SNil)))
!(assertEqual (sig-admitted (bad-param-change-sig)) False)

; duplicate constructor names are rejected
(= (dup-ctor-sig)
   (SCons (DIndG twoc TNil TNil
            (GCtors (GCtor c1 TNil ArgsNil) (GCtors (GCtor c1 TNil ArgsNil) GCNil)))
          SNil))
!(assertEqual (sig-admitted (dup-ctor-sig)) False)

; an ill-typed family kind (index type references a non-existent constant) is rejected
(= (bad-kind-sig)
   (SCons (DIndG bk TNil (TCons (Con nope) TNil)
            (GCtors (GCtor bkc TNil (ArgsCons (Con z) ArgsNil)) GCNil))
          SNil))
!(assertEqual (sig-admitted (bad-kind-sig)) False)

; a constructor whose generated type is ill-typed (wrong index count: vnil given
; an extra index) is rejected by gctors-types-ok
(= (bad-ctor-sig)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG vv (TCons (Srt type) TNil) (TCons (Con nat) TNil)
            (GCtors (GCtor vv0 TNil (ArgsCons (Con z) (ArgsCons (Con z) ArgsNil))) GCNil))
          SNil)))
!(assertEqual (sig-admitted (bad-ctor-sig)) False)

; =============================================================================
; PHASE 2: generated eliminator + branch TYPES (no iota/computation yet).
;   eliminator type =
;     Pi Delta. Pi (P : Pi Xi. (Name Delta Xi) -> Type).
;       branch_1 -> ... -> branch_k -> Pi Xi. Pi (x : Name Delta Xi). P Xi x
;   branch_i for  c_i : Pi Gamma_i. Name Delta resultIdx_i  =
;     Pi Gamma_i. [for each recursive arg: Pi (IH : P idx_args arg)] . P resultIdx (c_i Delta Gamma)
; Built by incremental descent (shift P/ctorApp by 1 per nonrec arg, by 2 per rec
; arg + its IH) so de Bruijn is correct by construction.
; =============================================================================

(= (shift-tel $d $c TNil) TNil)
(= (shift-tel $d $c (TCons $A $r)) (TCons (shift $d $c $A) (shift-tel $d (+ $c 1) $r)))

(= (tel-var-args $count $offset) (tel-var-args-go 0 $count $offset))
(= (tel-var-args-go $j $count $offset)
   (if (== $j $count) ArgsNil
     (ArgsCons (Var (- (- (+ $count $offset) 1) $j)) (tel-var-args-go (+ $j 1) $count $offset))))

; NB: equations must be non-overlapping (no `(drop-n 0 $args)` clause) — overlap
; makes CeTTa return duplicate results, which breaks the lockstep `if`.
(= (drop-n $k ArgsNil) ArgsNil)
(= (drop-n $k (ArgsCons $a $r)) (if (== $k 0) (ArgsCons $a $r) (drop-n (- $k 1) $r)))

; motive  P : Pi Xi. (Name Delta Xi) -> Type   (in context Delta)
(= (dindg-motive-type $name $np $indexTel)
   (let $nx (tel-len $indexTel)
     (tel-to-pi $indexTel
       (Pi (apply-args (apply-args (Con $name) (tel-var-args $np $nx)) (tel-var-args $nx 0))
           (Srt type)))))

; branch type for one constructor, with $pb branches already bound before it.
(= (dindg-branch-type $name $np (GCtor $c $argTel $resultIdx) $pb)
   (let $na (tel-len $argTel)
     (let $R (apply-args (apply-args (Con $name) (tel-var-args $np $na)) $resultIdx)
       (let $Tbody (tel-to-pi $argTel $R)
         (let $Tstart (shift (+ 1 $pb) 0 $Tbody)
           (let $Pinit (Var $pb)
             (let $cAppInit (apply-args (Con $c) (tel-var-args $np (+ 1 $pb)))
               (dindg-branch-go $name $np $Pinit $cAppInit $Tstart))))))))

(= (dindg-branch-go $name $np $P $cApp $T)
   (if (== (app-head $T) $name)
     (App (apply-args $P (drop-n $np (app-args-list $T))) $cApp)
     (unify $T (Pi $A $B)
       (if (== (app-head $A) $name)
         (Pi $A
           (Pi (App (apply-args (shift 1 0 $P) (drop-n $np (app-args-list (shift 1 0 $A)))) (Var 0))
             (dindg-branch-go $name $np (shift 2 0 $P) (App (shift 2 0 $cApp) (Var 1)) (shift 1 0 $B))))
         (Pi $A
           (dindg-branch-go $name $np (shift 1 0 $P) (App (shift 1 0 $cApp) (Var 0)) $B)))
       (Bad branch-shape))))

; conclusion  Pi Xi. Pi (x : Name Delta Xi). P Xi x   (in ctx Delta,P,k-branches)
(= (dindg-elim-concl $name $np $nx $indexTel $k)
   (tel-to-pi (shift-tel (+ 1 $k) 0 $indexTel)
     (Pi (apply-args (apply-args (Con $name) (tel-var-args $np (+ (+ $nx $k) 1))) (tel-var-args $nx 0))
       (App (apply-args (Var (+ (+ $nx $k) 1)) (tel-var-args $nx 1)) (Var 0)))))

(= (dindg-branches-pi $name $np GCNil $pb $concl) $concl)
(= (dindg-branches-pi $name $np (GCtors $ctor $rest) $pb $concl)
   (Pi (dindg-branch-type $name $np $ctor $pb)
       (dindg-branches-pi $name $np $rest (+ $pb 1) $concl)))

(= (gctors-len GCNil) 0)
(= (gctors-len (GCtors $c $r)) (+ 1 (gctors-len $r)))

(= (find-dindg SNil $name) (Bad unknown-inductive))
(= (find-dindg (SCons (DIndG $n $pT $iT $ctors) $rest) $name)
   (if (== $n $name) (DIndG $n $pT $iT $ctors) (find-dindg $rest $name)))
(= (find-dindg (SCons (DConst $c $T) $rest) $name) (find-dindg $rest $name))
(= (find-dindg (SCons (DDef $c $T $b) $rest) $name) (find-dindg $rest $name))
(= (find-dindg (SCons (DAxiom $c $T) $rest) $name) (find-dindg $rest $name))

(= (dindg-elim-type $sig $name)
   (let $decl (find-dindg $sig $name)
     (unify $decl (DIndG $n $pT $iT $ctors)
       (let $np (tel-len $pT)
         (let $nx (tel-len $iT)
           (let $k (gctors-len $ctors)
             (tel-to-pi $pT
               (Pi (dindg-motive-type $name $np $iT)
                 (dindg-branches-pi $name $np $ctors 0
                   (dindg-elim-concl $name $np $nx $iT $k)))))))
       (Bad unknown-inductive))))

; the generated eliminator type itself typechecks (Phase-2 lockstep predicate)
(= (dindg-elim-typechecks $sig $name)
   (let $et (dindg-elim-type $sig $name)
     (if (is-bad $et) False (sort-ok (nf $sig (infer $sig CtxNil $et))))))

; Strengthened admission view: first admit the signature, then require every
; DIndG declaration in that admitted signature to have a generated eliminator
; type that itself typechecks.  This is factored into small helpers because the
; earlier inline fold was evaluator-sensitive in CeTTa.
(= (dindg-elims-ok $sig SNil) True)
(= (dindg-elims-ok $sig (SCons (DIndG $n $pT $iT $ctors) $rest))
   (if (dindg-elim-typechecks $sig $n) (dindg-elims-ok $sig $rest) False))
(= (dindg-elims-ok $sig (SCons (DConst $n $T) $rest)) (dindg-elims-ok $sig $rest))
(= (dindg-elims-ok $sig (SCons (DDef $n $T $b) $rest)) (dindg-elims-ok $sig $rest))
(= (dindg-elims-ok $sig (SCons (DAxiom $n $T) $rest)) (dindg-elims-ok $sig $rest))
(= (sig-admitted-with-elims $sig)
   (if (sig-admitted $sig) (dindg-elims-ok $sig $sig) False))

; ---- REPLAY: generated eliminator types equal the known eliminator shapes ----
; Nat recursor:
!(assertEqual (dindg-elim-type (good-sig-G) nat)
   (Pi (Pi (Con nat) (Srt type)) (Pi (App (Var 0) (Con z)) (Pi (Pi (Con nat) (Pi (App (Var 2) (Var 0)) (App (Var 3) (App (Con s) (Var 1))))) (Pi (Con nat) (App (Var 3) (Var 0)))))))
; List A recursor (parameter + recursive arg with IH):
!(assertEqual (dindg-elim-type (good-sig-G) lst)
   (Pi (Srt type) (Pi (Pi (App (Con lst) (Var 0)) (Srt type)) (Pi (App (Var 0) (App (Con lnil) (Var 1))) (Pi (Pi (Var 2) (Pi (App (Con lst) (Var 3)) (Pi (App (Var 3) (Var 0)) (App (Var 4) (App (App (App (Con lcons) (Var 5)) (Var 2)) (Var 1)))))) (Pi (App (Con lst) (Var 3)) (App (Var 3) (Var 0))))))))
; Vec A n eliminator (indexed; matches the hand-written indexed-vec-elim-type):
!(assertEqual (dindg-elim-type (good-sig-G) vec)
   (Pi (Srt type) (Pi (Pi (Con nat) (Pi (App (App (Con vec) (Var 1)) (Var 0)) (Srt type))) (Pi (App (App (Var 0) (Con z)) (App (Con vnil) (Var 1))) (Pi (Pi (Con nat) (Pi (Var 3) (Pi (App (App (Con vec) (Var 4)) (Var 1)) (Pi (App (App (Var 4) (Var 2)) (Var 0)) (App (App (Var 5) (App (Con s) (Var 3))) (App (App (App (App (Con vcons) (Var 6)) (Var 3)) (Var 2)) (Var 1))))))) (Pi (Con nat) (Pi (App (App (Con vec) (Var 4)) (Var 0)) (App (App (Var 4) (Var 1)) (Var 0)))))))))
; Fin n eliminator (indexed, no params):
!(assertEqual (dindg-elim-type (good-sig-G) fin)
   (Pi (Pi (Con nat) (Pi (App (Con fin) (Var 0)) (Srt type))) (Pi (Pi (Con nat) (App (App (Var 1) (App (Con s) (Var 0))) (App (Con fz) (Var 0)))) (Pi (Pi (Con nat) (Pi (App (Con fin) (Var 0)) (Pi (App (App (Var 3) (Var 1)) (Var 0)) (App (App (Var 4) (App (Con s) (Var 2))) (App (App (Con fs) (Var 2)) (Var 1)))))) (Pi (Con nat) (Pi (App (Con fin) (Var 0)) (App (App (Var 4) (Var 1)) (Var 0))))))))
; Id eliminator == J, generated purely from the Id DIndG declaration (the keystone payoff):
!(assertEqual (dindg-elim-type (good-sig-G) Id)
   (Pi (Srt type) (Pi (Var 0) (Pi (Pi (Var 1) (Pi (App (App (App (Con Id) (Var 2)) (Var 1)) (Var 0)) (Srt type))) (Pi (App (App (Var 0) (Var 1)) (App (App (Con refl) (Var 2)) (Var 1))) (Pi (Var 3) (Pi (App (App (App (Con Id) (Var 4)) (Var 3)) (Var 0)) (App (App (Var 3) (Var 1)) (Var 0)))))))))
; Pair A B eliminator: Pi A B. Pi P:(pair A B)->Type.
;   (Pi x:A. Pi y:B. P (mkpair A B x y)) -> Pi p:pair A B. P p
!(assertEqual (dindg-elim-type (pair-sig-G) pair)
   (Pi (Srt type) (Pi (Srt type)
     (Pi (Pi (App (App (Con pair) (Var 1)) (Var 0)) (Srt type))
       (Pi (Pi (Var 2) (Pi (Var 2)
         (App (Var 2) (App (App (App (App (Con mkpair) (Var 4)) (Var 3)) (Var 1)) (Var 0)))))
         (Pi (App (App (Con pair) (Var 3)) (Var 2)) (App (Var 2) (Var 0))))))))

; ---- lockstep (verified per-family): every generated eliminator type typechecks
;      via the decidable predicate dindg-elim-typechecks.  This is the Phase-2
;      "no claimed eliminator without complete branch typing" property, checked
;      for each family below (Nat, List, Pair, indexed Vec/Fin, and J-for-Id).
!(assertEqual (dindg-elim-typechecks (good-sig-G) nat) True)
!(assertEqual (dindg-elim-typechecks (good-sig-G) lst) True)
!(assertEqual (dindg-elim-typechecks (good-sig-G) vec) True)
!(assertEqual (dindg-elim-typechecks (good-sig-G) fin) True)
!(assertEqual (dindg-elim-typechecks (good-sig-G) Id) True)
!(assertEqual (dindg-elim-typechecks (pair-sig-G) pair) True)
!(assertEqual (sig-admitted-with-elims (good-sig-G)) True)
!(assertEqual (sig-admitted-with-elims (pair-sig-G)) True)
!(assertEqual (sig-admitted-with-elims (bad-ctor-sig)) False)

; ---- negative-replay: the generator does NOT emit a wrong recursive-IH index --
; (the Vec cons IH must be P n xs = (App (App (Var 4) (Var 2)) (Var 0)); a variant
;  with the IH at P (s n) xs is wrong and must NOT be what we generate)
!(assertEqual
   (== (dindg-elim-type (good-sig-G) vec)
       (Pi (Srt type) (Pi (Pi (Con nat) (Pi (App (App (Con vec) (Var 1)) (Var 0)) (Srt type))) (Pi (App (App (Var 0) (Con z)) (App (Con vnil) (Var 1))) (Pi (Pi (Con nat) (Pi (Var 3) (Pi (App (App (Con vec) (Var 4)) (Var 1)) (Pi (App (App (Var 4) (App (Con s) (Var 2))) (Var 0)) (App (App (Var 5) (App (Con s) (Var 3))) (App (App (App (App (Con vcons) (Var 6)) (Var 3)) (Var 2)) (Var 1))))))) (Pi (Con nat) (Pi (App (App (Con vec) (Var 4)) (Var 0)) (App (App (Var 4) (Var 1)) (Var 0)))))))))
   False)

; =============================================================================
; PHASE 3: generated constructor-headed iota (computation) from the SAME DIndG
; descriptors.  The generic eliminator term is
;   (IndG name params motive cases indices scrut)
; and its iota fires when scrut is a constructor application:
;   IndG name params P cases idx (c <param-args> <ctor-args>)
;     ~> body_c applied to the non-param ctor-args, each recursive arg also
;        applied to its IH = (IndG name params P cases <rec-idx> <rec-arg>).
; Non-constructor (variable / stuck) scrutinees stay stuck.  J for Id is just
; this iota at the refl constructor (the diagonal rule) — no special rule.
; Mirrors the proven branch-apply-pi structure (dindpi_generic_v0).
; =============================================================================

; ---- Args / Cases plumbing --------------------------------------------------
(= (args-len ArgsNil) 0)
(= (args-len (ArgsCons $a $r)) (+ 1 (args-len $r)))
(= (shift-args $d $c ArgsNil) ArgsNil)
(= (shift-args $d $c (ArgsCons $a $r)) (ArgsCons (shift $d $c $a) (shift-args $d $c $r)))
(= (subst-args $j $s ArgsNil) ArgsNil)
(= (subst-args $j $s (ArgsCons $a $r)) (ArgsCons (subst $j $s $a) (subst-args $j $s $r)))
(= (nf-args $sig ArgsNil) ArgsNil)
(= (nf-args $sig (ArgsCons $a $r)) (ArgsCons (nf $sig $a) (nf-args $sig $r)))
(= (case-body-of CasesNil $ctor) (Bad missing-case))
(= (case-body-of (Cases (Case $c $body) $rest) $ctor)
   (if (== $c $ctor) $body (case-body-of $rest $ctor)))
(= (case-has-name CasesNil $ctor) False)
(= (case-has-name (Cases (Case $c $body) $rest) $ctor)
   (if (== $c $ctor) True (case-has-name $rest $ctor)))
(= (unique-cases CasesNil) True)
(= (unique-cases (Cases (Case $c $body) $rest))
   (if (case-has-name $rest $c) False (unique-cases $rest)))
(= (ctors-have-cases GCNil $cases) True)
(= (ctors-have-cases (GCtors (GCtor $c $aT $ri) $rest) $cases)
   (if (case-has-name $cases $c) (ctors-have-cases $rest $cases) False))
(= (cases-known-ctors CasesNil $ctors) True)
(= (cases-known-ctors (Cases (Case $c $body) $rest) $ctors)
   (if (gctor-has-name $c $ctors) (cases-known-ctors $rest $ctors) False))
(= (cases-exact-for-ctors $ctors $cases)
   (if (unique-cases $cases)
     (if (ctors-have-cases $ctors $cases) (cases-known-ctors $cases $ctors) False)
     False))
(= (shift-cases $d $c CasesNil) CasesNil)
(= (shift-cases $d $c (Cases (Case $cn $body) $rest))
   (Cases (Case $cn (shift $d $c $body)) (shift-cases $d $c $rest)))
(= (subst-cases $j $s CasesNil) CasesNil)
(= (subst-cases $j $s (Cases (Case $cn $body) $rest))
   (Cases (Case $cn (subst $j $s $body)) (subst-cases $j $s $rest)))
(= (nf-cases $sig CasesNil) CasesNil)
(= (nf-cases $sig (Cases (Case $cn $body) $rest))
   (Cases (Case $cn (nf $sig $body)) (nf-cases $sig $rest)))

; instantiate the leading Pi-telescope of a ctor type with a list of param args
(= (inst-tel-args $T ArgsNil) $T)
(= (inst-tel-args (Pi $A $B) (ArgsCons $arg $rest)) (inst-tel-args (subst 0 $arg $B) $rest))

; Typed IndG checking: interpret the generated eliminator type as the single
; typing specification, then apply it to params, motive, cases, indices, and
; scrutinee.  This deliberately avoids a parallel hand-written eliminator rule.
(= (infer-apply-arg $sig $ctx $T $arg)
   (let $nT (nf $sig $T)
     (infer-apply-arg-nf $sig $ctx $nT $arg)))
(= (infer-apply-arg-nf $sig $ctx $T $arg)
   (unify $T (Pi $A $B)
     (if (check $sig $ctx $arg $A) (nf $sig (subst 0 $arg $B)) (Bad indg-arg-type-mismatch))
     (unify $T (Bad $e) (Bad $e) (Bad indg-expected-pi))))
(= (infer-apply-args $sig $ctx $T ArgsNil) (nf $sig $T))
(= (infer-apply-args $sig $ctx $T (ArgsCons $arg $rest))
   (let $T1 (infer-apply-arg $sig $ctx $T $arg)
     (if (is-bad $T1) $T1 (infer-apply-args $sig $ctx $T1 $rest))))
(= (infer-apply-cases $sig $ctx $T GCNil $cases) (nf $sig $T))
(= (infer-apply-cases $sig $ctx $T (GCtors (GCtor $c $aT $ri) $rest) $cases)
   (let $body (case-body-of $cases $c)
     (let $T1 (infer-apply-arg $sig $ctx $T $body)
       (if (is-bad $T1) $T1 (infer-apply-cases $sig $ctx $T1 $rest $cases)))))

(= (infer-indg $sig $ctx $name $params $motive $cases $indices $scrut)
   (let $decl (find-dindg $sig $name)
     (unify $decl (DIndG $n $pT $iT $ctors)
       (infer-indg-cases $sig $ctx $name $params $motive $cases $indices $scrut $ctors)
       (Bad indg-unknown-family))))
(= (infer-indg-cases $sig $ctx $name $params $motive $cases $indices $scrut $ctors)
   (if (cases-exact-for-ctors $ctors $cases)
     (let $T0 (dindg-elim-type $sig $name)
       (infer-indg-params $sig $ctx $name $params $motive $cases $indices $scrut $ctors $T0))
     (Bad indg-cases-not-exact)))
(= (infer-indg-params $sig $ctx $name $params $motive $cases $indices $scrut $ctors $T0)
   (let $T1 (infer-apply-args $sig $ctx $T0 $params)
     (if (is-bad $T1) $T1
       (infer-indg-motive $sig $ctx $motive $cases $indices $scrut $ctors $T1))))
(= (infer-indg-motive $sig $ctx $motive $cases $indices $scrut $ctors $T1)
   (let $T2 (infer-apply-arg $sig $ctx $T1 $motive)
     (if (is-bad $T2) $T2
       (infer-indg-cases-typed $sig $ctx $cases $indices $scrut $ctors $T2))))
(= (infer-indg-cases-typed $sig $ctx $cases $indices $scrut $ctors $T2)
   (let $T3 (infer-apply-cases $sig $ctx $T2 $ctors $cases)
     (if (is-bad $T3) $T3
       (infer-indg-indices $sig $ctx $indices $scrut $T3))))
(= (infer-indg-indices $sig $ctx $indices $scrut $T3)
   (let $T4 (infer-apply-args $sig $ctx $T3 $indices)
     (if (is-bad $T4) $T4
       (infer-indg-scrut $sig $ctx $scrut $T4))))
(= (infer-indg-scrut $sig $ctx $scrut $T4)
   (infer-apply-arg $sig $ctx $T4 $scrut))

; ---- IndG term: de Bruijn + nf dispatch + head/args totality ----------------
(= (shift $d $c (IndG $name $params $motive $cases $indices $scrut))
   (IndG $name (shift-args $d $c $params) (shift $d $c $motive) (shift-cases $d $c $cases)
         (shift-args $d $c $indices) (shift $d $c $scrut)))
(= (subst $j $s (IndG $name $params $motive $cases $indices $scrut))
   (IndG $name (subst-args $j $s $params) (subst $j $s $motive) (subst-cases $j $s $cases)
         (subst-args $j $s $indices) (subst $j $s $scrut)))
(= (nf $sig (IndG $name $params $motive $cases $indices $scrut))
   (nf-indg $sig $name (nf-args $sig $params) (nf $sig $motive) (nf-cases $sig $cases)
            (nf-args $sig $indices) (nf $sig $scrut)))
(= (app-head (IndG $name $params $motive $cases $indices $scrut)) (NoHead indg))
(= (app-args-list (IndG $name $params $motive $cases $indices $scrut)) ArgsNil)
(= (infer $sig $ctx (IndG $name $params $motive $cases $indices $scrut))
   (infer-indg $sig $ctx $name $params $motive $cases $indices $scrut))

; ---- DIndG family lookups for the iota --------------------------------------
(= (ind-gctors-of $sig $name)
   (let $d (find-dindg $sig $name) (unify $d (DIndG $n $pT $iT $ctors) $ctors (Bad unknown-inductive))))
(= (paramtel-of $sig $name)
   (let $d (find-dindg $sig $name) (unify $d (DIndG $n $pT $iT $ctors) $pT (Bad unknown-inductive))))
(= (gctor-full-type $name $paramTel GCNil $x) (Bad unknown-constructor))
(= (gctor-full-type $name $paramTel (GCtors (GCtor $c $aT $ri) $rest) $x)
   (if (== $x $c) (dindg-ctor-type $name $paramTel (GCtor $c $aT $ri))
     (gctor-full-type $name $paramTel $rest $x)))

; ---- the iota ---------------------------------------------------------------
(= (indg-stuck $name $params $motive $cases $indices $scrut)
   (IndG $name $params $motive $cases $indices $scrut))
(= (nf-indg $sig $name $params $motive $cases $indices $scrut)
   (let $ctor (app-head $scrut)
     (let $pT (paramtel-of $sig $name)
       (let $gctors (ind-gctors-of $sig $name)
         (nf-indg-cases $sig $name $params $motive $cases $indices $scrut $ctor $pT $gctors)))))

(= (nf-indg-cases $sig $name $params $motive $cases $indices $scrut $ctor $pT $gctors)
   (if (cases-exact-for-ctors $gctors $cases)
     (nf-indg-ct $sig $name $params $motive $cases $indices $scrut $ctor $pT $gctors
       (gctor-full-type $name $pT $gctors $ctor))
     (indg-stuck $name $params $motive $cases $indices $scrut)))

(= (nf-indg-ct $sig $name $params $motive $cases $indices $scrut $ctor $pT $gctors $CT0)
   (unify $CT0 (Bad $e)
     (indg-stuck $name $params $motive $cases $indices $scrut)
     (nf-indg-params $sig $name $params $motive $cases $indices $scrut $ctor $CT0 (app-args-list $scrut))))

(= (nf-indg-params $sig $name $params $motive $cases $indices $scrut $ctor $CT0 $scrutArgs)
   (if (args-prefix-eq (args-len $params) $scrutArgs $params)
     (nf-indg-body $sig $name $params $motive $cases $indices $scrut $CT0
       (drop-n (args-len $params) $scrutArgs)
       (case-body-of $cases $ctor))
     (indg-stuck $name $params $motive $cases $indices $scrut)))

(= (nf-indg-body $sig $name $params $motive $cases $indices $scrut $CT0 $args $body)
   (unify $body (Bad $e)
     (indg-stuck $name $params $motive $cases $indices $scrut)
     (nf-indg-redex $sig $name $params $motive $cases $indices $scrut
       (branch-apply-g $sig $name $params $motive $cases $body (inst-tel-args $CT0 $params) $args))))

(= (nf-indg-redex $sig $name $params $motive $cases $indices $scrut $redex)
   (unify $redex (Bad $e)
     (indg-stuck $name $params $motive $cases $indices $scrut)
     (nf $sig $redex)))

(= (branch-apply-g $sig $name $params $motive $cases $body $T $args)
   (unify $args ArgsNil
     (if (== (app-head $T) $name) $body (Bad indg-arity-mismatch))
     (unify $args (ArgsCons $arg $rest)
       (unify $T (Pi $A $B)
         (branch-apply-g-arg $sig $name $params $motive $cases $body $A $B $arg $rest)
         (Bad indg-bad-ctor-shape))
       (Bad indg-bad-ctor-shape))))
(= (branch-apply-g-arg $sig $name $params $motive $cases $body $A $B $arg $rest)
   (if (== (app-head $A) $name)
     (let $idxs (drop-n (args-len $params) (app-args-list $A))
       (branch-apply-g $sig $name $params $motive $cases
         (App (App $body $arg) (IndG $name $params $motive $cases $idxs $arg))
         (subst 0 $arg $B)
         $rest))
     (branch-apply-g $sig $name $params $motive $cases
       (App $body $arg)
       (subst 0 $arg $B)
       $rest)))

; ---------- checked proof objects + provenance over typed terms ---------------
(= (args-axioms $sig ArgsNil) ANil)
(= (args-axioms $sig (ArgsCons $a $r)) (ax-union (term-axioms $sig $a) (args-axioms $sig $r)))
(= (cases-axioms $sig CasesNil) ANil)
(= (cases-axioms $sig (Cases (Case $c $body) $rest))
   (ax-union (term-axioms $sig $body) (cases-axioms $sig $rest)))
(= (term-axioms $sig (Var $k)) ANil)
(= (term-axioms $sig (Srt $s)) ANil)
(= (term-axioms $sig (Con $c)) (if (is-axiom-name $sig $c) (ACons $c ANil) ANil))
(= (term-axioms $sig (Def $c)) ANil)
(= (term-axioms $sig (Pi $A $B)) (ax-union (term-axioms $sig $A) (term-axioms $sig $B)))
(= (term-axioms $sig (Lam $A $b)) (ax-union (term-axioms $sig $A) (term-axioms $sig $b)))
(= (term-axioms $sig (App $f $a)) (ax-union (term-axioms $sig $f) (term-axioms $sig $a)))
(= (term-axioms $sig (IndG $name $params $motive $cases $indices $scrut))
   (ax-union (args-axioms $sig $params)
     (ax-union (term-axioms $sig $motive)
       (ax-union (cases-axioms $sig $cases)
         (ax-union (args-axioms $sig $indices) (term-axioms $sig $scrut))))))
(= (term-axioms $sig (Bad $e)) ANil)

(= (kernel-check-checked $sig $term $type True)
   (Ok (CheckedPrf (term-axioms $sig $term) $term $type)))
(= (kernel-check-checked $sig $term $type False) (Err check-failed))
(= (kernel-check $sig $term $type)
   (let $admitted (sig-admitted-with-elims $sig)
     (if $admitted
       (let $ok (check $sig CtxNil $term $type)
         (kernel-check-checked $sig $term $type $ok))
       (Err signature-not-admitted))))

; =============================================================================
; PHASE 4 SEED: typed IndG checking (trust boundary).
; The active infer-indg above checks an IndG term by applying the Phase-2
; generated eliminator type.  These replay terms use well-typed motives/cases,
; then both check and compute through the same generic IndG path.
; =============================================================================

(= (nat-motive-nat) (Lam (Con nat) (Con nat)))
(= (nat-id-cases-typed)
   (Cases (Case z (Con z))
     (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil)))
(= (nat-id-cases-typed-swapped)
   (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0)))))
     (Cases (Case z (Con z)) CasesNil)))
(= (nat-id-indg-typed)
   (IndG nat ArgsNil (nat-motive-nat) (nat-id-cases-typed)
     ArgsNil (App (Con s) (Con z))))
(= (nat-id-indg-typed-swapped)
   (IndG nat ArgsNil (nat-motive-nat) (nat-id-cases-typed-swapped)
     ArgsNil (App (Con s) (Con z))))

(= (list-motive-nat) (Lam (App (Con lst) (Con nat)) (Con nat)))
(= (list-length-cases-typed)
   (Cases (Case lnil (Con z))
     (Cases (Case lcons
       (Lam (Con nat)
         (Lam (App (Con lst) (Con nat))
           (Lam (Con nat) (App (Con s) (Var 0)))))) CasesNil)))
(= (list-one-term)
   (App (App (App (Con lcons) (Con nat)) (Con z)) (App (Con lnil) (Con nat))))
(= (list-length-indg-typed)
   (IndG lst (ArgsCons (Con nat) ArgsNil) (list-motive-nat) (list-length-cases-typed)
     ArgsNil (list-one-term)))

(= (pair-motive-nat) (Lam (App (App (Con pair) (Con nat)) (Con nat)) (Con nat)))
(= (pair-fst-cases-typed)
   (Cases (Case mkpair (Lam (Con nat) (Lam (Con nat) (Var 1)))) CasesNil))
(= (pair-value)
   (App (App (App (App (Con mkpair) (Con nat)) (Con nat)) (Con z)) (App (Con s) (Con z))))
(= (pair-fst-indg-typed)
   (IndG pair (ArgsCons (Con nat) (ArgsCons (Con nat) ArgsNil)) (pair-motive-nat)
     (pair-fst-cases-typed) ArgsNil (pair-value)))

(= (vec-motive-nat)
   (Lam (Con nat)
     (Lam (App (App (Con vec) (Con nat)) (Var 0)) (Con nat))))
(= (vec-length-cases-typed)
   (Cases (Case vnil (Con z))
     (Cases (Case vcons
       (Lam (Con nat)
         (Lam (Con nat)
           (Lam (App (App (Con vec) (Con nat)) (Var 1))
             (Lam (Con nat) (App (Con s) (Var 0))))))) CasesNil)))
(= (vec-one-term)
   (App (App (App (App (Con vcons) (Con nat)) (Con z)) (Con z)) (App (Con vnil) (Con nat))))
(= (vec-length-indg-typed)
   (IndG vec (ArgsCons (Con nat) ArgsNil) (vec-motive-nat) (vec-length-cases-typed)
     (ArgsCons (App (Con s) (Con z)) ArgsNil) (vec-one-term)))

(= (fin-motive-nat)
   (Lam (Con nat) (Lam (App (Con fin) (Var 0)) (Con nat))))
(= (fin-rank-cases-typed)
   (Cases (Case fz (Lam (Con nat) (Con z)))
     (Cases (Case fs
       (Lam (Con nat)
         (Lam (App (Con fin) (Var 0))
           (Lam (Con nat) (App (Con s) (Var 0)))))) CasesNil)))
(= (fin-one-term)
   (App (App (Con fs) (App (Con s) (Con z))) (App (Con fz) (Con z))))
(= (fin-rank-indg-typed)
   (IndG fin ArgsNil (fin-motive-nat) (fin-rank-cases-typed)
     (ArgsCons (App (Con s) (App (Con s) (Con z))) ArgsNil) (fin-one-term)))

(= (id-motive-nat)
   (Lam (Con nat)
     (Lam (App (App (App (Con Id) (Con nat)) (Con z)) (Var 0)) (Con nat))))
(= (id-j-cases-typed) (Cases (Case refl (Con z)) CasesNil))
(= (id-refl-z) (App (App (Con refl) (Con nat)) (Con z)))
(= (id-j-indg-typed)
   (IndG Id (ArgsCons (Con nat) (ArgsCons (Con z) ArgsNil)) (id-motive-nat)
     (id-j-cases-typed) (ArgsCons (Con z) ArgsNil) (id-refl-z)))

(= (IdNat $a $b) (App (App (App (Con Id) (Con nat)) $a) $b))
(= (RflNat $a) (App (App (Con refl) (Con nat)) $a))

; Successor congruence derived from generated J:
;   Pi a b. Id nat a b -> Id nat (s a) (s b)
; The motive is proof-dependent in the Id eliminator shape, but the target type
; ignores the proof argument.  No GEq/GRfl/GTransp/Transp primitive is used.
(= (cong-s-generated-J-type)
   (Pi (Con nat)
     (Pi (Con nat)
       (Pi (IdNat (Var 1) (Var 0))
         (IdNat (App (Con s) (Var 2)) (App (Con s) (Var 1)))))))
(= (cong-s-generated-J-term)
   (Lam (Con nat)
     (Lam (Con nat)
       (Lam (IdNat (Var 1) (Var 0))
         (IndG Id
           (ArgsCons (Con nat) (ArgsCons (Var 2) ArgsNil))
           (Lam (Con nat)
             (Lam (IdNat (Var 3) (Var 0))
               (IdNat (App (Con s) (Var 4)) (App (Con s) (Var 1)))))
           (Cases (Case refl (RflNat (App (Con s) (Var 2)))) CasesNil)
           (ArgsCons (Var 1) ArgsNil)
           (Var 0))))))

!(assertEqual (check (good-sig-G) CtxNil (nat-id-indg-typed) (Con nat)) True)
!(assertEqual (conv (good-sig-G) (nat-id-indg-typed) (App (Con s) (Con z))) True)
!(assertEqual (check (good-sig-G) CtxNil (nat-id-indg-typed-swapped) (Con nat)) True)
!(assertEqual (conv (good-sig-G) (nat-id-indg-typed-swapped) (App (Con s) (Con z))) True)
!(assertEqual (check (good-sig-G) CtxNil (list-length-indg-typed) (Con nat)) True)
!(assertEqual (conv (good-sig-G) (list-length-indg-typed) (App (Con s) (Con z))) True)
!(assertEqual (check (pair-nat-sig-G) CtxNil (pair-fst-indg-typed) (Con nat)) True)
!(assertEqual (conv (pair-nat-sig-G) (pair-fst-indg-typed) (Con z)) True)
!(assertEqual (check (good-sig-G) CtxNil (vec-length-indg-typed) (Con nat)) True)
!(assertEqual (conv (good-sig-G) (vec-length-indg-typed) (App (Con s) (Con z))) True)
!(assertEqual (check (good-sig-G) CtxNil (fin-rank-indg-typed) (Con nat)) True)
!(assertEqual (conv (good-sig-G) (fin-rank-indg-typed) (App (Con s) (Con z))) True)
!(assertEqual (check (good-sig-G) CtxNil (id-j-indg-typed) (Con nat)) True)
!(assertEqual (conv (good-sig-G) (id-j-indg-typed) (Con z)) True)
!(assertEqual (check (good-sig-G) CtxNil (cong-s-generated-J-term) (cong-s-generated-J-type)) True)
!(assertEqual
   (check (good-sig-G) CtxNil
     (cong-s-generated-J-term)
     (Pi (Con nat)
       (Pi (Con nat)
         (Pi (IdNat (Var 1) (Var 0))
           (IdNat (Var 2) (Var 1))))))
   False)

; typed negatives
!(assertEqual
   (check (good-sig-G) CtxNil
     (IndG nat ArgsNil (Con mtv) (nat-id-cases-typed) ArgsNil (App (Con s) (Con z)))
     (Con nat))
   False)
!(assertEqual
   (check (good-sig-G) CtxNil
     (IndG nat ArgsNil (nat-motive-nat) (Cases (Case z (Con z)) CasesNil)
       ArgsNil (App (Con s) (Con z)))
     (Con nat))
   False)
!(assertEqual
   (check (good-sig-G) CtxNil
     (IndG nat ArgsNil (nat-motive-nat)
       (Cases (Case z (Con nat))
         (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
       ArgsNil (App (Con s) (Con z)))
     (Con nat))
   False)
!(assertEqual
   (check (good-sig-G) CtxNil
     (IndG nat ArgsNil (nat-motive-nat) (nat-id-cases-typed) ArgsNil (Con nat))
     (Con nat))
   False)
!(assertEqual
   (check (good-sig-G) CtxNil
     (IndG vec (ArgsCons (Con nat) ArgsNil) (vec-motive-nat) (vec-length-cases-typed)
       (ArgsCons (Con z) ArgsNil) (vec-one-term))
     (Con nat))
   False)
!(assertEqual
   (check (good-sig-G) CtxNil
     (IndG nat ArgsNil (nat-motive-nat)
       (Cases (Case z (Con z))
         (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0)))))
           (Cases (Case bogus (Con z)) CasesNil)))
       ArgsNil (Con z))
     (Con nat))
   False)

; CheckedPrf/provenance: pure generated IndG is axiom-free; axiom use in a case
; is reflected in provenance.
!(assertEqual
   (kernel-check (good-sig-G) (id-j-indg-typed) (Con nat))
   (Ok (CheckedPrf ANil (id-j-indg-typed) (Con nat))))
!(assertEqual
   (kernel-check (good-sig-G) (cong-s-generated-J-term) (cong-s-generated-J-type))
   (Ok (CheckedPrf ANil (cong-s-generated-J-term) (cong-s-generated-J-type))))

(= (nat-axiom-cases-typed)
   (Cases (Case z (Con axN))
     (Cases (Case s (Lam (Con nat) (Lam (Con nat) (Var 0)))) CasesNil)))
(= (nat-axiom-indg-typed)
   (IndG nat ArgsNil (nat-motive-nat) (nat-axiom-cases-typed) ArgsNil (Con z)))
!(assertEqual
   (kernel-check (axiom-nat-sig-G) (nat-axiom-indg-typed) (Con nat))
   (Ok (CheckedPrf (ACons axN ANil) (nat-axiom-indg-typed) (Con nat))))

; =============================================================================
; RETIREMENT GATE (item 4): re-derive the equality theorems that the old slices
; carried via GEq/GRfl/GTransp/Transp — now through CHECKED generated J (IndG on
; Id) + the generated Nat recursor + generated-J cong-s, with NO equality
; primitive.  cong-s is above; here: a checked recursive definition `plus` over
; the generated IndG nat recursor, and `forall n. plus n z = n` by generated
; induction.  Placed after the typed-IndG machinery so the DDef body is inferred
; with infer-indg in scope (phase order).
; =============================================================================
(= (snoc-decl SNil $d) (SCons $d SNil))
(= (snoc-decl (SCons $h $t) $d) (SCons $h (snoc-decl $t $d)))

; plus : nat -> nat -> nat, recursion on the first arg via generated IndG nat
(= (plus-body)
   (Lam (Con nat) (Lam (Con nat)
     (IndG nat ArgsNil (Lam (Con nat) (Con nat))
       (Cases (Case z (Var 0))
         (Cases (Case s (Lam (Con nat) (Lam (Con nat) (App (Con s) (Var 0))))) CasesNil))
       ArgsNil (Var 1)))))
(= (plus-sig-G) (snoc-decl (good-sig-G) (DDef plus (Pi (Con nat) (Pi (Con nat) (Con nat))) (plus-body))))

; (1) plus admits as a CHECKED DDef over the generated recursor, and computes
!(assertEqual (sig-admitted (plus-sig-G)) True)
!(assertEqual (conv (plus-sig-G) (App (App (Def plus) (App (Con s) (Con z))) (Con z)) (App (Con s) (Con z))) True)
!(assertEqual (conv (plus-sig-G) (App (App (Def plus) (Con z)) (App (Con s) (Con z))) (App (Con s) (Con z))) True)
!(assertEqual (conv (plus-sig-G) (App (App (Def plus) (App (Con s) (Con z))) (App (Con s) (Con z))) (App (Con s) (App (Con s) (Con z)))) True)

; (2) forall n. plus n z = n  — generated Nat induction; base refl; step cong-s(IH)
(= (plus-O-r-type) (Pi (Con nat) (IdNat (App (App (Def plus) (Var 0)) (Con z)) (Var 0))))
(= (plus-O-r-term)
   (Lam (Con nat)
     (IndG nat ArgsNil
       (Lam (Con nat) (IdNat (App (App (Def plus) (Var 0)) (Con z)) (Var 0)))
       (Cases (Case z (RflNat (Con z)))
         (Cases (Case s
           (Lam (Con nat)
             (Lam (IdNat (App (App (Def plus) (Var 0)) (Con z)) (Var 0))
               (App (App (App (cong-s-generated-J-term)
                         (App (App (Def plus) (Var 1)) (Con z)))
                    (Var 1))
                 (Var 0))))) CasesNil))
       ArgsNil (Var 0))))
!(assertEqual (check (plus-sig-G) CtxNil (plus-O-r-term) (plus-O-r-type)) True)
; negative: the proof does NOT check at the off-by-one claim plus n z = s n
!(assertEqual (check (plus-sig-G) CtxNil (plus-O-r-term)
   (Pi (Con nat) (IdNat (App (App (Def plus) (Var 0)) (Con z)) (App (Con s) (Var 0))))) False)
; With J diagonal, cong-s, and plus-O-r all derived via generated J, the old
; GEq/GRfl/GTransp/Transp and Id/J slices are retired to `retired_fixtures/`.

; --- calculus character (v2 oracle): our core is ETA-FREE and PREDICATIVE ---
; (pinned verdicts; cf. Lean which has function/structure eta by defeq + impredicative Prop)
!(assertEqual (conv (good-sig-G) (Lam (Con nat) (App (Con s) (Var 0))) (Con s)) False)   ; eta-free: (lambda x. s x) is NOT defeq s
!(assertEqual (infer (good-sig-G) CtxNil (Pi (Srt type) (Var 0))) (Srt kind))            ; predicative: (Pi X:Type. X) : kind, not Type

; --- SR WEDGE (v2 oracle): the generated iota PRESERVES inferred type (subject reduction, first step) ---
; The iota is constructor-headed + non-overlapping by construction (off-constructor scrutinees stay stuck,
; tested above), so here we seal the observable SR property on each family's redex: infer t ≡ infer (nf t).
; This is the admission-level SR step; full universal SR/confluence is the Lean v3 metatheorem.
; helper-factored (let-bind intermediates — deep inline infer(nf t) is CeTTa-eval-fragile)
(= (sr-ok $sig $t)
   (let $nft (nf $sig $t)
     (let $a (infer $sig CtxNil $t)
       (let $b (infer $sig CtxNil $nft)
         (conv $sig $a $b)))))
!(assertEqual (sr-ok (good-sig-G) (nat-id-indg-typed)) True)
!(assertEqual (sr-ok (good-sig-G) (list-length-indg-typed)) True)
!(assertEqual (sr-ok (good-sig-G) (vec-length-indg-typed)) True)
!(assertEqual (sr-ok (good-sig-G) (fin-rank-indg-typed)) True)
!(assertEqual (sr-ok (good-sig-G) (id-j-indg-typed)) True)
!(assertEqual (sr-ok (pair-nat-sig-G) (pair-fst-indg-typed)) True)

; =============================================================================
; v4 SLICE-COLLAPSE REPLAY: re-derive the remaining inductive slices' EXACT
; claims through the SAME DIndG engine, BEFORE those slices retire to
; retired_fixtures/.  Replay-before-retire: nothing moves until DIndG rederives
; what it claimed.  These exercise shapes good-sig-G/pair-sig-G did not already:
;   * Bool (ibool)       — ind_v0/ind_v1: two NULLARY constructors, a bnot
;                          recursor, and the involution bnot (bnot b) = b proved
;                          via GENERATED J (Id ibool) — NO GEq/GRfl primitive.
;   * Tree-leaf          — ind_v1: leaf : nat -> tree (non-recursive payload) and
;                          its generated eliminator computes.
;   * Vec ctor indices   — vec_v0: vnil/vcons CONSTRUCTOR-application index
;                          discrimination; wrong index / wrong tail index / wrong
;                          element type all reject.
;   * Indexed positivity — dindpi: a non-strictly-positive INDEXED+parameterized
;                          constructor (family in an argument's Pi-domain) rejects.
;   * Empty inductive    — dindpi `bad-idj-no-rfl` DISSOLVES: an Id with no refl
;                          constructor is simply an EMPTY inductive; DIndG admits
;                          it and generates its vacuous eliminator.  The old slice
;                          REJECTED it only because the hard-coded Id/J schema
;                          required a refl ctor — a schema artifact, not soundness.
;                          Asserted here as a POSITIVE convergence witness.
; =============================================================================

; ---------- Bool (ibool): nullary enum + recursor + involution via generated J --
(= (bnot-body)
   (Lam (Con ibool)
     (IndG ibool ArgsNil (Lam (Con ibool) (Con ibool))
       (Cases (Case tt (Con ff))
         (Cases (Case ff (Con tt)) CasesNil))
       ArgsNil (Var 0))))
(= (bool-sig-G)
   (SCons (DIndG ibool TNil TNil
            (GCtors (GCtor tt TNil ArgsNil)
              (GCtors (GCtor ff TNil ArgsNil) GCNil)))
   (SCons (DIndG Id (TCons (Srt type) (TCons (Var 0) TNil)) (TCons (Var 1) TNil)
            (GCtors (GCtor refl TNil (ArgsCons (Var 0) ArgsNil)) GCNil))
   (SCons (DDef bnot (Pi (Con ibool) (Con ibool)) (bnot-body))
          SNil))))
(= (IdBool $a $b) (App (App (App (Con Id) (Con ibool)) $a) $b))
(= (RflBool $a) (App (App (Con refl) (Con ibool)) $a))
(= (bnot-invol-type)
   (Pi (Con ibool) (IdBool (App (Def bnot) (App (Def bnot) (Var 0))) (Var 0))))
(= (bnot-invol-term)
   (Lam (Con ibool)
     (IndG ibool ArgsNil
       (Lam (Con ibool) (IdBool (App (Def bnot) (App (Def bnot) (Var 0))) (Var 0)))
       (Cases (Case tt (RflBool (Con tt)))
         (Cases (Case ff (RflBool (Con ff))) CasesNil))
       ArgsNil (Var 0))))

!(assertEqual (decl-type-of (bool-sig-G) ibool) (Srt type))
!(assertEqual (decl-type-of (bool-sig-G) tt) (Con ibool))
!(assertEqual (decl-type-of (bool-sig-G) ff) (Con ibool))
!(assertEqual (sig-admitted (bool-sig-G)) True)
!(assertEqual (conv (bool-sig-G) (App (Def bnot) (Con tt)) (Con ff)) True)
!(assertEqual (conv (bool-sig-G) (App (Def bnot) (Con ff)) (Con tt)) True)
!(assertEqual (check (bool-sig-G) CtxNil (bnot-invol-term) (bnot-invol-type)) True)
; negative: bnot (bnot b) = bnot b is FALSE; the proof must NOT check at it
!(assertEqual (check (bool-sig-G) CtxNil (bnot-invol-term)
   (Pi (Con ibool) (IdBool (App (Def bnot) (App (Def bnot) (Var 0))) (App (Def bnot) (Var 0))))) False)

; ---------- Tree-leaf: non-recursive payload + generated eliminator -----------
(= (tree-sig-G)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG tree TNil TNil
            (GCtors (GCtor leaf (TCons (Con nat) TNil) ArgsNil) GCNil))
          SNil)))
!(assertEqual (decl-type-of (tree-sig-G) leaf) (Pi (Con nat) (Con tree)))
!(assertEqual (sig-admitted (tree-sig-G)) True)
!(assertEqual
   (conv (tree-sig-G)
     (IndG tree ArgsNil (Lam (Con tree) (Con nat))
       (Cases (Case leaf (Lam (Con nat) (Var 0))) CasesNil)
       ArgsNil (App (Con leaf) (App (Con s) (Con z))))
     (App (Con s) (Con z)))
   True)

; ---------- Vec: constructor-application index discrimination -----------------
; vnil : vec A z checks at index z, NOT at s z (the checker must not erase indices)
!(assertEqual (check (good-sig-G) CtxNil (App (Con vnil) (Con nat))
   (App (App (Con vec) (Con nat)) (Con z))) True)
!(assertEqual (check (good-sig-G) CtxNil (App (Con vnil) (Con nat))
   (App (App (Con vec) (Con nat)) (App (Con s) (Con z)))) False)
; vcons nat z z vnil : vec nat (s z) at the EXACT index
!(assertEqual (check (good-sig-G) CtxNil
   (App (App (App (App (Con vcons) (Con nat)) (Con z)) (Con z)) (App (Con vnil) (Con nat)))
   (App (App (Con vec) (Con nat)) (App (Con s) (Con z)))) True)
; wrong tail index: vcons claims length (s z) but tail vnil : vec nat z
!(assertEqual (infer (good-sig-G) CtxNil
   (App (App (App (App (Con vcons) (Con nat)) (App (Con s) (Con z))) (Con z)) (App (Con vnil) (Con nat))))
   (Bad arg-type-mismatch))
; wrong element type: element (Con nat):Type where the parameter type nat is expected
!(assertEqual (infer (good-sig-G) CtxNil
   (App (App (App (Con vcons) (Con nat)) (Con z)) (Con nat)))
   (Bad arg-type-mismatch))

; ---------- Indexed+parameterized positivity negative -------------------------
; mkBad : Pi A. ((badvec A z) -> A) -> badvec A z  — family in an arg's Pi-domain
(= (bad-indexed-pos-sig-G)
   (SCons (DIndG nat TNil TNil
            (GCtors (GCtor z TNil ArgsNil)
              (GCtors (GCtor s (TCons (Con nat) TNil) ArgsNil) GCNil)))
   (SCons (DIndG badvec (TCons (Srt type) TNil) (TCons (Con nat) TNil)
            (GCtors (GCtor mkBad
              (TCons (Pi (App (App (Con badvec) (Var 0)) (Con z)) (Var 1)) TNil)
              (ArgsCons (Con z) ArgsNil)) GCNil))
          SNil)))
!(assertEqual (sig-admitted (bad-indexed-pos-sig-G)) False)

; ---------- Empty inductive: the dissolved bad-idj-no-rfl ---------------------
; An inductive with NO constructors is admitted and its vacuous eliminator
; (the absurd/Empty recursor) typechecks.  This is exactly why "Id without refl"
; is no longer a rejection: DIndG treats it as an ordinary empty family.
(= (emp-sig-G) (SCons (DIndG emp TNil TNil GCNil) SNil))
!(assertEqual (sig-admitted (emp-sig-G)) True)
!(assertEqual (dindg-elim-typechecks (emp-sig-G) emp) True)
!(assertEqual (sig-admitted-with-elims (emp-sig-G)) True)
