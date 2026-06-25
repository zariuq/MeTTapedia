; =============================================================================
; kernel_binding_decl_v1.metta
;
; Shared BindingDecl interface for hosted LanguageDefs.
;
; This layer sits above the minimal performant waist.  The hot kernel clients
; keep importing kernel_binding_waist_v1 directly; notation/LanguageDef concrete syntax forms
; import this file when they need declared binding shapes such as dependent Pi,
; forall/exists binders, comprehensions, or proof-context binders.
; =============================================================================

!(import! &self kernel_binding_waist_v1)

; ---------- BindingDecl data -------------------------------------------------
; Existing notation files already use Bind0 and (Bind1 field).  BindFields is
; the general field-depth form.  BindPi records the common dependent-function
; shape where the domain is outside scope and the codomain/body is inside.
(= (binding-depth-ok $n)
   (if (== $n 0) True
     (if (> $n 0) (binding-depth-ok (- $n 1)) False)))

(= (binding-field-member $field BNil) False)
(= (binding-field-member $field (BCons (BField $f $d) $rest))
   (if (== $field $f) True (binding-field-member $field $rest)))

(= (binding-fields-admitted BNil) True)
(= (binding-fields-admitted (BCons (BField $field $depth) $rest))
   (if (binding-field-member $field $rest)
     False
     (if (binding-depth-ok $depth) (binding-fields-admitted $rest) False)))

(= (binding-field-depth BNil $field) (Bad undeclared-binding-field))
(= (binding-field-depth (BCons (BField $f $d) $rest) $field)
   (if (== $field $f) $d (binding-field-depth $rest $field)))

(= (binding-decl-admitted Bind0) True)
(= (binding-decl-admitted (Bind1 $field)) True)
(= (binding-decl-admitted (BindFields $fields)) (binding-fields-admitted $fields))
(= (binding-decl-admitted (BindPi $domain $codomain))
   (if (== $domain $codomain) False True))

(= (binding-decl-depth Bind0 $field) (Bad undeclared-binding-field))
(= (binding-decl-depth (Bind1 $body) $field)
   (if (== $field $body) 1 (Bad undeclared-binding-field)))
(= (binding-decl-depth (BindFields $fields) $field)
   (binding-field-depth $fields $field))
(= (binding-decl-depth (BindPi $domain $codomain) $field)
   (if (== $field $domain) 0
     (if (== $field $codomain) 1 (Bad undeclared-binding-field))))

; Hosted LanguageDefs can declare deeper fields without changing the current hot
; kernel traversal clauses.  Active kernel AST traversal uses bindg depth 0/1;
; these helpers are the LanguageDef-facing generalization.
(= (binding-shift-under-depth $d $c $depth $t)
   (if (== $depth 0)
     (bind-shift $d $c $t)
     (if (> $depth 0)
       (binding-shift-under-depth $d (+ $c 1) (- $depth 1) $t)
       (Bad bad-binding-depth))))

(= (binding-subst-under-depth $j $s $depth $t)
   (if (== $depth 0)
     (bind-subst $j $s $t)
     (if (> $depth 0)
       (binding-subst-under-depth
         (+ $j 1)
         (bind-shift 1 0 $s)
         (- $depth 1)
         $t)
       (Bad bad-binding-depth))))

; ---------- representative hosted-logic binders -----------------------------
!(assertEqual (binding-decl-admitted Bind0) True)
!(assertEqual (binding-decl-admitted (Bind1 body)) True)
!(assertEqual (binding-decl-admitted (BindPi domain codomain)) True)
!(assertEqual (binding-decl-admitted (BindPi body body)) False)
!(assertEqual
  (binding-decl-admitted
    (BindFields (BCons (BField lhs 0) (BCons (BField rhs 2) BNil))))
  True)
!(assertEqual
  (binding-decl-admitted
    (BindFields (BCons (BField body 1) (BCons (BField body 0) BNil))))
  False)
!(assertEqual
  (binding-decl-admitted
    (BindFields (BCons (BField body 3) BNil)))
  True)

!(assertEqual (binding-decl-depth Bind0 body) (Bad undeclared-binding-field))
!(assertEqual (binding-decl-depth (Bind1 body) body) 1)
!(assertEqual (binding-decl-depth (Bind1 body) ty) (Bad undeclared-binding-field))
!(assertEqual (binding-decl-depth (BindPi domain codomain) domain) 0)
!(assertEqual (binding-decl-depth (BindPi domain codomain) codomain) 1)
!(assertEqual (binding-decl-depth (BindPi domain codomain) body) (Bad undeclared-binding-field))
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField ty 0) (BCons (BField body 1) BNil)))
    body)
  1)
!(assertEqual (binding-decl-depth (Bind1 forallBody) forallBody) 1)
!(assertEqual (binding-decl-depth (Bind1 existsBody) existsBody) 1)
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField predicate 1) (BCons (BField carrier 0) BNil)))
    predicate)
  1)
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField left 0) (BCons (BField right 2) BNil)))
    right)
  2)

!(assertEqual (binding-shift-under-depth 1 0 0 (Var 0)) (Var 1))
!(assertEqual (binding-shift-under-depth 1 0 1 (Var 0)) (Var 0))
!(assertEqual (binding-shift-under-depth 1 0 2 (Var 1)) (Var 1))
!(assertEqual (binding-shift-under-depth 1 0 3 (Var 2)) (Var 2))
!(assertEqual (binding-shift-under-depth 1 0 3 (Var 3)) (Var 4))
!(assertEqual (binding-subst-under-depth 0 (Con z) 1 (Var 1)) (Con z))
!(assertEqual (binding-subst-under-depth 0 (Con z) 2 (Var 2)) (Con z))
!(assertEqual (binding-subst-under-depth 0 (Var 0) 2 (Var 2)) (Var 2))
!(assertEqual (binding-subst-under-depth 0 (Con z) 3 (Var 3)) (Con z))
!(assertEqual (binding-subst-under-depth 0 (Var 0) 3 (Var 3)) (Var 3))
!(assertEqual (binding-subst-under-depth 0 (Var 1) 4 (Var 4)) (Var 5))
