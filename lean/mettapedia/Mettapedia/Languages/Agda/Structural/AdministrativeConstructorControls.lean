import Mettapedia.Languages.Agda.Structural.AdministrativeConstructorPredicates
import Mettapedia.Languages.Agda.Structural.AdministrativePresheafControls

/-!
# Binding and correlated-argument predicate controls

A lambda predicate distinguishes its new bound variable from an ambient one.
A predicate on append arguments keeps a relation between its two inputs.
Both are stable under actual typed substitution. Structural membership is
tested separately from the existence of a static typing derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.ConstructorControls

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

noncomputable def identityArguments : Subfunctor (arguments (sig.arity Op.lam)) where
  obj _ := {args | args = .cons (.var .zero) .nil}
  map _ _ member := by
    cases member
    rfl

noncomputable def identityLambdas : Subfunctor (terms .term) :=
  constructorPredicate Op.lam identityArguments

theorem identity_member (X : Base) : lam (.var .zero) ∈ identityLambdas.obj X :=
  (constructor_member_iff Op.lam identityArguments X (.cons (.var .zero) .nil)).2 rfl

theorem ambient_variable_excluded :
    lam (.var (.succ .zero)) ∉ identityLambdas.obj Controls.openWorld := by
  intro member
  have same := (constructor_member_iff Op.lam identityArguments Controls.openWorld
    (.cons (.var (.succ .zero)) .nil)).1 member
  cases same

theorem nonbinding_lambda_excluded (X : Base) (body : (terms .term).obj X) :
    lamNoAbs body ∉ identityLambdas.obj X :=
  other_constructor_excluded Op.lam Op.lamNoAbs (by intro same; cases same)
    identityArguments X (.cons body .nil)

theorem substitution_fixes_bound_variable :
    (terms .term).map Controls.replaceWithRedex (lam (.var .zero)) = lam (.var .zero) := rfl

theorem substitution_weakens_ambient_image :
    (terms .term).map Controls.replaceWithRedex (lam (.var (.succ .zero))) =
      lam (weaken AdministrativeStatics.Controls.expanded) := rfl

theorem substitution_does_not_capture_ambient_image :
    (terms .term).map Controls.replaceWithRedex (lam (.var (.succ .zero))) ≠
      lam (.var .zero) := by
  intro same
  cases same

theorem identity_is_also_typable :
    Statics.Boundary.identityTerm ∈ typable.obj Controls.closedWorld := by
  apply (typable_iff Controls.closedWorld _).2
  exact ⟨_, ⟨includeCanonical Statics.Boundary.identityTyped⟩⟩

noncomputable def equalAppendArguments : Subfunctor (arguments (sig.arity Op.append)) where
  obj _ := {args | ∃ es, args = .cons es (.cons es .nil)}
  map {X Y} substitution := by
    rintro _ ⟨es, rfl⟩
    exact ⟨bind substitution.unop.val es, rfl⟩

noncomputable def equalAppends : Subfunctor (terms .spine) :=
  constructorPredicate Op.append equalAppendArguments

theorem equal_append_member (X : Base) (es : (terms .spine).obj X) :
    append es es ∈ equalAppends.obj X :=
  (constructor_member_iff Op.append equalAppendArguments X (.cons es (.cons es .nil))).2
    ⟨es, rfl⟩

theorem distinct_arguments_excluded :
    append nil (cons (apply (natLiteral 0)) nil) ∉ equalAppends.obj Controls.closedWorld := by
  intro member
  obtain ⟨es, same⟩ := (constructor_member_iff Op.append equalAppendArguments Controls.closedWorld
    (.cons nil (.cons (cons (apply (natLiteral 0)) nil) .nil))).1 member
  cases same

theorem correlated_arguments_restrict :
    (terms .spine).map Controls.replaceWithRedex
      (append AdministrativeStatics.Controls.variableSpine AdministrativeStatics.Controls.variableSpine) ∈
        equalAppends.obj Controls.closedWorld :=
  constructor_predicate_restrict Op.append equalAppendArguments Controls.replaceWithRedex _
    (equal_append_member Controls.openWorld _)

/-- A structural type-code pattern does not supply an admitted universe profile. -/
theorem unsupported_annotation_has_constructor_shape :
    AdministrativeStatics.Controls.unsupportedType ∈
      (constructorPredicate Op.el (⊤ : Subfunctor (arguments (sig.arity Op.el)))).obj
        Controls.closedWorld :=
  ⟨.cons (prop (levelClosed 1)) (.cons AdministrativeStatics.Controls.contracted .nil),
    trivial, rfl⟩

theorem unsupported_annotation_still_unformed :
    AdministrativeStatics.Controls.unsupportedType ∉ formed.obj Controls.closedWorld :=
  AdministrativeStatics.Controls.unsupported_type_unformed

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.ConstructorControls
