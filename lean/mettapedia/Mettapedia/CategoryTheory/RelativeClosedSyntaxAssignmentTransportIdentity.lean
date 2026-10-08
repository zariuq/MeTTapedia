import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransport

/-!
# Identity coherence of weak assignment transport

The identity functor retains the independently supplied base, objects and
complete primitive arrows. The actual parser calibration proves that its
constructor normalization recovers the supplied assignment. The resulting
comparison is the identity on the entire interpreted category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransport

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D) (realization : Realization signature meanings)

private instance identity_closed : MonoidalClosedFunctor (𝟭 D) where
  comparison_iso argument := by
    suffices ∀ result : D, IsIso ((expComparison (𝟭 D) argument).natTrans.app result) from
      NatIso.isIso_of_isIso_app _
    intro result
    rw [CartesianClosedFunctorCoherence.exponential_identity]
    exact IsIso.id (C := D) ((ihom argument).obj result)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem primitiveData_identity : primitiveData meanings (𝟭 D) = meanings := rfl

theorem selected_identity : selected meanings realization (𝟭 D) =
    Interpretation.functor meanings realization :=
  CanonicalExtension.atomic_functor meanings realization

variable (headers : HeaderFormation signature)

theorem assignment_identity : assignment meanings realization (𝟭 D) headers = meanings :=
  (CanonicalExtension.assignment_congr (selected_identity meanings realization) headers).trans
    (InterpretationNormalization.normalized_assignment meanings realization headers)

private theorem interpretation_equal {before after : Assignment C symbols D}
    (first : Realization signature before) (second : Realization signature after)
    (same : before = after) : Interpretation.functor before first =
      Interpretation.functor after second := by
  cases same
  rfl

theorem interpretation_identity : interpretation meanings realization (𝟭 D) headers =
    Interpretation.functor meanings realization :=
  interpretation_equal (locally_realized meanings realization (𝟭 D) headers) realization
    (assignment_identity meanings realization headers)

def identityComparison : Interpretation.functor meanings realization ≅
    Interpretation.functor meanings realization :=
  comparison meanings realization (𝟭 D) headers ≪≫
    eqToIso (interpretation_identity meanings realization headers)

theorem identityComparison_base (object : C) :
    (identityComparison meanings realization headers).hom.app (baseObject signature object) =
      𝟙 ((Interpretation.functor meanings realization).obj (baseObject signature object)) := by
  change ((eqToHom (functor_base meanings realization)).app object ≫
    (parserComparison (selected meanings realization (𝟭 D)) headers).hom.app
        (baseObject signature object)) ≫
      (eqToHom (interpretation_identity meanings realization headers)).app
        (baseObject signature object) = _
  rw [Category.assoc, parserComparison_hom_base, eqToHom_app, eqToHom_app, eqToHom_trans,
    eqToHom_trans, eqToHom_refl]
  rfl

theorem identityComparison_name (origin : symbols.ObjectName) :
    (identityComparison meanings realization headers).hom.app (namedObject origin) =
      𝟙 ((Interpretation.functor meanings realization).obj (namedObject origin)) := by
  change (eqToHom (CoherentExtension.target_named_object meanings realization origin) ≫
    (parserComparison (selected meanings realization (𝟭 D)) headers).hom.app (namedObject origin)) ≫
      (eqToHom (interpretation_identity meanings realization headers)).app (namedObject origin) = _
  rw [Category.assoc, parserComparison_hom_name, eqToHom_app, eqToHom_trans, eqToHom_trans, eqToHom_refl]

theorem identityComparison_eq_refl : identityComparison meanings realization headers =
    Iso.refl (Interpretation.functor meanings realization) := by
  apply Iso.ext
  exact FunctorCellUniqueness.cells_equal_of_generators (Iso.refl _) _
    (identityComparison_base meanings realization headers) (identityComparison_name meanings realization headers)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransport
