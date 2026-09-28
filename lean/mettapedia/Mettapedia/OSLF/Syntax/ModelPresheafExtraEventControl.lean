import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelPresheaf
import Mettapedia.OSLF.Syntax.MonoidEquationRung

/-!
# A lawful interpretation with additional target firings

The monoid presentation has three equations and no operational rules. Its
free operational model therefore has no firing evidence. A target model can
nevertheless supply additional evidence at every well-sorted pair of terms.
The unique interpretation from the free model preserves every source event,
but cannot cover the target's new events or reflect its reduction predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ModelPresheafExtraEventControl

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.MonoidEquationRung
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial

private noncomputable abbrev A : BindingCloneAlgebra.Algebra sig :=
  (FreeBindingEquationModel.presented monoidE).algebra

private abbrev R : List (Rule sig metas) := []

/-- A genuine target operational model with one extra piece of evidence at
every pair of well-sorted monoid terms. It interprets no rule constructors,
because the authored presentation has none. -/
noncomputable def fullModel : SubstitutionModel R A where
  evidence := {
    carrier := fun _ _ => PUnit
    rules := {
      act := by
        intro base judgment layer
        exact Fin.elim0 layer.1.1.index
    }
  }
  act := by
    intro judgment evidence Δ σ target eq
    exact PUnit.unit
  act_rules := by
    intro judgment shape children Δ σ target eq
    exact Fin.elim0 shape.1.index
  act_identity := by
    intro judgment evidence eq
    rfl
  act_comp := by
    intro judgment evidence Δ Θ σ τ target second direct
    rfl

/-- The unique free-model interpretation into a model with additional
target behavior is still an ordinary lawful model morphism. -/
noncomputable def freeToFull : SubstitutionModel.Hom R
    (SubstitutionModel.free R A) fullModel :=
  SubstitutionModel.foldHom R fullModel

/-- The free monoid presentation cannot fire at any judgment, including
the authored unit program. -/
theorem free_has_no_events (j : AuthoredPositionedRulePolynomial.Judgment A) :
    ¬ Nonempty ((SubstitutionModel.free R A).evidence.carrier () j) := by
  intro event
  exact no_rules_no_reduction (M := metas) A j event

/-- The target interpretation adds a firing at every judgment without
changing the monoid equations or the contextual substitution action. -/
theorem full_has_event (j : AuthoredPositionedRulePolynomial.Judgment A) :
    Nonempty (fullModel.evidence.carrier () j) :=
  ⟨PUnit.unit⟩

/-- At the actual authored monoid unit, the target's reduction observation
is true while the free presentation's is false. -/
theorem unit_reduction_not_reflected :
    ∃ X : Base A,
      ∃ first last : A.substitution.Carrier X.unop.context .element,
        ((⟨.element, first⟩, ⟨.element, last⟩) :
          (states A).obj X × (states A).obj X) ∈
            (modelReduction R fullModel).obj X ∧
        ((⟨.element, first⟩, ⟨.element, last⟩) :
          (states A).obj X × (states A).obj X) ∉
            (modelReduction R (SubstitutionModel.free R A)).obj X := by
  let X : Base A := Opposite.op
    (ContextObject.ofList A.substitution.toClone [])
  let unit : A.substitution.Carrier X.unop.context .element := unitQ
  refine ⟨X, unit, unit, ?_, ?_⟩
  · exact (mem_modelReduction_iff R fullModel X .element unit unit).2
      (full_has_event ⟨X.unop.context, .element, (unit, unit)⟩)
  · intro reflected
    exact free_has_no_events ⟨X.unop.context, .element, (unit, unit)⟩
      ((mem_modelReduction_iff R (SubstitutionModel.free R A)
        X .element unit unit).1 reflected)

/-- This lawful model map preserves the image observation in the forward
direction, even though the target observation has strictly more pairs. -/
theorem freeToFull_preserves_reduction :
    modelReduction R (SubstitutionModel.free R A) ≤
      modelReduction R fullModel :=
  modelReduction_le R freeToFull

#print axioms fullModel
#print axioms freeToFull
#print axioms free_has_no_events
#print axioms unit_reduction_not_reflected
#print axioms freeToFull_preserves_reduction

end Mettapedia.OSLF.Binding.ModelPresheafExtraEventControl
