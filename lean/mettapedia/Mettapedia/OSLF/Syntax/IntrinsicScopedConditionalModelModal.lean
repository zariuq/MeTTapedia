import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelHistory
import Mettapedia.OSLF.Syntax.ModelPresheafExtraEventControl
import Mettapedia.OSLF.Syntax.EventGraphModalTransport

/-!
# OSLF may-observations of contextual operational models

A substitution-operational model supplies both retained evidence and its
endpoint-image observation. Its ordinary model morphisms preserve generated
may-observations in the forward direction. An authored no-rule monoid model
with extra target firings shows that a converse would be false.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelModal

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.EventGraphImageMorphism
open Mettapedia.OSLF.Binding.EventGraphModalTransport
open Mettapedia.OSLF.Binding.EquationExtensionEventGraph
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- A model's variable-vertex graph exposes its actual individual evidence
to the common operational observation interface. -/
noncomputable def modelEventGraph
    {A : BindingCloneAlgebra.Algebra.{0} S}
    (Y : SubstitutionModel R A) : EventGraph (Base A) :=
  variableGraph (modelGraph R Y)

/-- Every lawful model map induces an event-graph map with identity state
translation and its specified map of individual evidence. -/
def modelEventGraphMap
    {A : BindingCloneAlgebra.Algebra.{0} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    EventGraphHom (modelEventGraph R Y) (modelEventGraph R Z) where
  vertexMap := 𝟙 (states A)
  edgeMap := mapModelEvents R h
  source_comm := by
    ext X event
    rfl
  target_comm := by
    ext X event
    rfl

/-- The GSLT/OSLF step relation observed at a context is exactly the
endpoint-image predicate of the model's retained event graph. -/
theorem modelStep_iff_evidence
    {A : BindingCloneAlgebra.Algebra.{0} S}
    (Y : SubstitutionModel R A) (X : Base A)
    (sort : S.Srt)
    (first last : A.substitution.Carrier X.unop.context sort) :
    (theoryAt (modelEventGraph R Y) X).Step
      ⟨sort, first⟩ ⟨sort, last⟩ ↔
      Nonempty (Y.evidence.carrier ()
        (⟨X.unop.context, sort, (first, last)⟩ :
          AuthoredPositionedRulePolynomial.Judgment A)) :=
  mem_modelReduction_iff R Y X sort first last

/-- Ordinary model maps preserve the generated may modality. The theorem
does not require target-step coverage or injectivity on source programs. -/
theorem modelDiamond_map
    {A : BindingCloneAlgebra.Algebra.{0} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (X : Base A) (predicate : (states A).obj X → Prop)
    (source : (states A).obj X)
    (may : gsltDiamond (theoryAt (modelEventGraph R Y) X)
      predicate source) :
    gsltDiamond (theoryAt (modelEventGraph R Z) X)
      predicate source := by
  exact diamond_map (modelEventGraphMap R h) X predicate source may

namespace MonoidControl

open Mettapedia.OSLF.Binding.MonoidEquationRung
open Mettapedia.OSLF.Binding.ModelPresheafExtraEventControl

private noncomputable abbrev A : BindingCloneAlgebra.Algebra sig :=
  (FreeBindingEquationModel.presented monoidE).algebra

private abbrev noRules : List (Rule sig metas) := []

/-- At the authored monoid unit, adding lawful target evidence creates a
may-success which the unique free-model interpretation cannot reflect. -/
theorem added_event_not_reflected_by_diamond :
    ∃ X : Base A,
      ∃ first last : A.substitution.Carrier X.unop.context .element,
        gsltDiamond
          (theoryAt (modelEventGraph noRules fullModel) X)
          (fun candidate => candidate = ⟨.element, last⟩)
          ⟨.element, first⟩ ∧
        ¬ gsltDiamond
          (theoryAt (modelEventGraph noRules
            (SubstitutionModel.free noRules A)) X)
          (fun candidate => candidate = ⟨.element, last⟩)
          ⟨.element, first⟩ := by
  obtain ⟨X, first, last, targetStep, noSourceStep⟩ :=
    unit_reduction_not_reflected
  refine ⟨X, first, last, ?_, ?_⟩
  · apply (gsltDiamond_singleton_iff_step
      (theoryAt (modelEventGraph noRules fullModel) X)
      ⟨.element, first⟩ ⟨.element, last⟩).2
    exact targetStep
  · intro may
    apply noSourceStep
    exact (gsltDiamond_singleton_iff_step
      (theoryAt (modelEventGraph noRules
        (SubstitutionModel.free noRules A)) X)
      ⟨.element, first⟩ ⟨.element, last⟩).1 may

end MonoidControl

#print axioms modelEventGraphMap
#print axioms modelStep_iff_evidence
#print axioms modelDiamond_map
#print axioms MonoidControl.added_event_not_reflected_by_diamond

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelModal
