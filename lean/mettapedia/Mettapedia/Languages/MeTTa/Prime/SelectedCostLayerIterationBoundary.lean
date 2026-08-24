import Mettapedia.GSLT.LanguageDef.Cost
import Mettapedia.Languages.MeTTa.Prime.CostLayerIterationBoundary

/-!
# The selected rho cost-layer iteration displayed boundary

The production Cost surface exports an unconditional proof-relevant cost layer
domain object for rho.  Earlier cost-layer iteration theorems are deliberately parameterized
by a first-layer normalizer configuration and its local representative.  This
module closes that last application boundary: the selected configuration is
definitionally the compact output of rho's exported cost layer object, and the
representative required by the cost-layer iteration obstruction is a theorem.

Consequently the second application of Cost has an unconditional displayed
carrier and an unconditional nonfactorization boundary.  Compact syntax
remains an admitted hot key for fibre-invariant policies, but cannot serve as
an exact receipt; retained elaboration provenance admits the stronger request.
No selected compact cost-layer iteration executor is constructed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.SelectedCostLayerIterationBoundary

noncomputable section

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyTransport
open Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyContract
open Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The closed first-layer input -/

/-- The exact law bundle used by the unconditional rho cost layer object. -/
noncomputable def rhoSelectedCompactOpenNormalizerLaws :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCostLayer.compactLaws

/-- The selected first-layer normalizer, viewed through the configuration
interface consumed by the cost-layer iteration obstruction. -/
noncomputable def rhoSelectedCostLayerConfiguration :
    RhoCostLayerConfiguration :=
  RhoCostLayerConfiguration.hereditarySupported rhoSelectedCompactOpenNormalizerLaws

/-- This is not a second first-layer choice: its generated source is exactly
the compact output of the unconditional production cost layer object. -/
@[simp] theorem rhoSelectedCostLayerConfiguration_source :
    rhoSelectedCostLayerConfiguration.source =
      rhoHereditaryCostLayer.compactOutput.toCIGSLT :=
  rfl

/-- The selected executor satisfies the concrete empty-parallel premise used
to expose the nontrivial second-layer elaboration fibre. -/
theorem rhoSelectedCostLayerRepresentative :
    RhoEmptyParallelSourceRepresentative rhoSelectedCostLayerConfiguration :=
  hereditarySupported_emptyParallelSourceRepresentative rhoSelectedCompactOpenNormalizerLaws

/-! ## Unconditional displayed cost-layer iteration -/

/-- The proof-relevant state space obtained by applying Cost elaboration to
the selected first Cost output. -/
abbrev RhoSelectedCostLayerIterationState :=
  CostElaborationFiber rhoSelectedCostLayerConfiguration.source

/-- Its compact implementation key forgets only the selected elaboration
tree, retaining the complete dependent compact term and its indices. -/
abbrev rhoSelectedCostLayerIterationCompactKey :
    RhoSelectedCostLayerIterationState →
      CompactCostCarrier rhoSelectedCostLayerConfiguration.source :=
  compactCarrierKey rhoSelectedCostLayerConfiguration.source

/-- The selected second layer really has a nontrivial proof-relevant fibre;
this is the positive displayed-state witness behind the nonfaithfulness
negative. -/
theorem rhoSelectedCostLayerIteration_has_nontrivial_fibre :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort
        rhoSelectedCostLayerConfiguration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        rhoSelectedCostLayerConfiguration.source.costWholeReflectionProfile
        rhoSelectedCostLayerConfiguration.source.costWholeLanguage
        targetFree targetBound targetSort)
      (left right : CostOpenElaboration
        rhoSelectedCostLayerConfiguration.source term),
      left ≠ right := by
  have notAll := rhoCostLayerFor_not_all_elaborationFibersSubsingleton
    rhoSelectedCostLayerConfiguration rhoSelectedCostLayerRepresentative
  simp only [CIGSLT.CostElaborationFibersSubsingleton, not_forall] at notAll
  obtain ⟨targetFree, targetBound, targetSort, term, notSubsingleton⟩ := notAll
  by_contra noPair
  push Not at noPair
  exact notSubsingleton
    ⟨noPair targetFree targetBound targetSort term⟩

/-- The complete laws-free cost-layer iteration boundary now applies to rho's actual selected
cost layer object with no remaining configuration or representative premise. -/
theorem rhoSelectedCostLayerIteration_boundary_package :
    ¬ rhoSelectedCostLayerConfiguration.source.CostNormalizationFactorsThroughCompactErasure ∧
      ¬ rhoSelectedCostLayerConfiguration.source.CostCompactErasureFaithful ∧
      ¬ rhoSelectedCostLayerConfiguration.source.CostElaborationFibersSubsingleton ∧
      (∃ (targetFree : WellSorted.FreeTypeContext)
        (targetBound : List TypeExpr)
        (targetSort : LangSort
          rhoSelectedCostLayerConfiguration.source.costWholeLanguage)
        (term : ReflectiveWellSorted.OpenTerm
          rhoSelectedCostLayerConfiguration.source.costWholeReflectionProfile
          rhoSelectedCostLayerConfiguration.source.costWholeLanguage
          targetFree targetBound targetSort)
        (policy : CostOpenElaboration
          rhoSelectedCostLayerConfiguration.source term → Bool),
        ¬ ∃ value : Bool, ∀ elaboration, policy elaboration = value) :=
  rhoCostLayerIteration_boundary_package rhoSelectedCostLayerConfiguration
    rhoSelectedCostLayerRepresentative

/-! ## Unconditional implementation and NIK consequences -/

/-- The complete compact value is a runnable hot policy at any revision, but
it is not an exact receipt; the retained displayed state admits exact replay. -/
theorem rhoSelectedCostLayerIteration_global_key_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostLayerConfiguration.source) False)
          (compactCarrierKey rhoSelectedCostLayerConfiguration.source)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostLayerConfiguration.source) True)
          (compactCarrierKey rhoSelectedCostLayerConfiguration.source)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostLayerConfiguration.source) True)
          (id : RhoSelectedCostLayerIterationState → RhoSelectedCostLayerIterationState)) :=
  rhoCostLayerIteration_compact_hot_key_but_not_exact_receipt dependencies revision
    rhoSelectedCostLayerConfiguration rhoSelectedCostLayerRepresentative

/-- The stronger per-fibre boundary is also unconditional: a concrete policy
distinguishes two compactly equal elaborations, so compact admission is refused
for both that policy and exact replay while the provenance key admits both. -/
theorem rhoSelectedCostLayerIteration_nik_policy_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort
        rhoSelectedCostLayerConfiguration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        rhoSelectedCostLayerConfiguration.source.costWholeReflectionProfile
        rhoSelectedCostLayerConfiguration.source.costWholeLanguage
        targetFree targetBound targetSort)
      (policy : CostOpenElaboration
        rhoSelectedCostLayerConfiguration.source term → Bool),
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy False) (compactFibreKey term)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy True) (compactFibreKey term)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy False)
          (provenanceKey
            (source := rhoSelectedCostLayerConfiguration.source)
            (term := term))) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy True)
          (provenanceKey
            (source := rhoSelectedCostLayerConfiguration.source)
            (term := term))) :=
  rhoCostLayerIteration_nik_policy_key_boundary dependencies revision
    rhoSelectedCostLayerConfiguration rhoSelectedCostLayerRepresentative

/-- The global policy/replay separation is stable under the displayed cost layer
transport theory and needs no selected second-layer normalizer. -/
theorem rhoSelectedCostLayerIteration_displayed_compact_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostLayerConfiguration.source) False)
          (compactCarrierKey rhoSelectedCostLayerConfiguration.source)) ∧
      ¬ ReplayKey.IsExact
        (compactCarrierKey rhoSelectedCostLayerConfiguration.source) :=
  rho_compact_policy_admission_without_exact_replay dependencies revision
    rhoSelectedCostLayerConfiguration rhoSelectedCostLayerRepresentative

#print axioms rhoSelectedCostLayerConfiguration_source
#print axioms rhoSelectedCostLayerRepresentative
#print axioms rhoSelectedCostLayerIteration_has_nontrivial_fibre
#print axioms rhoSelectedCostLayerIteration_boundary_package
#print axioms rhoSelectedCostLayerIteration_global_key_boundary
#print axioms rhoSelectedCostLayerIteration_nik_policy_boundary
#print axioms rhoSelectedCostLayerIteration_displayed_compact_boundary

end

end Mettapedia.Languages.MeTTa.Prime.SelectedCostLayerIterationBoundary
