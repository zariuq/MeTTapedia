import Mettapedia.GSLT.LanguageDef.Cost
import Mettapedia.Languages.MeTTa.Prime.CostTwoRhoBoundary

/-!
# The selected rho Cost² displayed boundary

The production Cost surface exports an unconditional proof-relevant Cost₁
domain object for rho.  Earlier Cost² theorems are deliberately parameterized
by a first-layer normalizer configuration and its local representative.  This
module closes that last application boundary: the selected configuration is
definitionally the compact output of rho's exported Cost₁ object, and the
representative required by the Cost² obstruction is a theorem.

Consequently the second application of Cost has an unconditional displayed
carrier and an unconditional nonfactorization boundary.  Compact syntax
remains an admitted hot key for fibre-invariant policies, but cannot serve as
an exact receipt; retained elaboration provenance admits the stronger request.
No selected compact Cost² executor is constructed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoSelectedDisplayedBoundary

noncomputable section

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport
open Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The closed first-layer input -/

/-- The exact law bundle used by the unconditional rho Cost₁ object. -/
noncomputable def rhoSelectedCostOneLaws :
    CIGSLT.CostOneObjectLawsFor rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCostOneDomainObject.compactLaws

/-- The selected first-layer normalizer, viewed through the configuration
interface consumed by the Cost² obstruction. -/
noncomputable def rhoSelectedCostOneConfiguration :
    RhoCostOneConfiguration :=
  RhoCostOneConfiguration.hereditarySupported rhoSelectedCostOneLaws

/-- This is not a second first-layer choice: its generated source is exactly
the compact output of the unconditional production Cost₁ object. -/
@[simp] theorem rhoSelectedCostOneConfiguration_source :
    rhoSelectedCostOneConfiguration.source =
      rhoHereditaryCostOneDomainObject.compactOutput.toCIGSLT :=
  rfl

/-- The selected executor satisfies the concrete empty-parallel premise used
to expose the nontrivial second-layer elaboration fibre. -/
theorem rhoSelectedCostOneRepresentative :
    RhoEmptyParallelSourceRepresentative rhoSelectedCostOneConfiguration :=
  hereditarySupported_emptyParallelSourceRepresentative rhoSelectedCostOneLaws

/-! ## Unconditional displayed Cost² -/

/-- The proof-relevant state space obtained by applying Cost elaboration to
the selected first Cost output. -/
abbrev RhoSelectedCostTwoState :=
  CostElaborationFiber rhoSelectedCostOneConfiguration.source

/-- Its compact implementation key forgets only the selected elaboration
tree, retaining the complete dependent compact term and its indices. -/
abbrev rhoSelectedCostTwoCompactKey :
    RhoSelectedCostTwoState →
      CompactCostCarrier rhoSelectedCostOneConfiguration.source :=
  compactCarrierKey rhoSelectedCostOneConfiguration.source

/-- The selected second layer really has a nontrivial proof-relevant fibre;
this is the positive displayed-state witness behind the nonfaithfulness
negative. -/
theorem rhoSelectedCostTwo_has_nontrivial_fibre :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort
        rhoSelectedCostOneConfiguration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        rhoSelectedCostOneConfiguration.source.costWholeReflectionProfile
        rhoSelectedCostOneConfiguration.source.costWholeLanguage
        targetFree targetBound targetSort)
      (left right : CostOpenElaboration
        rhoSelectedCostOneConfiguration.source term),
      left ≠ right := by
  have notAll := rhoCostOneFor_not_all_elaborationFibersSubsingleton
    rhoSelectedCostOneConfiguration rhoSelectedCostOneRepresentative
  simp only [CIGSLT.CostElaborationFibersSubsingleton, not_forall] at notAll
  obtain ⟨targetFree, targetBound, targetSort, term, notSubsingleton⟩ := notAll
  by_contra noPair
  push Not at noPair
  exact notSubsingleton
    ⟨noPair targetFree targetBound targetSort term⟩

/-- The complete laws-free Cost² boundary now applies to rho's actual selected
Cost₁ object with no remaining configuration or representative premise. -/
theorem rhoSelectedCostTwo_boundary_package :
    ¬ rhoSelectedCostOneConfiguration.source.CostNormalizationFactorsThroughCompactErasure ∧
      ¬ rhoSelectedCostOneConfiguration.source.CostCompactErasureFaithful ∧
      ¬ rhoSelectedCostOneConfiguration.source.CostElaborationFibersSubsingleton ∧
      (∃ (targetFree : WellSorted.FreeTypeContext)
        (targetBound : List TypeExpr)
        (targetSort : LangSort
          rhoSelectedCostOneConfiguration.source.costWholeLanguage)
        (term : ReflectiveWellSorted.OpenTerm
          rhoSelectedCostOneConfiguration.source.costWholeReflectionProfile
          rhoSelectedCostOneConfiguration.source.costWholeLanguage
          targetFree targetBound targetSort)
        (policy : CostOpenElaboration
          rhoSelectedCostOneConfiguration.source term → Bool),
        ¬ ∃ value : Bool, ∀ elaboration, policy elaboration = value) :=
  rhoCostTwo_boundary_package rhoSelectedCostOneConfiguration
    rhoSelectedCostOneRepresentative

/-! ## Unconditional implementation and NIK consequences -/

/-- The complete compact value is a runnable hot policy at any revision, but
it is not an exact receipt; the retained displayed state admits exact replay. -/
theorem rhoSelectedCostTwo_global_key_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostOneConfiguration.source) False)
          (compactCarrierKey rhoSelectedCostOneConfiguration.source)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostOneConfiguration.source) True)
          (compactCarrierKey rhoSelectedCostOneConfiguration.source)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostOneConfiguration.source) True)
          (id : RhoSelectedCostTwoState → RhoSelectedCostTwoState)) :=
  rhoCostTwo_compact_hot_key_but_not_exact_receipt dependencies revision
    rhoSelectedCostOneConfiguration rhoSelectedCostOneRepresentative

/-- The stronger per-fibre boundary is also unconditional: a concrete policy
distinguishes two compactly equal elaborations, so compact admission is refused
for both that policy and exact replay while the provenance key admits both. -/
theorem rhoSelectedCostTwo_nik_policy_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort
        rhoSelectedCostOneConfiguration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        rhoSelectedCostOneConfiguration.source.costWholeReflectionProfile
        rhoSelectedCostOneConfiguration.source.costWholeLanguage
        targetFree targetBound targetSort)
      (policy : CostOpenElaboration
        rhoSelectedCostOneConfiguration.source term → Bool),
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
            (source := rhoSelectedCostOneConfiguration.source)
            (term := term))) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy True)
          (provenanceKey
            (source := rhoSelectedCostOneConfiguration.source)
            (term := term))) :=
  rhoCostTwo_nik_policy_key_boundary dependencies revision
    rhoSelectedCostOneConfiguration rhoSelectedCostOneRepresentative

/-- The global policy/replay separation is stable under the displayed Cost₁
transport theory and needs no selected second-layer normalizer. -/
theorem rhoSelectedCostTwo_displayed_compact_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostOneConfiguration.source) False)
          (compactCarrierKey rhoSelectedCostOneConfiguration.source)) ∧
      ¬ ExactReplayKey
        (compactCarrierKey rhoSelectedCostOneConfiguration.source) :=
  rho_compact_policy_admission_without_exact_replay dependencies revision
    rhoSelectedCostOneConfiguration rhoSelectedCostOneRepresentative

#print axioms rhoSelectedCostOneConfiguration_source
#print axioms rhoSelectedCostOneRepresentative
#print axioms rhoSelectedCostTwo_has_nontrivial_fibre
#print axioms rhoSelectedCostTwo_boundary_package
#print axioms rhoSelectedCostTwo_global_key_boundary
#print axioms rhoSelectedCostTwo_nik_policy_boundary
#print axioms rhoSelectedCostTwo_displayed_compact_boundary

end

end Mettapedia.Languages.MeTTa.Prime.CostTwoSelectedDisplayedBoundary
