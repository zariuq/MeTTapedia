import Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyTransport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationPolicyCorollary

/-!
# The reflective-rho instance of the Prime cost-layer iteration boundary

The generic Prime cost-layer iteration interface is independent of any concrete language.
This annex instantiates its cache, information-order, NIK-admission,
implementation-key, and displayed-transport boundaries with the reflective
rho calculus.

The compact term remains an admissible key for fibre-invariant observations,
but the rho cost-layer iteration witness proves that it cannot replay arbitrary retained
elaborations.  The proof-relevant elaboration key remains exact.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.Elaboration

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Rho's cost-layer iteration witness produces a concrete future policy for which compact
syntax is neither a safe cache key nor an exact replay key, while the retained
proof-relevant key supports the same policy exactly.

The two normalization negatives are included so the cache statement cannot
be detached from the actual cost-layer iteration nonfactorization witness. -/
theorem rhoCostLayerIteration_cache_replay_boundary
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostNormalizationFactorsThroughCompactErasure ∧
      ¬ configuration.source.CostCompactErasureFaithful ∧
      ∃ (targetFree : WellSorted.FreeTypeContext)
        (targetBound : List TypeExpr)
        (targetSort : LangSort configuration.source.costWholeLanguage)
        (term : ReflectiveWellSorted.OpenTerm
          configuration.source.costWholeReflectionProfile
          configuration.source.costWholeLanguage targetFree targetBound
          targetSort)
        (policy : CostOpenElaboration configuration.source term → Bool),
        ¬ ReplayKey.Supports (compactFibreKey term) policy ∧
          ¬ ReplayKey.IsExact (compactFibreKey term) ∧
          ReplayKey.IsExact
            (provenanceKey (source := configuration.source) (term := term)) ∧
          ReplayKey.Supports
            (provenanceKey (source := configuration.source) (term := term))
            policy := by
  refine ⟨rhoCostLayerFor_not_normalizationFactorsThroughCompactErasure
      configuration representative,
    rhoCostLayerFor_not_costCompactErasureFaithful configuration representative,
    ?_⟩
  obtain ⟨targetFree, targetBound, targetSort, term, policy, nonconstant⟩ :=
    rhoCostLayerFor_exists_nonconstant_fiber_policy configuration representative
  have compactUnsafe : ¬ ReplayKey.Supports (compactFibreKey term) policy := by
    rw [compactFibreKey_supports_iff_constant]
    exact nonconstant
  refine ⟨targetFree, targetBound, targetSort, term, policy, compactUnsafe, ?_,
    provenanceKey_isExact, provenanceKey_supports policy⟩
  intro exact
  exact compactUnsafe (exact.supports policy)

/-- Compact syntax cannot encode an exact replay codec on the rho cost-layer iteration
witness fibre. -/
theorem rhoCostLayerIteration_no_exact_compact_replay
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort configuration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        configuration.source.costWholeReflectionProfile
        configuration.source.costWholeLanguage targetFree targetBound
        targetSort),
      ¬ ReplayKey.IsExact (compactFibreKey term) := by
  obtain ⟨targetFree, targetBound, targetSort, term, _policy, _compactUnsafe,
      notExact, _provenanceExact, _provenanceSafe⟩ :=
    (rhoCostLayerIteration_cache_replay_boundary configuration representative).2.2
  exact ⟨targetFree, targetBound, targetSort, term, notExact⟩

end Mettapedia.GSLT.LanguageDef.Cost.Elaboration

namespace Mettapedia.GSLT.LanguageDef.Cost.Elaboration

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- On rho's cost-layer iteration witness, retained construction provenance is strictly
more informative than the compact term. -/
theorem rhoCostLayerIteration_provenance_strictlyRefines_compact
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort configuration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        configuration.source.costWholeReflectionProfile
        configuration.source.costWholeLanguage targetFree targetBound
        targetSort),
      ReplayKey.StrictlyRefines
        (provenanceKey (source := configuration.source) (term := term))
        (compactFibreKey term) := by
  obtain ⟨targetFree, targetBound, targetSort, term, policy, compactUnsafe,
      _compactNotExact, provenanceExact, _provenanceSafe⟩ :=
    (rhoCostLayerIteration_cache_replay_boundary configuration representative).2.2
  refine ⟨targetFree, targetBound, targetSort, term,
    ReplayKey.IsExact.refines provenanceExact (compactFibreKey term), ?_⟩
  intro compactRefinesProvenance
  exact compactUnsafe
    (compactRefinesProvenance.supports (provenanceKey_supports policy))

/-- The strict rho cost-layer iteration information order has a direct replay failure: every
compact decoder misreplays at least one of two collided elaborations. -/
theorem rhoCostLayerIteration_compact_collision_forces_decode_failure
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort configuration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        configuration.source.costWholeReflectionProfile
        configuration.source.costWholeLanguage targetFree targetBound
        targetSort)
      (policy : CostOpenElaboration configuration.source term → Bool)
      (left right : CostOpenElaboration configuration.source term),
      policy left ≠ policy right ∧
        left ≠ right ∧
        compactFibreKey term left = compactFibreKey term right ∧
        ∀ decode :
            ReflectiveWellSorted.OpenTerm
                configuration.source.costWholeReflectionProfile
                configuration.source.costWholeLanguage targetFree targetBound
                targetSort →
              CostOpenElaboration configuration.source term,
          decode (compactFibreKey term left) ≠ left ∨
            decode (compactFibreKey term right) ≠ right := by
  obtain ⟨targetFree, targetBound, targetSort, term, policy, nonconstant⟩ :=
    rhoCostLayerFor_exists_nonconstant_fiber_policy configuration representative
  obtain ⟨left, right, policyDifferent⟩ :=
    ReplayKey.exists_bool_distinguished_pair policy nonconstant
  have different : left ≠ right := by
    intro same
    exact policyDifferent (congrArg policy same)
  refine ⟨targetFree, targetBound, targetSort, term, policy, left, right,
    policyDifferent, different, rfl, ?_⟩
  intro decode
  exact ReplayKey.collision_forces_decode_failure
    (key := compactFibreKey term) (left := left) (right := right)
    different rfl decode

end Mettapedia.GSLT.LanguageDef.Cost.Elaboration

namespace Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Rho's cost-layer iteration witness distinguishes request-scoped policy sufficiency from
exact replay without introducing another semantic authority. -/
theorem rhoCostLayerIteration_nik_policy_key_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort configuration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        configuration.source.costWholeReflectionProfile
        configuration.source.costWholeLanguage targetFree targetBound
        targetSort)
      (policy : CostOpenElaboration configuration.source term → Bool),
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy False) (compactFibreKey term)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy True) (compactFibreKey term)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy False)
          (provenanceKey (source := configuration.source) (term := term))) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest policy True)
          (provenanceKey (source := configuration.source) (term := term))) := by
  obtain ⟨targetFree, targetBound, targetSort, term, policy, compactUnsafe,
      compactNotExact, _provenanceExact, _provenanceSafe⟩ :=
    (rhoCostLayerIteration_cache_replay_boundary configuration representative).2.2
  refine ⟨targetFree, targetBound, targetSort, term, policy, ?_, ?_, ?_, ?_⟩
  · rintro ⟨admission⟩
    exact compactUnsafe (admission.supports ())
  · rintro ⟨admission⟩
    exact compactNotExact (admission.isExact True.intro)
  · exact ⟨by
      simpa [provenanceKey] using
        (identityKeyAdmission dependencies revision
          (singlePolicyRequest policy False))⟩
  · exact ⟨by
      simpa [provenanceKey] using
        (identityKeyAdmission dependencies revision
          (singlePolicyRequest policy True))⟩

end Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission

namespace Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyContract

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Rho admits the complete compact representation as a hot policy answer but
refuses it as an exact receipt.  The displayed elaboration remains exact. -/
theorem rhoCostLayerIteration_compact_hot_key_but_not_exact_receipt
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey configuration.source) False)
          (compactCarrierKey configuration.source)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey configuration.source) True)
          (compactCarrierKey configuration.source)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey configuration.source) True)
          (id : CostElaborationFiber configuration.source →
            CostElaborationFiber configuration.source)) := by
  constructor
  · exact ⟨compactIdentityPolicyAdmission dependencies revision
      configuration.source⟩
  constructor
  · rintro ⟨admission⟩
    have compactExact :
        ReplayKey.IsExact (compactCarrierKey configuration.source) :=
      admission.isExact True.intro
    have faithful : configuration.source.CostCompactErasureFaithful :=
      (compactCarrierKey_exactReplay_iff_erasureFaithful
        configuration.source).1 compactExact
    exact (rhoCostLayerFor_not_costCompactErasureFaithful
      configuration representative) faithful
  · exact ⟨identityKeyAdmission dependencies revision
      (singlePolicyRequest
        (compactCarrierKey configuration.source) True)⟩

end Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyContract

namespace Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyTransport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyContract
open Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission

/-- The rho compact value is an admitted hot observation, while the same
global key has no exact replay decoder. -/
theorem rho_compact_policy_admission_without_exact_replay
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (configuration :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey configuration.source) False)
          (compactCarrierKey configuration.source)) ∧
      ¬ ReplayKey.IsExact (compactCarrierKey configuration.source) := by
  have boundary := rhoCostLayerIteration_compact_hot_key_but_not_exact_receipt
    dependencies revision configuration representative
  constructor
  · exact boundary.1
  · intro replay
    have faithful : configuration.source.CostCompactErasureFaithful :=
      (compactCarrierKey_exactReplay_iff_erasureFaithful
        configuration.source).1 replay
    exact
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoCostLayerFor_not_costCompactErasureFaithful
        configuration representative) faithful

end Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyTransport

#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.rhoCostLayerIteration_cache_replay_boundary
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.rhoCostLayerIteration_no_exact_compact_replay
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.rhoCostLayerIteration_provenance_strictlyRefines_compact
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.rhoCostLayerIteration_compact_collision_forces_decode_failure
#print axioms Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission.rhoCostLayerIteration_nik_policy_key_boundary
#print axioms Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyContract.rhoCostLayerIteration_compact_hot_key_but_not_exact_receipt
#print axioms Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyTransport.rho_compact_policy_admission_without_exact_replay
