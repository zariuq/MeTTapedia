import Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationPolicyCorollary

/-!
# The reflective-rho instance of the Prime Cost² boundary

The generic Prime Cost² interface is independent of any concrete language.
This annex instantiates its cache, information-order, NIK-admission,
implementation-key, and displayed-transport boundaries with the reflective
rho calculus.

The compact term remains an admissible key for fibre-invariant observations,
but the rho Cost² witness proves that it cannot replay arbitrary retained
elaborations.  The proof-relevant elaboration key remains exact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Rho's Cost² witness produces a concrete future policy for which compact
syntax is neither a safe cache key nor an exact replay key, while the retained
proof-relevant key supports the same policy exactly.

The two normalization negatives are included so the cache statement cannot
be detached from the actual Cost² nonfactorization witness. -/
theorem rhoCostTwo_cache_replay_boundary
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
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
        ¬ PolicySafe (compactFibreKey term) policy ∧
          ¬ ExactReplayKey (compactFibreKey term) ∧
          ExactReplayKey
            (provenanceKey (source := configuration.source) (term := term)) ∧
          PolicySafe
            (provenanceKey (source := configuration.source) (term := term))
            policy := by
  refine ⟨rhoCostOneFor_not_normalizationFactorsThroughCompactErasure
      configuration representative,
    rhoCostOneFor_not_costCompactErasureFaithful configuration representative,
    ?_⟩
  obtain ⟨targetFree, targetBound, targetSort, term, policy, nonconstant⟩ :=
    rhoCostOneFor_exists_nonconstant_fiber_policy configuration representative
  have compactUnsafe : ¬ PolicySafe (compactFibreKey term) policy := by
    rw [compactFibreKey_policySafe_iff_constant]
    exact nonconstant
  refine ⟨targetFree, targetBound, targetSort, term, policy, compactUnsafe, ?_,
    provenanceKey_exactReplayKey, provenanceKey_policySafe policy⟩
  intro exact
  exact compactUnsafe (exact.policySafe policy)

/-- Compact syntax cannot encode an exact replay codec on the rho Cost²
witness fibre. -/
theorem rhoCostTwo_no_exact_compact_replay
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
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
      ¬ ExactReplayKey (compactFibreKey term) := by
  obtain ⟨targetFree, targetBound, targetSort, term, _policy, _compactUnsafe,
      notExact, _provenanceExact, _provenanceSafe⟩ :=
    (rhoCostTwo_cache_replay_boundary configuration representative).2.2
  exact ⟨targetFree, targetBound, targetSort, term, notExact⟩

end Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- On rho's Cost² witness, retained construction provenance is strictly
more informative than the compact term. -/
theorem rhoCostTwo_provenance_strictlyRefines_compact
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
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
      StrictlyRefines
        (provenanceKey (source := configuration.source) (term := term))
        (compactFibreKey term) := by
  obtain ⟨targetFree, targetBound, targetSort, term, _policy, _compactUnsafe,
      compactNotExact, provenanceExact, _provenanceSafe⟩ :=
    (rhoCostTwo_cache_replay_boundary configuration representative).2.2
  refine ⟨targetFree, targetBound, targetSort, term,
    ExactReplayKey.refines provenanceExact (compactFibreKey term), ?_⟩
  intro compactRefinesProvenance
  have identitySafe :
      PolicySafe (compactFibreKey term)
        (id : CostOpenElaboration configuration.source term →
          CostOpenElaboration configuration.source term) := by
    simpa [provenanceKey] using
      (keyRefines_iff_policySafe (compactFibreKey term)
        (provenanceKey (source := configuration.source) (term := term))).1
        compactRefinesProvenance
  exact compactNotExact
    ((exactReplayKey_iff_identityPolicySafe (compactFibreKey term)).2
      identitySafe)

/-- The strict rho Cost² information order has a direct replay failure: every
compact decoder misreplays at least one of two collided elaborations. -/
theorem rhoCostTwo_compact_collision_forces_decode_failure
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
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
    rhoCostOneFor_exists_nonconstant_fiber_policy configuration representative
  obtain ⟨left, right, policyDifferent⟩ :=
    exists_policy_distinguished_pair policy nonconstant
  have different : left ≠ right := by
    intro same
    exact policyDifferent (congrArg policy same)
  refine ⟨targetFree, targetBound, targetSort, term, policy, left, right,
    policyDifferent, different, rfl, ?_⟩
  intro decode
  exact collision_forces_decode_failure
    (key := compactFibreKey term) (left := left) (right := right)
    different rfl decode

end Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Rho's Cost² witness distinguishes request-scoped policy sufficiency from
exact replay without introducing another semantic authority. -/
theorem rhoCostTwo_nik_policy_key_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
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
    (rhoCostTwo_cache_replay_boundary configuration representative).2.2
  refine ⟨targetFree, targetBound, targetSort, term, policy, ?_, ?_, ?_, ?_⟩
  · rintro ⟨admission⟩
    exact compactUnsafe (admission.supports ())
  · rintro ⟨admission⟩
    exact compactNotExact (admission.exactReplayKey True.intro)
  · exact ⟨by
      simpa [provenanceKey] using
        (identityKeyAdmission dependencies revision
          (singlePolicyRequest policy False))⟩
  · exact ⟨by
      simpa [provenanceKey] using
        (identityKeyAdmission dependencies revision
          (singlePolicyRequest policy True))⟩

end Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Rho admits the complete compact representation as a hot policy answer but
refuses it as an exact receipt.  The displayed elaboration remains exact. -/
theorem rhoCostTwo_compact_hot_key_but_not_exact_receipt
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
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
        ExactReplayKey (compactCarrierKey configuration.source) :=
      admission.exactReplayKey True.intro
    have faithful : configuration.source.CostCompactErasureFaithful :=
      (compactCarrierKey_exactReplay_iff_erasureFaithful
        configuration.source).1 compactExact
    exact (rhoCostOneFor_not_costCompactErasureFaithful
      configuration representative) faithful
  · exact ⟨identityKeyAdmission dependencies revision
      (singlePolicyRequest
        (compactCarrierKey configuration.source) True)⟩

end Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission

/-- The rho compact value is an admitted hot observation, while the same
global key has no exact replay decoder. -/
theorem rho_compact_policy_admission_without_exact_replay
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (configuration :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction.RhoCostOneConfiguration)
    (representative :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey configuration.source) False)
          (compactCarrierKey configuration.source)) ∧
      ¬ ExactReplayKey (compactCarrierKey configuration.source) := by
  have boundary := rhoCostTwo_compact_hot_key_but_not_exact_receipt
    dependencies revision configuration representative
  constructor
  · exact boundary.1
  · intro replay
    have faithful : configuration.source.CostCompactErasureFaithful :=
      (compactCarrierKey_exactReplay_iff_erasureFaithful
        configuration.source).1 replay
    exact
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoCostOneFor_not_costCompactErasureFaithful
        configuration representative) faithful

end Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport

#print axioms Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary.rhoCostTwo_cache_replay_boundary
#print axioms Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary.rhoCostTwo_no_exact_compact_replay
#print axioms Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder.rhoCostTwo_provenance_strictlyRefines_compact
#print axioms Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder.rhoCostTwo_compact_collision_forces_decode_failure
#print axioms Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission.rhoCostTwo_nik_policy_key_boundary
#print axioms Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract.rhoCostTwo_compact_hot_key_but_not_exact_receipt
#print axioms Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport.rho_compact_policy_admission_without_exact_replay
