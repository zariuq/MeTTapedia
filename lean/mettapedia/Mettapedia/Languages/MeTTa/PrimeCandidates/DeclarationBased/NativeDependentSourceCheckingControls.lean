import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ExecutableWeakHeadControls

/-!
# Native-wire controls with an explicit declaration inventory

Every source is lowered with the actual number-model signature. A missing
declaration therefore cannot accidentally explain a refusal intended to test
annotations. The expected checking observations below are independently
computed and kernel-verified. Runtime replay is a separate evidence layer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceCheckingControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeDependentSourceWire
open ExecutableWrittenCheckingControls (numA zeroA sortA writtenId wrongDomainId missingDomain
  idType invalidExpected invalidContext invalidContextDomain)
open ExecutableCheckingControls (level pack packType wrongPack polymorphicId polymorphicIdType
  copiedByRecursor numeral num)

structure Probe where
  label : String
  scope : Nat
  context : ExecutableWrittenChecking.SourceContext Tower.Head scope
  term : ATm Tower.Head scope
  type : ATm Tower.Head scope
  expected : Bool

def input (probe : Probe) : Option Wire := do
  let header ← lowerDeclarations (NativeDependentSourceChecking.declarations level)
  lowerScopedOver header probe.context probe.term

def observe (probe : Probe) : Option Bool := do
  let source ← input probe
  let type ← lower probe.type
  return NativeDependentSourceChecking.accepts level 120 probe.scope source type

/-- Actual dependent source formation is recovered from successful lowering
and checking, without supplying a typing tree as input. -/
theorem observe_typed (probe : Probe) (accepted : observe probe = some true) :
    ATyped (TowerNumbersModel.rules level) probe.context.erase probe.term probe.type.erase := by
  unfold observe input at accepted
  cases hh : lowerDeclarations (NativeDependentSourceChecking.declarations level) with
  | none => simp [hh] at accepted
  | some header =>
      cases hs : lowerScopedOver header probe.context probe.term with
      | none => simp [hh, hs] at accepted
      | some source =>
          cases ht : lower probe.type with
          | none => simp [hh, hs, ht] at accepted
          | some type =>
              have decodedSource := decodeInputOver_lowerScopedOver header hs
              have decodedType := lower_decode ht
              simp [hh, hs, ht, NativeDependentSourceChecking.accepts, decodedSource,
                decodedType] at accepted
              exact ExecutableTowerNumbersWeakHead.acceptsSource_sound level accepted

def validContextDomain : ATm Tower.Head 0 :=
  .app (.lamTyped (sortA 1) (sortA 0)) (sortA 0)

def functionContext : ExecutableWrittenChecking.SourceContext Tower.Head 1 :=
  .snoc .nil (.pi numA numA)

def probes : List Probe :=
  [⟨"bare-identity", 0, .nil, .lamBare (.var 0), idType, true⟩,
   ⟨"written-identity", 0, .nil, writtenId, idType, true⟩,
   ⟨"written-domain-mismatch", 0, .nil, wrongDomainId, idType, false⟩,
   ⟨"written-domain-missing", 0, .nil, missingDomain, idType, false⟩,
   ⟨"invalid-annotated-context", 1, invalidContext, .var 0, sortA 0, false⟩,
   ⟨"valid-annotated-context", 1, .snoc .nil validContextDomain, .var 0, sortA 0, true⟩,
   ⟨"erased-invalid-context", 1, .snoc .nil (ATm.ofTm invalidContextDomain.erase),
     .var 0, sortA 0, true⟩,
   ⟨"annotated-expected-endpoint", 0, .nil, .refl missingDomain, invalidExpected, false⟩,
   ⟨"dependent-pack", 0, .nil, ATm.ofTm pack, ATm.ofTm packType, true⟩,
   ⟨"dependent-wrong-endpoint", 0, .nil, ATm.ofTm wrongPack, ATm.ofTm packType, false⟩,
   ⟨"polymorphic-identity", 0, .nil, ATm.ofTm polymorphicId, ATm.ofTm polymorphicIdType, true⟩,
   ⟨"universe-self", 0, .nil, sortA 0, sortA 0, false⟩,
   ⟨"universe-cumulative", 0, .nil, sortA 0, sortA 3, true⟩,
   ⟨"non-type-context", 1, .snoc .nil zeroA, .var 0, zeroA, false⟩,
   ⟨"non-type-expected", 0, .nil, zeroA, zeroA, false⟩,
   ⟨"unused-well-typed-argument", 0, .nil, .app (.lamBare zeroA) (sortA 0), numA, true⟩,
   ⟨"unused-undeclared-argument", 0, .nil, .app (.lamBare zeroA) (.const `missing), numA, false⟩,
   ⟨"wrong-id-endpoint-type", 0, .nil, .refl zeroA, .id numA zeroA (sortA 0), false⟩,
   ⟨"distinct-id-endpoints", 0, .nil, .refl zeroA,
     .id numA zeroA (.app (.const TowerNumbersModel.succ) zeroA), false⟩,
   ⟨"dependent-function-eta", 1, functionContext,
     .refl (.lamBare (.app (.var 1) (.var 0))), .id (.pi numA numA) (.var 0) (.var 0), true⟩,
   ⟨"recursor-typing", 0, .nil, ATm.ofTm (copiedByRecursor 3), numA, true⟩,
   ⟨"recursor-conversion", 0, .nil, .refl (ATm.ofTm (copiedByRecursor 3)),
     .id numA (ATm.ofTm (numeral 3)) (ATm.ofTm (numeral 3)), true⟩]

theorem all_observations : ∀ probe ∈ probes, observe probe = some probe.expected := by
  decide +kernel

theorem accepted_sources_typed : ∀ probe ∈ probes, probe.expected = true →
    ATyped (TowerNumbersModel.rules level) probe.context.erase probe.term probe.type.erase := by
  intro probe member expected
  exact observe_typed probe (expected ▸ all_observations probe member)

theorem inventory_names :
    (NativeDependentSourceChecking.declarations level).map Prod.fst =
      [TowerNumbersModel.numRec, TowerNumbersModel.succ, TowerNumbersModel.zero,
        TowerNumbersModel.num] := rfl

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceCheckingControls
