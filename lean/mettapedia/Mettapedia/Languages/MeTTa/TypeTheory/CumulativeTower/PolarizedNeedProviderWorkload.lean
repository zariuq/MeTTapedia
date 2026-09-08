import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedInferenceService
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceMILWorkload

/-!
# Selecting and sharing an input-sensitive inference provider

Each provider is an actual source computation function whose body submits its
native argument to the fixed MIL checker. Selection and per-call effects are
retained in the owned Need machine. Sharing the selected function correlates
the two provider identities; selecting independently permits mixed identities.
Both programs retain both raw replies, including the submitted proof articles.

The source type qualifies raw Data transport, not the represented theorems.
The effects are explicit source events, not a model of checker cost. These
executed controls do not adopt a compiler optimization or a Prime profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedProviderWorkload

open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open PolarizedNeedInferenceService

inductive Event where
  | selecting
  | called (provider : Bool)
  deriving DecidableEq, Repr

abbrev Source := Computation Tower.Head Operation Event 0 0 0
abbrev Machine := NeedMachine Tower.Head Operation Event Empty Empty 0

def providerType {n : Nat} : CTy Tower.Head n :=
  .nativePi NativeWireData.dataType (.returns (.native NativeWireData.dataType))

def pairType {n : Nat} : Tower.Tm n :=
  .sigma NativeWireData.dataType NativeWireData.dataType

/-- The bound native argument is read at every call. This workload shares the
function's selection; no candidate or reply is baked into the function. -/
def provider {n v k : Nat} (identity : Bool) : Computation Tower.Head Operation Event n v k :=
  .nativeLambda (.emit (.called identity) (.call .check (.var 0)))

def selectProvider {n v k : Nat} : Computation Tower.Head Operation Event n v k :=
  .emit .selecting (.choose (provider false) (provider true))

def candidateTerm {n : Nat} (candidate : Candidate) : Tower.Tm n :=
  NativeWireData.encode (RawInferenceService.encodeCandidate candidate)

def sharedProvider {n : Nat} (first second : Candidate) :
    Computation Tower.Head Operation Event n 0 0 :=
  .letNeed selectProvider
    (.sequenceSigma (.nativeApply (.forceNeed 0) (candidateTerm first))
      (.nativeApply (.forceNeed 0) (candidateTerm second)))

def freshProvider {n : Nat} (first second : Candidate) :
    Computation Tower.Head Operation Event n 0 0 :=
  .sequenceSigma (.nativeApply selectProvider (candidateTerm first))
    (.nativeApply selectProvider (candidateTerm second))

theorem data_formed {n : Nat} (context : Tower.Ctx n) :
    NativeFormation NativeWireData.rules context NativeWireData.dataType :=
  ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed context⟩

theorem provider_type_formed {n : Nat} (context : Tower.Ctx n) :
    ComputationFormation NativeWireData.rules context providerType :=
  .nativePi (data_formed context) (.returns (.native (data_formed _)))

theorem pair_type_formed {n : Nat} (context : Tower.Ctx n) :
    NativeFormation NativeWireData.rules context pairType :=
  ⟨.sort (.max Tower.zero Tower.zero), .sort _,
    .sigmaForm (NativeWireData.dataType_formed context) (.sort _)
      (NativeWireData.dataType_formed _) (.sort _) (.sorts _ _)⟩

theorem provider_typed {n v k : Nat} (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n)
    (identity : Bool) :
    ComputationTyping NativeWireData.rules signature context valueTypes needTypes
      (provider identity) providerType :=
  .nativeLambda (data_formed context) (.returns (.native (data_formed _)))
    (.emit (.call (operation_formed .check) (.var 0)))

theorem selectProvider_typed {n v k : Nat} (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n) :
    ComputationTyping NativeWireData.rules signature context valueTypes needTypes
      selectProvider providerType :=
  .emit (.choose (provider_typed context valueTypes needTypes false)
    (provider_typed context valueTypes needTypes true))

theorem sharedProvider_typed {n : Nat} (context : Tower.Ctx n) (first second : Candidate) :
    ComputationTyping NativeWireData.rules signature context Fin.elim0 Fin.elim0
      (sharedProvider first second) (.returns (.native pairType)) := by
  apply ComputationTyping.letNeed (provider_type_formed context)
    (.returns (.native (pair_type_formed context))) (selectProvider_typed context _ _)
  apply ComputationTyping.sequenceSigma (pair_type_formed context)
  · have function : ComputationTyping (Effect := Event) NativeWireData.rules signature context Fin.elim0
        (extendNeedTypes providerType Fin.elim0) (.forceNeed 0) providerType := .forceNeed 0
    exact .nativeApply function (NativeWireData.encode_typing context _)
  · have function : ComputationTyping (Effect := Event) NativeWireData.rules signature
        (.snoc context NativeWireData.dataType)
        (weakenValueTypes (Fin.elim0 : Fin 0 → VTy Tower.Head n))
        (weakenNeedTypes (extendNeedTypes (providerType : CTy Tower.Head n) Fin.elim0))
        (.forceNeed 0) providerType := .forceNeed 0
    exact .nativeApply function (NativeWireData.encode_typing _ _)

theorem freshProvider_typed {n : Nat} (context : Tower.Ctx n) (first second : Candidate) :
    ComputationTyping NativeWireData.rules signature context Fin.elim0 Fin.elim0
      (freshProvider first second) (.returns (.native pairType)) := by
  apply ComputationTyping.sequenceSigma (pair_type_formed context)
  · exact .nativeApply (selectProvider_typed context _ _) (NativeWireData.encode_typing context _)
  · exact .nativeApply (selectProvider_typed _ _ _) (NativeWireData.encode_typing _ _)

def initialWorld : NeedWorld Tower.Head Operation Event Empty Empty 0 :=
  ⟨0, [], .empty, .empty, 0, 0⟩

def initial (source : Source) : Machine :=
  ⟨initialWorld, .run (.evaluate ⟨0, 0, 0, source, Fin.elim0, Fin.elim0, Fin.elim0⟩ .done) [], {}⟩

def frontier (scope : Scope) (fuel : Nat) (source : Source) : List Machine :=
  PrimeNeedLocalSteps.runFrontier (extension (primitive MILCheckedChain.learned.target scope))
    fuel [initial source]

def effects (machine : Machine) : List Event :=
  machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect effect => some effect
    | _ => none

/-- The full frontier remains available. This selected observation retains
literal native answers rather than replacing proof articles with truth tags. -/
def nativeResult (machine : Machine) : Option (Tower.Tm 0) :=
  match haltedOutcome machine with
  | some (.value (.returned (.native term))) => some term
  | _ => none

def observations (scope : Scope) (fuel : Nat) (source : Source) :
    List (Option (Tower.Tm 0) × List Event) :=
  (frontier scope fuel source).map fun machine => (nativeResult machine, effects machine)

theorem initial_typed {source : Source}
    (typed : ComputationTyping NativeWireData.rules signature .nil Fin.elim0 Fin.elim0
      source (.returns (.native pairType))) :
    MachineTyping NativeWireData.rules signature .nil (fun _ => none)
      (initial source) (.returns (.native pairType)) :=
  source_closed_initial_typing typed (fun index => Fin.elim0 index) initialWorld rfl

theorem shared_no_domain_fault (scope : Scope) (first second : Candidate)
    (fault : Fault Empty) (fuel : Nat) :
    .retryableFault (.domain fault) ∉
      PrimeNeedLocalSteps.answers (extension (primitive MILCheckedChain.learned.target scope))
        fuel (initial (sharedProvider first second)) := by
  intro observed
  obtain ⟨native, _⟩ := answers_domain_fault_native
    (primitive_sound MILCheckedChain.learned.target scope .nil)
    (initial_typed (sharedProvider_typed .nil first second)) observed
  exact native.elim

theorem fresh_no_domain_fault (scope : Scope) (first second : Candidate)
    (fault : Fault Empty) (fuel : Nat) :
    .retryableFault (.domain fault) ∉
      PrimeNeedLocalSteps.answers (extension (primitive MILCheckedChain.learned.target scope))
        fuel (initial (freshProvider first second)) := by
  intro observed
  obtain ⟨native, _⟩ := answers_domain_fault_native
    (primitive_sound MILCheckedChain.learned.target scope .nil)
    (initial_typed (freshProvider_typed .nil first second)) observed
  exact native.elim

def scope : Scope := ⟨17, 2⟩

/-- The first article is accepted; the second is rejected for a wrong
intermediate entity, although the represented goal is the same. -/
def acceptedCandidate : Candidate :=
  RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
    MILCheckedChain.motherProof

def rejectedCandidate : Candidate :=
  RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.bob
    MILCheckedChain.wrongMiddleProof

def acceptedReply : Wire := RawInferenceService.encodeReply ⟨acceptedCandidate, .checked true⟩
def rejectedReply : Wire := RawInferenceService.encodeReply ⟨rejectedCandidate, .checked false⟩

def expectedPair : Tower.Tm 0 :=
  .pair (NativeWireData.encode acceptedReply) (NativeWireData.encode rejectedReply)

def sharedWorkload : Source := sharedProvider acceptedCandidate rejectedCandidate
def freshWorkload : Source := freshProvider acceptedCandidate rejectedCandidate

theorem accepted_reply_computed :
    checkedReply MILCheckedChain.learned.target scope acceptedCandidate = acceptedReply := by
  have checked := (RawInferenceService.validate_evaluated _ _ _).mp
    (RawInferenceMILWorkload.mother_service_accepted scope)
  change RawInferenceService.check MILCheckedChain.learned.target scope acceptedCandidate =
    .checked true at checked
  change RawInferenceService.encodeReply
    ⟨acceptedCandidate, RawInferenceService.check MILCheckedChain.learned.target scope acceptedCandidate⟩ = _
  rw [checked]
  rfl

theorem rejected_reply_computed :
    checkedReply MILCheckedChain.learned.target scope rejectedCandidate = rejectedReply := by
  have rejected := RawInferenceMILWorkload.wrong_middle_packet_rejected
  rw [Mettapedia.GSLT.LanguageDef.InferenceCettaWire.encodeDefinition,
    Mettapedia.GSLT.LanguageDef.InferenceCettaWire.checkPacket_encode] at rejected
  change RawInferenceService.encodeReply
    ⟨rejectedCandidate, RawInferenceService.check MILCheckedChain.learned.target scope rejectedCandidate⟩ = _
  unfold rejectedCandidate
  rw [RawInferenceMILWorkload.check_candidate, Option.some.inj rejected]
  rfl

theorem shared_provider_correlates :
    observations scope 64 sharedWorkload =
      [(some expectedPair, [.selecting, .called false, .called false]),
       (some expectedPair, [.selecting, .called true, .called true])] := by
  unfold expectedPair
  rw [← accepted_reply_computed, ← rejected_reply_computed]
  change ([(some (.pair _ _), [.selecting, .called false, .called false]),
    (some (.pair _ _), [.selecting, .called true, .called true])] :
    List (Option (Tower.Tm 0) × List Event)) = _
  simp only [subst, Fin.cases_zero, candidateTerm, NativeWireData.subst_encode,
    NativeWireData.decode_encode, Option.bind_some, RawInferenceService.evaluateWire_encode,
    Option.getD_some, checkedReply]

theorem fresh_provider_selects_independently :
    observations scope 64 freshWorkload =
      [(some expectedPair, [.selecting, .called false, .selecting, .called false]),
       (some expectedPair, [.selecting, .called false, .selecting, .called true]),
       (some expectedPair, [.selecting, .called true, .selecting, .called false]),
       (some expectedPair, [.selecting, .called true, .selecting, .called true])] := by
  unfold expectedPair
  rw [← accepted_reply_computed, ← rejected_reply_computed]
  change ([(some (.pair _ _), [.selecting, .called false, .selecting, .called false]),
    (some (.pair _ _), [.selecting, .called false, .selecting, .called true]),
    (some (.pair _ _), [.selecting, .called true, .selecting, .called false]),
    (some (.pair _ _), [.selecting, .called true, .selecting, .called true])] :
    List (Option (Tower.Tm 0) × List Event)) = _
  simp only [subst, Fin.cases_zero, candidateTerm, NativeWireData.subst_encode,
    NativeWireData.decode_encode, Option.bind_some, RawInferenceService.evaluateWire_encode,
    Option.getD_some, checkedReply]

theorem workloads_have_completed_frontiers :
    (frontier scope 64 sharedWorkload).map isHalted = [true, true] ∧
      (frontier scope 64 freshWorkload).map isHalted = [true, true, true, true] := by
  exact ⟨rfl, rfl⟩

theorem provider_sharing_changes_observation :
    observations scope 64 sharedWorkload ≠ observations scope 64 freshWorkload := by
  intro equal
  have lengths := congrArg List.length equal
  rw [shared_provider_correlates, fresh_provider_selects_independently] at lengths
  cases lengths

theorem shared_provider_not_constant_reply :
    expectedPair ≠ .pair (NativeWireData.encode acceptedReply) (NativeWireData.encode acceptedReply) := by
  intro equal
  have right := Tm.pair.inj equal |>.2
  have wires := NativeWireData.encode_injective right
  have replies := congrArg RawInferenceService.decodeReply wires
  simp only [rejectedReply, acceptedReply, RawInferenceService.decode_encode_reply,
    Option.some.injEq] at replies
  have verdict := congrArg RawInferenceService.Reply.verdict replies
  cases verdict

theorem shared_provider_not_constant_observation :
    observations scope 64 sharedWorkload ≠
      [(some (.pair (NativeWireData.encode acceptedReply) (NativeWireData.encode acceptedReply)),
        [.selecting, .called false, .called false]),
       (some (.pair (NativeWireData.encode acceptedReply) (NativeWireData.encode acceptedReply)),
        [.selecting, .called true, .called true])] := by
  intro same
  rw [shared_provider_correlates] at same
  have first := (List.cons.inj same).1
  exact shared_provider_not_constant_reply (Option.some.inj (congrArg Prod.fst first))

theorem sharing_excludes_mixed_calls :
    (some expectedPair, [.selecting, .called false, .called true]) ∉
      observations scope 64 sharedWorkload := by
  rw [shared_provider_correlates]
  simp

theorem fresh_mixed_calls_occur :
    (some expectedPair, [.selecting, .called false, .selecting, .called true]) ∈
      observations scope 64 freshWorkload := by
  rw [fresh_provider_selects_independently]
  simp

#print axioms data_formed
#print axioms provider_type_formed
#print axioms pair_type_formed
#print axioms provider_typed
#print axioms selectProvider_typed
#print axioms sharedProvider_typed
#print axioms freshProvider_typed
#print axioms initial_typed
#print axioms shared_no_domain_fault
#print axioms fresh_no_domain_fault
#print axioms accepted_reply_computed
#print axioms rejected_reply_computed
#print axioms shared_provider_correlates
#print axioms fresh_provider_selects_independently
#print axioms workloads_have_completed_frontiers
#print axioms provider_sharing_changes_observation
#print axioms shared_provider_not_constant_reply
#print axioms shared_provider_not_constant_observation
#print axioms sharing_excludes_mixed_calls
#print axioms fresh_mixed_calls_occur

end PolarizedNeedProviderWorkload
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
