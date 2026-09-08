import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNativeProofWire
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedImmediateDemand
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedInferenceService

/-!
# Executed admission of raw native proof objects

The selected environment and current revision are service parameters. The
submitted request must equal the expected request in every coordinate before
the actual Mathdata native proof kernel is invoked. Replies retain the raw
submitted packet; no acceptance field in that packet is trusted.

The source allocates and immediately forces a real Need cell containing the
checker call. Independent natural evaluation and reflection retain its exact
final world. Data preservation is not model validity, native dependent proof
inhabitation, cache transport across revisions, or foreign-checker refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedNativeProofService

open Mettapedia.Languages.Megalodon MathdataKernel
open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open Presentation.PolarizedNeedNaturalSemantics
open PolarizedNeedNativeProofWire

inductive Verdict where
  | malformed
  | stale
  | wrongRequest
  | checked (accepted : Bool)
  deriving DecidableEq, Repr

def encodeVerdict : Verdict → Wire
  | .malformed => .symbol "NativeProof.malformed"
  | .stale => .symbol "NativeProof.stale"
  | .wrongRequest => .symbol "NativeProof.wrongRequest"
  | .checked false => .symbol "NativeProof.refused"
  | .checked true => .symbol "NativeProof.admitted"

theorem encodeVerdict_injective : Function.Injective encodeVerdict := by
  intro first second same
  rcases first with _ | _ | _ | (_ | _) <;>
    rcases second with _ | _ | _ | (_ | _) <;> simp_all [encodeVerdict]

def checkPacket (environment : Environment) (current : Scope) (expected : Request)
    (packet : Packet) : Verdict :=
  if expected.scope ≠ current then .stale
  else if packet.request ≠ expected then .wrongRequest
  else .checked (NIKNativeProof.nativeKernel.decide (expected.claim environment) packet.proof)

def evaluate (environment : Environment) (current : Scope) (expected : Request) (input : Wire) : Verdict :=
  match decodePacket input with
  | none => .malformed
  | some packet => checkPacket environment current expected packet

@[simp] theorem evaluate_encode (environment : Environment) (current : Scope)
    (expected : Request) (packet : Packet) :
    evaluate environment current expected (encodePacket packet) =
      checkPacket environment current expected packet := by simp [evaluate]

theorem checkPacket_admitted_iff (environment : Environment) (current : Scope)
    (expected : Request) (packet : Packet) :
    checkPacket environment current expected packet = .checked true ↔
      expected.scope = current ∧ packet.request = expected ∧
      checkProof environment expected.fuel expected.typeDepth expected.termContext
        expected.proofContext packet.proof expected.proposition = true := by
  by_cases scope : expected.scope = current
  · by_cases request : packet.request = expected
    · simp [checkPacket, scope, request, NIKNativeProof.nativeKernel, Request.claim]
    · simp [checkPacket, scope, request]
  · simp [checkPacket, scope]

theorem evaluate_admitted_iff (environment : Environment) (current : Scope)
    (expected : Request) (input : Wire) :
    evaluate environment current expected input = .checked true ↔
      ∃ packet, decodePacket input = some packet ∧ expected.scope = current ∧
        packet.request = expected ∧ checkProof environment expected.fuel expected.typeDepth
          expected.termContext expected.proofContext packet.proof expected.proposition = true := by
  cases decoded : decodePacket input with
  | none => simp [evaluate, decoded]
  | some packet => simp [evaluate, decoded, checkPacket_admitted_iff]

def reply (input : Wire) (verdict : Verdict) : Wire :=
  .application "NativeProof.reply" [input, encodeVerdict verdict]

theorem reply_verdict_injective (input : Wire) : Function.Injective (reply input) := by
  intro first second same
  exact encodeVerdict_injective ((List.cons.inj (List.cons.inj
    ((Mettapedia.GSLT.LanguageDef.CettaWire.Term.application.inj same).2)).2).1)

def signature : ScopedComputation.OperationSignature Tower.Head Unit where
  input _ := NativeWireData.dataType
  output _ := NativeWireData.dataType

theorem operation_formed : ScopedComputation.OperationFormation NativeWireData.rules signature () where
  input_formed := ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed _⟩
  output_formed := ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed _⟩

def primitive {n : Nat} (environment : Environment) (current : Scope) (expected : Request) :
    Unit → Tower.Tm n → Produced (Tower.Tm n) Empty Empty := fun _ argument =>
  .value (NativeWireData.encode (match NativeWireData.decode argument with
    | none => .symbol "NativeProof.malformedNativeData"
    | some input => reply input (evaluate environment current expected input)))

theorem primitive_sound {n : Nat} (environment : Environment) (current : Scope) (expected : Request)
    (context : Tower.Ctx n) :
    PrimitiveSoundness NativeWireData.rules signature context (primitive environment current expected) := by
  intro operation argument value _ _ produced
  simp only [primitive, Produced.value.injEq] at produced
  cases produced
  exact NativeWireData.encode_typing context _

@[simp] theorem primitive_encode {n : Nat} (environment : Environment) (current : Scope)
    (expected : Request) (input : Wire) :
    primitive (n := n) environment current expected () (NativeWireData.encode input) =
      .value (NativeWireData.encode (reply input (evaluate environment current expected input))) := by
  simp only [primitive, NativeWireData.decode_encode]

variable {Effect : Type} {n : Nat}

def source {n v k : Nat} (input : Wire) : Computation Tower.Head Unit Effect n v k :=
  .letNeed (.call () (NativeWireData.encode input)) (.forceNeed 0)

theorem source_typed {n v k : Nat} (context : Tower.Ctx n)
    (values : Fin v → VTy Tower.Head n) (needs : Fin k → CTy Tower.Head n) (input : Wire) :
    ComputationTyping NativeWireData.rules signature context values needs (source (Effect := Effect) input)
      (.returns (.native NativeWireData.dataType)) := by
  have formed : ComputationFormation NativeWireData.rules context (.returns (.native NativeWireData.dataType)) :=
    .returns (.native ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed context⟩)
  exact .letNeed formed formed (.call operation_formed (NativeWireData.encode_typing context input)) (.forceNeed 0)

def callClosure (input : Wire) : Closure Tower.Head Unit Effect n :=
  ⟨0, 0, 0, .call () (NativeWireData.encode input), Fin.elim0, Fin.elim0, Fin.elim0⟩

def sourceClosure (input : Wire) : Closure Tower.Head Unit Effect n :=
  ⟨0, 0, 0, source input, Fin.elim0, Fin.elim0, Fin.elim0⟩

def outcome (wire : Wire) : Outcome Tower.Head Unit Effect Empty Empty n :=
  .value (.returned (.native (NativeWireData.encode wire)))

theorem outcome_injective : Function.Injective (outcome (Effect := Effect) (n := n)) := by
  intro first second same
  exact NativeWireData.encode_injective (RuntimeValue.native.inj (Answer.returned.inj (Produced.value.inj same)))

def finalWorld (world : NeedWorld Tower.Head Unit Effect Empty Empty n)
    (cell : CellId) (origin : Closure Tower.Head Unit Effect n) (wire : Wire) :=
  let entered := enterWorld world cell origin 0 .entry
  let cached := entered.setKnownCache cell ⟨origin, .evaluating world.nextEvaluator⟩
    (.value (.returned (.native (NativeWireData.encode wire))))
  (cached.record (.observe cell (outcome wire))).1

theorem finalize_value (world : NeedWorld Tower.Head Unit Effect Empty Empty n)
    (cell : CellId) (origin : Closure Tower.Head Unit Effect n) (wire : Wire) :
    finalize (enterWorld world cell origin 0 .entry) cell world.nextEvaluator (outcome wire) =
      (outcome wire, finalWorld world cell origin wire) := by
  simp [finalize, enterWorld, World.record, World.setKnownCache, Heap.setKnownCache_lookup_same,
    outcome, finalWorld]

section Execution

variable (environment : Environment) (current : Scope) (expected : Request) (input : Wire)

theorem force_evaluates (world : NeedWorld Tower.Head Unit Effect Empty Empty n) (cell : CellId)
    (suspended : world.heap.lookup cell = some ⟨callClosure input, .suspended⟩) :
    Nonempty (Force (primitive environment current expected) cell world
      (outcome (reply input (evaluate environment current expected input)))
      (finalWorld world cell (callClosure input) (reply input (evaluate environment current expected input)))) := by
  have body : Eval (primitive environment current expected) (callClosure input)
      (enterWorld world cell (callClosure input) 0 .entry)
      (outcome (reply input (evaluate environment current expected input)))
      (enterWorld world cell (callClosure input) 0 .entry) := by
    simpa only [callClosure, NativeWireData.subst_encode, primitive_encode, liftOutcome, outcome] using
      (Eval.call (primitive := primitive environment current expected) () (NativeWireData.encode input)
        Fin.elim0 Fin.elim0 Fin.elim0 (enterWorld world cell (callClosure input) 0 .entry))
  have forced := Force.suspended suspended
    (Selection.entry (by intro left right impossible; cases impossible)) body
  simpa only [finalize_value] using (show Nonempty _ from ⟨forced⟩)

theorem force_exact {world final : NeedWorld Tower.Head Unit Effect Empty Empty n}
    {cell : CellId} {result : Outcome Tower.Head Unit Effect Empty Empty n}
    (suspended : world.heap.lookup cell = some ⟨callClosure input, .suspended⟩)
    (forced : Force (primitive environment current expected) cell world result final) :
    result = outcome (reply input (evaluate environment current expected input)) ∧
      final = finalWorld world cell (callClosure input) (reply input (evaluate environment current expected input)) := by
  cases forced with
  | cachedValue lookup => rw [suspended] at lookup; cases lookup
  | cachedStable lookup => rw [suspended] at lookup; cases lookup
  | missing lookup => rw [suspended] at lookup; cases lookup
  | evaluating lookup => rw [suspended] at lookup; cases lookup
  | suspended lookup selection body =>
      cases Option.some.inj (lookup.symm.trans suspended)
      cases selection with
      | entry _ =>
          cases body with
          | call =>
              simp only [NativeWireData.subst_encode, primitive_encode, liftOutcome]
              change (finalize _ _ _ (outcome _)).1 = _ ∧ (finalize _ _ _ (outcome _)).2 = _
              rw [finalize_value]
              exact ⟨rfl, rfl⟩

theorem source_evaluates {world allocated : NeedWorld Tower.Head Unit Effect Empty Empty n} {cell : CellId}
    (allocation : world.allocate? (callClosure input) = some (allocated, cell)) :
    Nonempty (Eval (primitive environment current expected) (sourceClosure input) world
      (outcome (reply input (evaluate environment current expected input)))
      (finalWorld allocated cell (callClosure input) (reply input (evaluate environment current expected input)))) := by
  obtain ⟨forced⟩ := force_evaluates environment current expected input allocated cell
    (World.allocate?_lookup_same allocation)
  exact ⟨.letNeed allocation (.forceNeed 0 forced)⟩

theorem source_evaluation_exact {world allocated final : NeedWorld Tower.Head Unit Effect Empty Empty n}
    {cell : CellId} {result : Outcome Tower.Head Unit Effect Empty Empty n}
    (allocation : world.allocate? (callClosure input) = some (allocated, cell))
    (evaluation : Eval (primitive environment current expected) (sourceClosure input) world result final) :
    result = outcome (reply input (evaluate environment current expected input)) ∧
      final = finalWorld allocated cell (callClosure input) (reply input (evaluate environment current expected input)) := by
  cases evaluation with
  | letNeed actual body =>
      cases Option.some.inj (actual.symm.trans allocation)
      cases body with
      | forceNeed _ forced =>
          exact force_exact environment current expected input
            (World.allocate?_lookup_same allocation) forced
  | letNeedAllocationFailure _ failed =>
      change world.allocate? (callClosure input) = none at failed
      rw [allocation] at failed
      cases failed

def machine (world : NeedWorld Tower.Head Unit Effect Empty Empty n) (work : Work) :
    NeedMachine Tower.Head Unit Effect Empty Empty n :=
  ⟨world, .run (.evaluate (sourceClosure input) .done) [], work⟩

def answers (world : NeedWorld Tower.Head Unit Effect Empty Empty n) (work : Work) (fuel : Nat) :=
  PrimeNeedLocalSteps.answers (extension (primitive environment current expected)) fuel (machine input world work)

theorem answer_exists (world : NeedWorld Tower.Head Unit Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) :
    ∃ fuel, outcome (reply input (evaluate environment current expected input)) ∈
      answers environment current expected input world work fuel := by
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (callClosure input) 0
  obtain ⟨evaluation⟩ := source_evaluates environment current expected input allocation
  exact evaluation.halts.answers work

theorem halted_exact {world : NeedWorld Tower.Head Unit Effect Empty Empty n}
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {final : NeedMachine Tower.Head Unit Effect Empty Empty n}
    {result : Outcome Tower.Head Unit Effect Empty Empty n}
    (member : final ∈ PrimeNeedLocalSteps.runFrontier (extension (primitive environment current expected)) fuel
      [machine input world work]) (halted : haltedOutcome final = some result) :
    result = outcome (reply input (evaluate environment current expected input)) ∧
      ∃ allocated cell, world.allocate? (callClosure input) = some (allocated, cell) ∧
        final.world = finalWorld allocated cell (callClosure input) (reply input (evaluate environment current expected input)) := by
  obtain ⟨evaluation⟩ := frontier_halt_has_natural_derivation (primitive environment current expected) member halted
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (callClosure input) 0
  obtain ⟨same, finalSame⟩ := source_evaluation_exact environment current expected input allocation evaluation
  exact ⟨same, allocated, _, allocation, finalSame⟩

theorem observed_admission {world : NeedWorld Tower.Head Unit Effect Empty Empty n}
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) {fuel : Nat}
    (observed : outcome (reply input (.checked true)) ∈ answers environment current expected input world work fuel) :
    ∃ packet, decodePacket input = some packet ∧ expected.scope = current ∧ packet.request = expected ∧
      checkProof environment expected.fuel expected.typeDepth expected.termContext
        expected.proofContext packet.proof expected.proposition = true := by
  obtain ⟨final, member, halted⟩ := List.mem_filterMap.mp observed
  have same := (halted_exact environment current expected input bounded work member halted).1
  exact (evaluate_admitted_iff environment current expected input).mp
    ((reply_verdict_injective input (outcome_injective same)).symm)

end Execution

#print axioms encodeVerdict_injective
#print axioms checkPacket_admitted_iff
#print axioms evaluate_admitted_iff
#print axioms primitive_sound
#print axioms source_typed
#print axioms force_evaluates
#print axioms force_exact
#print axioms source_evaluates
#print axioms source_evaluation_exact
#print axioms answer_exists
#print axioms halted_exact
#print axioms observed_admission

end PolarizedNeedNativeProofService
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
