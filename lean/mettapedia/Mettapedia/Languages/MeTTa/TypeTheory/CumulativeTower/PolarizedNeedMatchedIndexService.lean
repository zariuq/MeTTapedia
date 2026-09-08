import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMatchedIndexData
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeWireData
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalAdequacy
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalMachineLaws
import Mettapedia.Languages.MeTTa.PrimeNeedAllocationBound

/-!
# Executed selected matching and dependent index admission

The source binds the actual raw selection reply and passes it to a separate
complete-request consumer. The existing machine allocates, forces and caches
that reply. Every completed admitted answer has the independently checked
match occurrence and bounded element, with its full receipt retained as data.

Data formation is proved independently of acceptance. The dependent witness
is recovered outside the raw runtime by checker soundness, not installed as a
native Fin type or supplied as a trusted primitive result. Only this finite
two-call source is shown to have a completed result in slot-bounded worlds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedMatchedIndex

open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open Presentation.PolarizedNeedNaturalSemantics

inductive Operation where
  | select
  | consume
  deriving DecidableEq, Repr

def signature : ScopedComputation.OperationSignature Tower.Head Operation where
  input _ := NativeWireData.dataType
  output _ := NativeWireData.dataType

theorem operation_formed (operation : Operation) :
    ScopedComputation.OperationFormation NativeWireData.rules signature operation where
  input_formed := ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed _⟩
  output_formed := ⟨.sort Tower.zero, .sort _, NativeWireData.dataType_formed _⟩

def consumeInput : Wire → Wire
  | .application "PrimeMatchedIndexConsume" [expected, input] =>
      match decodeRequest expected with
      | some request => consumeWire request input
      | none => .symbol "PrimeMatchedIndexMalformedConsumer"
  | _ => .symbol "PrimeMatchedIndexMalformedConsumer"

def primitive {n : Nat} : Operation → Tower.Tm n → Produced (Tower.Tm n) Empty Empty
  | .select, argument => .value (NativeWireData.encode
      (((NativeWireData.decode argument).map selectWire).getD
        (.symbol "PrimeMatchedIndexMalformedRequest")))
  | .consume, argument => .value (NativeWireData.encode
      (((NativeWireData.decode argument).map consumeInput).getD
        (.symbol "PrimeMatchedIndexMalformedConsumer")))

/-- Transport preservation says Data, never that an encoded claim is true. -/
theorem primitive_sound {n : Nat} (context : Tower.Ctx n) :
    PrimitiveSoundness NativeWireData.rules signature context primitive := by
  intro operation argument value _ _ produced
  cases operation <;> simp only [primitive, Produced.value.injEq] at produced <;>
    cases produced <;> exact NativeWireData.encode_typing context _

def consumeArgument {n : Nat} (expected : Request) (reply : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const NativeWireData.applicationName)
    (NativeWireData.encode (.symbol "PrimeMatchedIndexConsume")))
    (.app (.app (.const NativeWireData.consName) (NativeWireData.encode (encodeRequest expected)))
      (.app (.app (.const NativeWireData.consName) reply) (.const NativeWireData.nilName)))

@[simp] theorem consumeArgument_encode {n : Nat} (expected : Request) (reply : Wire) :
    consumeArgument expected (NativeWireData.encode (n := n) reply) =
      NativeWireData.encode (.application "PrimeMatchedIndexConsume" [encodeRequest expected, reply]) := by
  simp only [consumeArgument, NativeWireData.encode, NativeWireData.encodeList]

@[simp] theorem subst_consumeArgument {n m : Nat} (substitution : Sub Tower.Head n m)
    (expected : Request) (reply : Tower.Tm n) :
    subst substitution (consumeArgument expected reply) =
      consumeArgument expected (subst substitution reply) := by
  simp only [consumeArgument, subst, NativeWireData.subst_encode]

@[simp] theorem primitive_select {n : Nat} (request : Request) :
    primitive .select (NativeWireData.encode (n := n) (encodeRequest request)) =
      .value (NativeWireData.encode (selectedWire request)) := by
  simp only [primitive, NativeWireData.decode_encode, Option.map_some, selectWire_request, Option.getD_some]

@[simp] theorem primitive_consume {n : Nat} (expected : Request) (reply : Wire) :
    primitive .consume (consumeArgument expected (NativeWireData.encode (n := n) reply)) =
      .value (NativeWireData.encode (consumeWire expected reply)) := by
  simp only [consumeArgument_encode, primitive, NativeWireData.decode_encode, Option.map_some,
    consumeInput, decode_encode_request, Option.getD_some]

def source {n v k : Nat} {Effect : Type} (expected actual : Request) :
    Computation Tower.Head Operation Effect n v k :=
  .bindNative (.call .select (NativeWireData.encode (encodeRequest actual)))
    (.call .consume (consumeArgument expected (.var 0)))

theorem consumeArgument_typed {n : Nat} {context : Tower.Ctx n} (expected : Request)
    {reply : Tower.Tm n}
    (typed : FormationSensitive.Typing NativeWireData.rules context reply NativeWireData.dataType) :
    FormationSensitive.Typing NativeWireData.rules context (consumeArgument expected reply)
      NativeWireData.dataType :=
  NativeWireData.application_typing (NativeWireData.encode_typing context _)
    (NativeWireData.cons_typing (NativeWireData.encode_typing context _)
      (NativeWireData.cons_typing typed (NativeWireData.nil_typing context)))

theorem source_typed {n v k : Nat} {Effect : Type} (context : Tower.Ctx n)
    (valueTypes : Fin v → VTy Tower.Head n) (needTypes : Fin k → CTy Tower.Head n)
    (expected actual : Request) :
    ComputationTyping NativeWireData.rules signature context valueTypes needTypes
      (source (Effect := Effect) expected actual) (.returns (.native NativeWireData.dataType)) := by
  apply ComputationTyping.bindNative
    ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed context⟩
    (.returns (.native ⟨.sort Tower.zero, Tower.IsUniverse.sort _, NativeWireData.dataType_formed context⟩))
  · exact .call (operation_formed .select) (NativeWireData.encode_typing context _)
  · exact .call (operation_formed .consume) (consumeArgument_typed expected (.var 0))

variable {Effect : Type} {n : Nat}

def selectionOrigin (actual : Request) : Closure Tower.Head Operation Effect n :=
  ⟨0, 0, 0, .call .select (NativeWireData.encode (encodeRequest actual)),
    Fin.elim0, Fin.elim0, Fin.elim0⟩

def sourceClosure (expected actual : Request) : Closure Tower.Head Operation Effect n :=
  ⟨0, 0, 0, source expected actual, Fin.elim0, Fin.elim0, Fin.elim0⟩

def replyOutcome (reply : Wire) : Outcome Tower.Head Operation Effect Empty Empty n :=
  .value (.returned (.native (NativeWireData.encode reply)))

/-- Exact final heap and receipts, including the cached unqualified selection. -/
def replyWorld (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (cell : CellId) (origin : Closure Tower.Head Operation Effect n) (reply : Wire) :
    NeedWorld Tower.Head Operation Effect Empty Empty n :=
  let entered := enterWorld world cell origin 0 .entry
  let cached := entered.setKnownCache cell ⟨origin, .evaluating world.nextEvaluator⟩
    (.value (.returned (.native (NativeWireData.encode reply))))
  (cached.record (.observe cell (replyOutcome reply))).1

theorem finalize_reply (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (cell : CellId) (origin : Closure Tower.Head Operation Effect n) (reply : Wire) :
    finalize (enterWorld world cell origin 0 .entry) cell world.nextEvaluator (replyOutcome reply) =
      (replyOutcome reply, replyWorld world cell origin reply) := by
  simp [finalize, enterWorld, World.record, World.setKnownCache, Heap.setKnownCache_lookup_same,
    replyOutcome, replyWorld]

theorem force_selection (actual : Request)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (cell : CellId)
    (suspended : world.heap.lookup cell = some ⟨selectionOrigin actual, .suspended⟩) :
    Nonempty (Force primitive cell world (replyOutcome (selectedWire actual))
      (replyWorld world cell (selectionOrigin actual) (selectedWire actual))) := by
  have evaluation : Eval primitive (selectionOrigin actual)
      (enterWorld world cell (selectionOrigin actual) 0 .entry)
      (replyOutcome (selectedWire actual))
      (enterWorld world cell (selectionOrigin actual) 0 .entry) := by
    simpa only [selectionOrigin, NativeWireData.subst_encode, primitive_select, liftOutcome,
      replyOutcome] using
      (Eval.call (primitive := primitive) (Effect := Effect) .select
        (NativeWireData.encode (n := 0) (encodeRequest actual))
        (Fin.elim0 : Sub Tower.Head 0 n) Fin.elim0 Fin.elim0
        (enterWorld world cell (selectionOrigin actual) 0 .entry))
  have forcing := Force.suspended suspended
    (Selection.entry (by intro left right impossible; cases impossible)) evaluation
  simpa only [finalize_reply] using (show Nonempty _ from ⟨forcing⟩)

theorem source_evaluates (expected actual : Request)
    {world allocated : NeedWorld Tower.Head Operation Effect Empty Empty n} {cell : CellId}
    (allocation : world.allocate? (selectionOrigin actual) = some (allocated, cell)) :
    Nonempty (Eval primitive (sourceClosure expected actual) world
      (replyOutcome (consumeWire expected (selectedWire actual)))
      (replyWorld allocated cell (selectionOrigin actual) (selectedWire actual))) := by
  obtain ⟨forced⟩ := force_selection actual allocated cell (World.allocate?_lookup_same allocation)
  have consumer : Eval primitive
      (NativeBody.open ⟨0, 0, 0, .call .consume (consumeArgument expected (.var 0)),
        Fin.elim0, Fin.elim0, Fin.elim0⟩ (NativeWireData.encode (selectedWire actual)))
      (replyWorld allocated cell (selectionOrigin actual) (selectedWire actual))
      (replyOutcome (consumeWire expected (selectedWire actual)))
      (replyWorld allocated cell (selectionOrigin actual) (selectedWire actual)) := by
    simpa only [NativeBody.open, subst_consumeArgument, subst, Fin.cases_zero,
      primitive_consume, liftOutcome, replyOutcome] using
      (Eval.call (primitive := primitive) (Effect := Effect) .consume
        (consumeArgument expected (.var (0 : Fin 1)))
        (Fin.cases (NativeWireData.encode (selectedWire actual)) Fin.elim0)
        Fin.elim0 Fin.elim0
        (replyWorld allocated cell (selectionOrigin actual) (selectedWire actual)))
  exact ⟨Eval.bindNativeValue allocation forced consumer⟩

theorem force_selection_exact (actual : Request)
    {world final : NeedWorld Tower.Head Operation Effect Empty Empty n}
    {cell : CellId} {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (suspended : world.heap.lookup cell = some ⟨selectionOrigin actual, .suspended⟩)
    (forcing : Force primitive cell world outcome final) :
    outcome = replyOutcome (selectedWire actual) ∧
      final = replyWorld world cell (selectionOrigin actual) (selectedWire actual) := by
  cases forcing with
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
              simp only [NativeWireData.subst_encode, primitive_select, liftOutcome]
              change (finalize (enterWorld world cell (selectionOrigin actual) 0 .entry)
                cell world.nextEvaluator (replyOutcome (selectedWire actual))).1 = _ ∧
                (finalize (enterWorld world cell (selectionOrigin actual) 0 .entry)
                  cell world.nextEvaluator (replyOutcome (selectedWire actual))).2 = _
              rw [finalize_reply]
              exact ⟨rfl, rfl⟩

theorem source_evaluation_exact (expected actual : Request)
    {world allocated final : NeedWorld Tower.Head Operation Effect Empty Empty n} {cell : CellId}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (allocation : world.allocate? (selectionOrigin actual) = some (allocated, cell))
    (evaluation : Eval primitive (sourceClosure expected actual) world outcome final) :
    outcome = replyOutcome (consumeWire expected (selectedWire actual)) ∧
      final = replyWorld allocated cell (selectionOrigin actual) (selectedWire actual) := by
  cases evaluation with
  | bindNativeValue allocation' forcing consumer =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      obtain ⟨produced, selected⟩ := force_selection_exact actual
        (World.allocate?_lookup_same allocation) forcing
      cases produced
      cases selected
      cases consumer with
      | call =>
          simp only [subst_consumeArgument, subst, Fin.cases_zero, primitive_consume,
            liftOutcome, replyOutcome]
          constructor <;> first | rfl | trivial
  | bindNativeMismatch _ allocation' forcing mismatch =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      cases (force_selection_exact actual (World.allocate?_lookup_same allocation) forcing).1
      exact False.elim (mismatch _ rfl)
  | bindNativeFault _ allocation' forcing fault =>
      cases Option.some.inj (allocation'.symm.trans allocation)
      cases (force_selection_exact actual (World.allocate?_lookup_same allocation) forcing).1
      cases fault
  | bindNativeAllocationFailure _ failed =>
      change world.allocate? (selectionOrigin actual) = none at failed
      rw [allocation] at failed
      cases failed

def sourceMachine (expected actual : Request)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (work : Work) :
    NeedMachine Tower.Head Operation Effect Empty Empty n :=
  ⟨world, .run (.evaluate (sourceClosure expected actual) .done) [], work⟩

def answers (expected actual : Request)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n) (work : Work) (fuel : Nat) :=
  PrimeNeedLocalSteps.answers (extension primitive) fuel (sourceMachine expected actual world work)

/-- Reflection starts from an actual completed frontier, retaining its full world. -/
theorem completed_exact (expected actual : Request)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {final : NeedMachine Tower.Head Operation Effect Empty Empty n}
    {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (member : final ∈ PrimeNeedLocalSteps.runFrontier (extension primitive) fuel
      [sourceMachine expected actual world work])
    (halted : haltedOutcome final = some outcome) :
    outcome = replyOutcome (consumeWire expected (selectedWire actual)) ∧
      ∃ allocated cell, world.allocate? (selectionOrigin actual) = some (allocated, cell) ∧
        final.world = replyWorld allocated cell (selectionOrigin actual) (selectedWire actual) := by
  obtain ⟨evaluation⟩ := frontier_halt_has_natural_derivation primitive member halted
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (selectionOrigin actual) 0
  obtain ⟨same, finalWorld⟩ := source_evaluation_exact expected actual allocation evaluation
  exact ⟨same, allocated, _, allocation, finalWorld⟩

theorem answer_exact (expected actual : Request)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work)
    {fuel : Nat} {outcome : Outcome Tower.Head Operation Effect Empty Empty n}
    (observed : outcome ∈ answers expected actual world work fuel) :
    outcome = replyOutcome (consumeWire expected (selectedWire actual)) := by
  obtain ⟨final, member, halted⟩ := List.mem_filterMap.mp observed
  exact (completed_exact expected actual world bounded work member halted).1

theorem answer_exists (expected actual : Request)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) :
    ∃ fuel, replyOutcome (consumeWire expected (selectedWire actual)) ∈
      answers expected actual world work fuel := by
  obtain ⟨allocated, allocation⟩ := bounded.allocate_succeeds (selectionOrigin actual) 0
  obtain ⟨evaluation⟩ := source_evaluates expected actual allocation
  exact evaluation.halts.answers work

/-- The admitted raw artifact itself supplies the dependent witness. No
independent replacement selection or proof-bearing primitive is assumed. -/
theorem observed_evidence (expected actual : Request) (receipt : Receipt)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) {fuel : Nat}
    (observed : replyOutcome (admittedWire receipt) ∈ answers expected actual world work fuel) :
    select? actual = some receipt ∧ Nonempty (Evidence expected receipt) := by
  have same := answer_exact expected actual world bounded work observed
  have wireSame := NativeWireData.encode_injective
    (RuntimeValue.native.inj (Answer.returned.inj (Produced.value.inj same)))
  obtain ⟨selected, checked⟩ := (consume_selected_iff expected actual receipt).mp wireSame.symm
  exact ⟨selected, (validate_evidence_iff _ _).mp checked⟩

/-- Every independently checked successful selection has an actual completed
admitted execution; the producer need not be assumed to terminate. -/
theorem selected_eventually_admitted (request : Request) (receipt : Receipt)
    (selected : select? request = some receipt)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) :
    ∃ fuel, replyOutcome (admittedWire receipt) ∈ answers request request world work fuel := by
  have admitted := (consume_selected_iff request request receipt).mpr
    ⟨selected, select_validates selected⟩
  simpa only [admitted] using answer_exists request request world bounded work

theorem wrong_selection_never_admitted (expected actual : Request)
    (different : actual ≠ expected) (receipt : Receipt)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) (fuel : Nat) :
    replyOutcome (admittedWire receipt) ∉ answers expected actual world work fuel := by
  intro observed
  obtain ⟨selected, ⟨evidence⟩⟩ := observed_evidence expected actual receipt world bounded work observed
  have actualEq := ((validate_iff actual receipt).mp (select_validates selected)).1
  exact different (actualEq.symm.trans evidence.request_eq)

theorem outside_never_admitted (expected actual : Request) (receipt : Receipt)
    (outside : receipt.values.length ≤ expected.index)
    (world : NeedWorld Tower.Head Operation Effect Empty Empty n)
    (bounded : PrimeNeedAllocationBound.SlotBound world) (work : Work) (fuel : Nat) :
    replyOutcome (admittedWire receipt) ∉ answers expected actual world work fuel := by
  intro observed
  obtain ⟨_, ⟨evidence⟩⟩ := observed_evidence expected actual receipt world bounded work observed
  have bound := evidence.index.isLt
  rw [evidence.index_eq] at bound
  exact Nat.not_lt_of_ge outside bound

#print axioms primitive_sound
#print axioms source_typed
#print axioms source_evaluates
#print axioms source_evaluation_exact
#print axioms completed_exact
#print axioms answer_exact
#print axioms answer_exists
#print axioms observed_evidence
#print axioms selected_eventually_admitted
#print axioms wrong_selection_never_admitted
#print axioms outside_never_admitted

end PolarizedNeedMatchedIndex
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
