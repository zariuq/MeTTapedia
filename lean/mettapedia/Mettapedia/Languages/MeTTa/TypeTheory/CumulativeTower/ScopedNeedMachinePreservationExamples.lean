import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachinePreservation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationExamples

/-!
# Dependent native operations on the owned Need machine

The raw primitive implementation and its native signature are independent.
Retaining an argument returns its declared ground type; reflexivity returns
the identity fibre indexed by that actual argument. A changed implementation
can still return a raw native term while violating this dependent contract.

The source suspension chooses a native argument once, forces it twice and
constructs its dependent reflexivity pair. General whole-control preservation
qualifies every returned value of every independently typed source over these
operations, from an empty heap and a typed native environment. The mathematical
payloads remain raw terms; neither primitive outputs nor machine values contain
typing proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine.PreservationExamples

open PrimeNeedReference
open ScopedComputation (OperationSignature OperationFormation)
open ScopedNeedComputation (Code)

inductive Operation where
  | retain
  | reflexivity
  deriving DecidableEq, Repr

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def signature : OperationSignature Tower.Head Operation where
  input _ := ground
  output
    | .retain => ground
    | .reflexivity => .id ground (.var 0) (.var 0)

/-- Both declarations are independently formed by the actual native rules. -/
theorem operation_formation (operation : Operation) :
    OperationFormation Tower.rules signature operation := by
  constructor
  · exact ⟨.sort Tower.zero, .sort Tower.zero, .headType .legacyGround⟩
  · cases operation with
    | retain => exact ⟨.sort Tower.zero, .sort Tower.zero, .headType .legacyGround⟩
    | reflexivity =>
        exact ⟨.sort Tower.zero, .sort Tower.zero,
          .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩

/-- The handler returns raw values, not values paired with native proofs. -/
def primitive {m : Nat} : Operation → Tower.Tm m → Produced (Tower.Tm m) Empty Empty
  | .retain, argument => .value argument
  | .reflexivity, argument => .value (.refl argument)

/-- Implementation qualification holds for every admitted argument in every
native context, not merely for the displayed shared-choice execution. -/
theorem primitive_value_typing {m : Nat} {Δ : Tower.Ctx m}
    (operation : Operation) (argument value : Tower.Tm m)
    (admitted : FormationSensitive.Typing Tower.rules Δ argument
      (liftClosed (signature.input operation)))
    (returned : primitive operation argument = .value value) :
    FormationSensitive.Typing Tower.rules Δ value (signature.result operation argument) := by
  cases operation with
  | retain =>
      cases returned
      exact admitted
  | reflexivity =>
      cases returned
      exact .reflIntro admitted

/-- Discharge the actual machine primitive contract for every native context. -/
theorem primitive_sound {m : Nat} {Δ : Tower.Ctx m} :
    PrimitiveSoundness Tower.rules signature Δ primitive := by
  intro operation argument value _ admitted returned
  exact primitive_value_typing operation argument value admitted returned

abbrev context := ScopedComputation.NativeExamples.context
abbrev older := ScopedComputation.NativeExamples.older
abbrev newer := ScopedComputation.NativeExamples.newer
abbrev identityFamily := ScopedComputation.NativeExamples.identityFamily

theorem context_formed : FormationSensitive.ContextFormation Tower.rules context :=
  ScopedComputation.NativeExamples.context_formed

theorem sigma_formed : FormationSensitive.Typing Tower.rules context
    (.sigma ground identityFamily) (sortTm (.max Tower.zero Tower.zero)) :=
  ScopedComputation.NativeExamples.sigma_formed

def producer : Code Tower.Head Operation Nat 2 0 :=
  .choose (.emit 10 (.call .retain older)) (.emit 20 (.call .retain newer))

/-- The second force crosses a native binder but still addresses the same
cell. The final reflexivity argument is the retained first selected value. -/
def source : Code Tower.Head Operation Nat 2 0 :=
  .letNeed producer
    (.sequenceSigma (.force 0)
      (.sequence (.force 0) (.call .reflexivity (.var 1))))

theorem producer_typing :
    ScopedNeedComputation.Typing Tower.rules signature context Fin.elim0 producer ground :=
  .choose (.emit (.call (operation_formation .retain) (.var 1)))
    (.emit (.call (operation_formation .retain) (.var 0)))

/-- Initial source typing does not inspect the runtime handler or heap. -/
theorem source_typing :
    ScopedNeedComputation.Typing Tower.rules signature context Fin.elim0 source
      (.sigma ground identityFamily) := by
  refine .letNeed
    (.headType .legacyGround) (.sort Tower.zero) sigma_formed (.sort _) producer_typing ?_
  refine .sequenceSigma sigma_formed (.sort _) (.force 0) ?_
  refine .sequence
    (.headType .legacyGround) (.sort Tower.zero)
    (.idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0))
    (.sort Tower.zero) (.force 0) ?_
  exact .call (operation_formation .reflexivity) (.var 1)

theorem source_judgment :
    ScopedNeedComputation.Judgment Tower.rules signature context Fin.elim0 source
      (.sigma ground identityFamily) :=
  ⟨context_formed, fun index => Fin.elim0 index, source_typing⟩

/-- An empty-heap initial state for independently supplied scoped code and
native substitution. This constructs a state, not another evaluator. -/
def initial {Effect : Type} {n m : Nat} (code : Code Tower.Head Operation Effect n 0)
    (values : Sub Tower.Head n m) : NeedMachine Tower.Head Operation Effect Empty Empty m where
  world :=
    { lineage := 0, path := [], heap := .empty, receipts := .empty,
      nextCell := 0, nextEvaluator := 0 }
  control := .run (.evaluate ⟨n, 0, code, values, Fin.elim0⟩ .done) []

/-- Source typing and the captured native environment establish the initial
machine invariant. No condition on an intermediate or final heap is assumed. -/
theorem initial_typed {Effect : Type} {n m : Nat} {Γ : Tower.Ctx n} {Δ : Tower.Ctx m}
    {code : Code Tower.Head Operation Effect n 0} {A : Tower.Tm n}
    (source : ScopedNeedComputation.Typing Tower.rules signature Γ Fin.elim0 code A)
    {values : Sub Tower.Head n m} (environment : FormationSensitive.CtxMor Tower.rules Γ Δ values) :
    MachineTyping Tower.rules signature Δ (fun _ => none) (initial code values) (subst values A) :=
  source_initial_typing source environment (initial code values).world rfl

/-- Every actual returned value of every independently typed source over the
qualified operations has its substituted native judgment. The theorem covers
all fuel bounds and all returned branches, not just the concrete source below. -/
theorem admitted_program_results {Effect : Type} {n m : Nat} {Γ : Tower.Ctx n} {Δ : Tower.Ctx m}
    {code : Code Tower.Head Operation Effect n 0} {A : Tower.Tm n}
    (source : ScopedNeedComputation.Judgment Tower.rules signature Γ Fin.elim0 code A)
    {values : Sub Tower.Head n m}
    (target : FormationSensitive.ContextFormation Tower.rules Δ)
    (environment : FormationSensitive.CtxMor Tower.rules Γ Δ values)
    {fuel : Nat} {value : Tower.Tm m}
    (returned : Produced.value value ∈ answers (spec primitive) fuel (initial code values)) :
    FormationSensitive.Judgment Tower.rules Δ value (subst values A) :=
  answers_value_judgment primitive_sound target (initial_typed source.typing environment) returned

/-- The shared dependent source inherits the general theorem; its final
heap typing is established by preservation, not supplied as a fixture. -/
theorem source_results {fuel : Nat} {value : Tower.Tm 2}
    (returned : Produced.value value ∈ answers (spec primitive) fuel (initial source ids)) :
    FormationSensitive.Judgment Tower.rules context value (.sigma ground identityFamily) := by
  have environment : FormationSensitive.CtxMor Tower.rules context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index)
  simpa only [subst_ids] using admitted_program_results source_judgment context_formed
    environment returned

/-- Project only chronological source effect receipts, retaining the outcome
status. Administrative singleton forks are not source choice observations. -/
def observe (machine : NeedMachine Tower.Head Operation Nat Empty Empty 2) :
    Option (Outcome Tower.Head Empty Empty 2) × List Nat :=
  (haltedOutcome machine, machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect event => some event
    | _ => none)

/-- The single captured producer branches once. Repeated force records no
second producer effect and preserves the selected native identity fibre. -/
theorem source_execution :
    (runFrontier (spec primitive) 64 [initial source ids]).map observe =
      [(some (.value (.pair older (.refl older))), [10]),
       (some (.value (.pair newer (.refl newer))), [20])] := rfl

theorem source_answers :
    answers (spec primitive) 64 (initial source ids) =
      [.value (.pair older (.refl older)), .value (.pair newer (.refl newer))] := rfl

theorem older_result_admitted :
    FormationSensitive.Judgment Tower.rules context (.pair older (.refl older))
      (.sigma ground identityFamily) := by
  apply source_results (fuel := 64)
  rw [source_answers]
  exact List.mem_cons_self

theorem newer_result_admitted :
    FormationSensitive.Judgment Tower.rules context (.pair newer (.refl newer))
      (.sigma ground identityFamily) := by
  apply source_results (fuel := 64)
  rw [source_answers]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- This altered primitive disregards reflexivity's actual native index. -/
def misindexedPrimitive : Operation → Tower.Tm 2 → Produced (Tower.Tm 2) Empty Empty
  | .retain, argument => .value argument
  | .reflexivity, _ => .value (.refl older)

theorem misindexed_returns_wrong_fibre :
    misindexedPrimitive .reflexivity newer = .value (.refl older) := rfl

/-- The actual refined Tower judgment rejects this returned term, including
its native conversion and cumulativity tail rules. -/
theorem misindexed_result_not_typed :
    ¬ FormationSensitive.Typing Tower.rules context (.refl older)
      (signature.result .reflexivity newer) :=
  ScopedComputation.NativeExamples.wrong_selected_index_not_admitted

/-- Operational return is not enough to qualify the declared dependent
signature, even when that signature is independently formed. -/
theorem misindexed_primitive_not_sound :
    ¬ PrimitiveSoundness Tower.rules signature context misindexedPrimitive := by
  intro sound
  exact misindexed_result_not_typed
    (sound .reflexivity newer (.refl older) (operation_formation .reflexivity)
      (.var 0) misindexed_returns_wrong_fibre)

def wrongSource : Code Tower.Head Operation Nat 2 0 := .call .reflexivity newer

theorem wrongSource_typing :
    ScopedNeedComputation.Typing Tower.rules signature context Fin.elim0 wrongSource
      (signature.result .reflexivity newer) :=
  .call (operation_formation .reflexivity) (.var 0)

/-- Source admission alone cannot repair an unqualified primitive. -/
theorem misindexed_machine_returns :
    answers (spec misindexedPrimitive) 2 (initial wrongSource ids) =
      [.value (.refl older)] := rfl

theorem misindexed_return_not_admitted :
    ¬ FormationSensitive.Judgment Tower.rules context (.refl older)
      (signature.result .reflexivity newer) := by
  intro admitted
  exact misindexed_result_not_typed admitted.typing

#print axioms operation_formation
#print axioms primitive_value_typing
#print axioms primitive_sound
#print axioms source_typing
#print axioms source_judgment
#print axioms initial_typed
#print axioms admitted_program_results
#print axioms source_results
#print axioms source_execution
#print axioms source_answers
#print axioms older_result_admitted
#print axioms newer_result_admitted
#print axioms misindexed_result_not_typed
#print axioms misindexed_primitive_not_sound
#print axioms wrongSource_typing
#print axioms misindexed_machine_returns
#print axioms misindexed_return_not_admitted

end ScopedNeedMachine.PreservationExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
