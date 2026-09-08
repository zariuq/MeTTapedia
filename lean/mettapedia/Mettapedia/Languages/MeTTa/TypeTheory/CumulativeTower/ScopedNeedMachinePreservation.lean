import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineControlTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineTypingLaws

/-!
# Whole-control preservation for scoped native Need computations

The existing machine runs raw source closures and stores raw native terms.
Independent source typing, primitive-result qualification and a proof-side
cell-type assignment qualify every actual successor, including allocation,
choice, consumer resumption and owned commit. The assignment may grow at fresh
allocation; the declared type of an older cell does not change.

Faults remain outcomes, not inhabitants of native mathematical types. The
theorem is preservation, not normalization, fault freedom or adequacy for a
full CBPV language. No machine transition is replaced by a typing oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

/-- A commit preserves its cell's declared result type. A consumer may change
the result type only through its independently qualified resume protocol. -/
inductive StackTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    List (Frame (Resume Head Operation Effect m)) → Tm Head m → Tm Head m → Prop where
  | nil (A : Tm Head m) : StackTyping R signature Δ types [] A A
  | commit {cell : CellId} {owner : EvaluatorId}
      {rest : List (Frame (Resume Head Operation Effect m))} {A B : Tm Head m} :
      types cell = some A → StackTyping R signature Δ types rest A B →
      StackTyping R signature Δ types (.commit cell owner :: rest) A B
  | resume {token : Resume Head Operation Effect m}
      {rest : List (Frame (Resume Head Operation Effect m))} {A B C : Tm Head m} :
      DemandTyping R signature Δ types token A B →
      StackTyping R signature Δ types rest B C →
      StackTyping R signature Δ types (.resume token :: rest) A C

theorem StackTyping.extend {before after : CellTypes Head m}
    {stack : List (Frame (Resume Head Operation Effect m))} {A B : Tm Head m}
    (typed : StackTyping R signature Δ before stack A B)
    (extension : StoreExtends before after) : StackTyping R signature Δ after stack A B := by
  induction typed with
  | nil A => exact .nil A
  | commit declared _ ih => exact .commit (extension _ _ declared) ih
  | resume demand _ ih => exact .resume (demand.extend extension) ih

/-- Local return types and outer consumers are aligned explicitly. -/
inductive ControlTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Control (Local Head Operation Effect StableFault NativeFault m)
      (Resume Head Operation Effect m) (Tm Head m) StableFault (Fault NativeFault) →
        Tm Head m → Prop where
  | force {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
      {A B : Tm Head m} :
      types cell = some A → StackTyping R signature Δ types stack A B →
      ControlTyping R signature Δ types (.force cell stack) B
  | run {state : Local Head Operation Effect StableFault NativeFault m}
      {stack : List (Frame (Resume Head Operation Effect m))} {A B : Tm Head m} :
      LocalTyping R signature Δ types state A → StackTyping R signature Δ types stack A B →
      ControlTyping R signature Δ types (.run state stack) B
  | returned {outcome : Outcome Head StableFault NativeFault m}
      {stack : List (Frame (Resume Head Operation Effect m))} {A B : Tm Head m} :
      OutcomeTyping R Δ A outcome → StackTyping R signature Δ types stack A B →
      ControlTyping R signature Δ types (.returned outcome stack) B
  | halted {outcome : Outcome Head StableFault NativeFault m} {A : Tm Head m} :
      OutcomeTyping R Δ A outcome → ControlTyping R signature Δ types (.halted outcome) A

theorem ControlTyping.extend {before after : CellTypes Head m}
    {control : Control (Local Head Operation Effect StableFault NativeFault m)
      (Resume Head Operation Effect m) (Tm Head m) StableFault (Fault NativeFault)}
    {A : Tm Head m} (typed : ControlTyping R signature Δ before control A)
    (extension : StoreExtends before after) : ControlTyping R signature Δ after control A := by
  cases typed with
  | force declared stack => exact .force (extension _ _ declared) (stack.extend extension)
  | run stateTyped stack => exact .run (stateTyped.extend extension) (stack.extend extension)
  | returned outcome stack => exact .returned outcome (stack.extend extension)
  | halted outcome => exact .halted outcome

structure MachineTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (A : Tm Head m) : Prop where
  heap : HeapTyping R signature Δ types machine.world.heap
  control : ControlTyping R signature Δ types machine.control A

private theorem retryMachine_typed
    {machine : NeedMachine Head Operation Effect StableFault NativeFault m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {types : CellTypes Head m} {A B : Tm Head m}
    (heap : HeapTyping R signature Δ types world.heap)
    {stack : List (Frame (Resume Head Operation Effect m))}
    (typed : StackTyping R signature Δ types stack A B)
    (cell : CellId) (reason : RetryReason (Fault NativeFault))
    (lookups updates receipts allocations : Nat) :
    MachineTyping R signature Δ types
      (retryMachine machine world cell reason stack lookups updates receipts allocations) B :=
  ⟨heap, .returned (.retryableFault reason) typed⟩

private theorem branchAlternatives_preservation
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    {base : NeedWorld Head Operation Effect StableFault NativeFault m}
    {types : CellTypes Head m} {A B : Tm Head m}
    (heap : HeapTyping R signature Δ types base.heap)
    (cell : CellId) (record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault)
    (present : base.heap.lookup cell = some record) (declared : types cell = some A)
    (owner : EvaluatorId) {stack : List (Frame (Resume Head Operation Effect m))}
    (typed : StackTyping R signature Δ types stack A B)
    (start : Nat) (choices : List (Rule × Local Head Operation Effect StableFault NativeFault m))
    (admitted : ∀ choice ∈ choices, LocalTyping R signature Δ types choice.2 A)
    {candidate : NeedMachine Head Operation Effect StableFault NativeFault m}
    (member : candidate ∈ branchAlternatives machine base cell record owner stack start choices) :
    MachineTyping R signature Δ types candidate B := by
  induction choices generalizing start candidate with
  | nil => simp [branchAlternatives] at member
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at member
      rcases member with equal | member
      · subst candidate
        exact ⟨heap.setKnownCache present declared (.evaluating owner),
          .run (admitted head (by simp)) (.commit declared typed)⟩
      · exact ih (start + 1) (fun choice membership => admitted choice (by simp [membership])) member

/-- Every actual successor preserves the independently assigned final native
type. Only fresh allocation extends the proof-side cell assignment. -/
theorem step_preservation
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : Tm Head m}
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types machine A)
    (member : next ∈ step (spec primitive) machine) :
    ∃ nextTypes, StoreExtends types nextTypes ∧ MachineTyping R signature Δ nextTypes next A := by
  rcases machine with ⟨world, control, work⟩
  obtain ⟨heap, controlTyped⟩ := typed
  change HeapTyping R signature Δ types world.heap at heap
  change ControlTyping R signature Δ types control A at controlTyped
  cases controlTyped with
  | halted outcome => simp [step] at member
  | force declared stackTyped =>
      rename_i cell stack B
      refine ⟨types, StoreExtends.refl types, ?_⟩
      cases present : world.heap.lookup cell with
      | none =>
          simp only [step, present, List.mem_singleton] at member
          subst next
          exact retryMachine_typed heap stackTyped _ _ _ _ _ _
      | some record =>
          obtain ⟨originTyped, cacheTyped⟩ := heap.lookup_typed declared present
          obtain ⟨origin, cache⟩ := record
          cases cache with
          | suspended =>
              cases choices : alternatives (StableFault := StableFault) (NativeFault := NativeFault) origin with
              | nil =>
                  simp only [step, spec, present, choices, List.mem_singleton] at member
                  subst next
                  exact ⟨heap, .returned (.retryableFault (.noRule cell)) stackTyped⟩
              | cons head tail =>
                  simp only [step, spec, present, choices] at member
                  exact branchAlternatives_preservation _
                    (base := { world with nextEvaluator := world.nextEvaluator + 1 })
                    heap cell ⟨origin, .suspended⟩ present declared world.nextEvaluator stackTyped
                    0 (head :: tail) (fun choice membership => originTyped.alternatives
                      (by simpa only [choices] using membership)) member
          | evaluating owner =>
              simp only [step, present, List.mem_singleton] at member
              subst next
              exact retryMachine_typed heap stackTyped _ _ _ _ _ _
          | value value =>
              simp only [step, present, List.mem_singleton] at member
              subst next
              cases cacheTyped with
              | value admitted => exact ⟨heap, .returned (.value admitted) stackTyped⟩
          | stableFault fault =>
              simp only [step, present, List.mem_singleton] at member
              subst next
              exact ⟨heap, .returned (.stableFault fault) stackTyped⟩
  | run stateTyped stackTyped =>
      rename_i state stack B
      have actionTyped := stateTyped.action sound
      cases actionEq : action primitive state with
      | done outcome =>
          rw [actionEq] at actionTyped
          cases actionTyped with
          | done admitted =>
              simp only [step, spec, actionEq, List.mem_singleton] at member
              subst next
              exact ⟨types, StoreExtends.refl types, heap, .returned admitted stackTyped⟩
      | demand cell resume =>
          rw [actionEq] at actionTyped
          cases actionTyped with
          | demand declared demandTyped =>
              simp only [step, spec, actionEq, List.mem_singleton] at member
              subst next
              exact ⟨types, StoreExtends.refl types, heap,
                .force declared (.resume demandTyped stackTyped)⟩
      | allocate origin resume =>
          rw [actionEq] at actionTyped
          cases actionTyped with
          | allocate originTyped resumeTyped =>
              cases allocated : world.allocate? origin with
              | none =>
                  simp only [step, spec, actionEq, allocated, List.mem_singleton] at member
                  subst next
                  exact ⟨types, StoreExtends.refl types,
                    retryMachine_typed heap stackTyped _ _ _ _ _ _⟩
              | some result =>
                  obtain ⟨nextWorld, cell⟩ := result
                  simp only [step, spec, actionEq, allocated, List.mem_singleton] at member
                  subst next
                  obtain ⟨extension, declared, nextHeap⟩ := heap.allocate_package originTyped allocated
                  exact ⟨_, extension, nextHeap,
                    .run ((resumeTyped.extend extension).afterAllocation declared)
                      (stackTyped.extend extension)⟩
      | resample source resume =>
          rw [actionEq] at actionTyped
          cases actionTyped
      | perform effect nextLocal =>
          rw [actionEq] at actionTyped
          cases actionTyped with
          | perform nextTyped =>
              simp only [step, spec, actionEq, List.mem_singleton] at member
              subst next
              exact ⟨types, StoreExtends.refl types, heap, .run nextTyped stackTyped⟩
  | returned outcomeTyped stackTyped =>
      rename_i outcome stack B
      refine ⟨types, StoreExtends.refl types, ?_⟩
      cases stackTyped with
      | nil =>
          simp only [step, List.mem_singleton] at member
          subst next
          exact ⟨heap, .halted outcomeTyped⟩
      | resume demandTyped restTyped =>
          simp only [step, List.mem_singleton] at member
          subst next
          exact ⟨heap, .run (demandTyped.afterDemand outcomeTyped) restTyped⟩
      | commit declared restTyped =>
          rename_i cell owner rest
          cases present : world.heap.lookup cell with
          | none =>
              simp only [step, present, List.mem_singleton] at member
              subst next
              exact retryMachine_typed heap restTyped _ _ _ _ _ _
          | some record =>
              obtain ⟨origin, cache⟩ := record
              cases cache with
              | evaluating actual =>
                  by_cases sameOwner : actual = owner
                  · cases outcomeTyped with
                    | value admitted =>
                        simp only [step, present, dif_pos sameOwner, List.mem_singleton] at member
                        subst next
                        exact ⟨heap.setKnownCache present declared (.value admitted),
                          .returned (.value admitted) restTyped⟩
                    | stableFault fault =>
                        simp only [step, present, dif_pos sameOwner, List.mem_singleton] at member
                        subst next
                        exact ⟨heap.setKnownCache present declared (.stableFault fault),
                          .returned (.stableFault fault) restTyped⟩
                    | retryableFault reason =>
                        simp only [step, present, dif_pos sameOwner, List.mem_singleton] at member
                        subst next
                        exact retryMachine_typed
                          (heap.setKnownCache present declared .suspended) restTyped _ _ _ _ _ _
                  · simp only [step, present, dif_neg sameOwner, List.mem_singleton] at member
                    subst next
                    exact retryMachine_typed heap restTyped _ _ _ _ _ _
              | suspended | value _ | stableFault _ =>
                  simp only [step, present, List.mem_singleton] at member
                  subst next
                  exact retryMachine_typed heap restTyped _ _ _ _ _ _

/-- The heap and control premises are supplied at the start, not assumed at
every subsequent step. The final cell assignment extends the initial one. -/
theorem steps_preservation
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : Tm Head m} {length : Nat}
    {initial final : NeedMachine Head Operation Effect StableFault NativeFault m}
    (execution : Steps (spec primitive) length initial final)
    (typed : MachineTyping R signature Δ types initial A) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ MachineTyping R signature Δ finalTypes final A := by
  induction execution generalizing types with
  | refl => exact ⟨types, StoreExtends.refl types, typed⟩
  | cons successor _ ih =>
      obtain ⟨nextTypes, extension, nextTyped⟩ := step_preservation sound typed (successor.mem _)
      obtain ⟨finalTypes, restExtension, finalTyped⟩ := ih nextTyped
      exact ⟨finalTypes, extension.trans restExtension, finalTyped⟩

/-- A frontier retains its qualification even when fuel runs out or a halted
state is carried forward. No termination or successful-value premise is used. -/
theorem runFrontier_preservation
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : Tm Head m}
    (fuel : Nat) {states : List (NeedMachine Head Operation Effect StableFault NativeFault m)}
    (qualified : ∀ machine ∈ states,
      ∃ currentTypes, StoreExtends types currentTypes ∧
        MachineTyping R signature Δ currentTypes machine A)
    {final : NeedMachine Head Operation Effect StableFault NativeFault m}
    (member : final ∈ runFrontier (spec primitive) fuel states) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ MachineTyping R signature Δ finalTypes final A := by
  induction fuel generalizing states final with
  | zero => exact qualified final member
  | succ fuel ih =>
      by_cases stopped : states.all isHalted
      · simp only [runFrontier, stopped, ↓reduceIte] at member
        exact qualified final member
      · simp only [runFrontier, stopped, Bool.false_eq_true, ↓reduceIte] at member
        apply ih (states := states.flatMap (advance (spec primitive))) _ member
        intro next nextMember
        obtain ⟨previous, previousMember, advanced⟩ := List.mem_flatMap.mp nextMember
        obtain ⟨previousTypes, priorExtension, previousTyped⟩ := qualified previous previousMember
        cases stepEq : step (spec primitive) previous with
        | nil =>
            simp only [advance, stepEq, List.mem_singleton] at advanced
            subst next
            exact ⟨previousTypes, priorExtension, previousTyped⟩
        | cons head tail =>
            have stepped : next ∈ step (spec primitive) previous := by
              simpa only [advance, stepEq] using advanced
            obtain ⟨nextTypes, extension, nextTyped⟩ := step_preservation sound previousTyped stepped
            exact ⟨nextTypes, priorExtension.trans extension, nextTyped⟩

theorem MachineTyping.haltedOutcome {types : CellTypes Head m} {A : Tm Head m}
    {machine : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types machine A)
    {outcome : Outcome Head StableFault NativeFault m}
    (observed : haltedOutcome machine = some outcome) : OutcomeTyping R Δ A outcome := by
  rcases machine with ⟨world, state, work⟩
  obtain ⟨heap, control⟩ := typed
  change ControlTyping R signature Δ types state A at control
  cases control with
  | halted admitted =>
      exact (Option.some.inj observed) ▸ admitted
  | force _ _ | run _ _ | returned _ _ => cases observed

/-- Every actually observed answer is qualified from initial typing and
primitive soundness. Fault constructors do not provide native proof terms. -/
theorem answers_typing
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : Tm Head m}
    {initial : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types initial A)
    {fuel : Nat} {outcome : Outcome Head StableFault NativeFault m}
    (member : outcome ∈ answers (spec primitive) fuel initial) : OutcomeTyping R Δ A outcome := by
  obtain ⟨final, inFrontier, observed⟩ := List.mem_filterMap.mp member
  have qualified : ∀ machine ∈ [initial],
      ∃ currentTypes, StoreExtends types currentTypes ∧
        MachineTyping R signature Δ currentTypes machine A := by
    intro machine membership
    cases List.mem_singleton.mp membership
    exact ⟨types, StoreExtends.refl types, typed⟩
  obtain ⟨finalTypes, _, finalTyped⟩ := runFrontier_preservation sound fuel qualified inFrontier
  exact finalTyped.haltedOutcome observed

theorem answers_value_judgment
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    (context : FormationSensitive.ContextFormation R Δ)
    {types : CellTypes Head m} {A value : Tm Head m}
    {initial : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types initial A)
    {fuel : Nat} (member : Produced.value value ∈ answers (spec primitive) fuel initial) :
    FormationSensitive.Judgment R Δ value A := by
  have admitted := answers_typing sound typed member
  cases admitted with
  | value valueTyped => exact ⟨context, valueTyped⟩

/-- Loading an independently typed source with no external need references
establishes the machine invariant over an empty heap. Native variables are
interpreted by the supplied typed captured environment. -/
theorem source_initial_typing {n : Nat} {Γ : Ctx Head n}
    {code : ScopedNeedComputation.Code Head Operation Effect n 0} {A : Tm Head n}
    {values : Sub Head n m}
    (source : ScopedNeedComputation.Typing R signature Γ Fin.elim0 code A)
    (environment : FormationSensitive.CtxMor R Γ Δ values)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (empty : world.heap = Heap.empty) (work : Work := {}) :
    MachineTyping R signature Δ (fun _ => none)
      { world := world
        control := .run (.evaluate ⟨n, 0, code, values, Fin.elim0⟩ .done) []
        work := work }
      (subst values A) := by
  constructor
  · simpa only [empty] using (HeapTyping.empty (R := R) (signature := signature) (Δ := Δ)
      (Effect := Effect) (StableFault := StableFault))
  · exact .run (.evaluate (.captured source environment (fun index => Fin.elim0 index))
      (.done _)) (.nil _)

#print axioms StackTyping.extend
#print axioms ControlTyping.extend
#print axioms step_preservation
#print axioms steps_preservation
#print axioms runFrontier_preservation
#print axioms answers_typing
#print axioms answers_value_judgment
#print axioms source_initial_typing

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
