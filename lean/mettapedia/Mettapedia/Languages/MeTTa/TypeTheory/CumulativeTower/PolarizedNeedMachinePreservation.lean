import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachineLocalTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachineHeapTyping

/-!
# Whole-control preservation for the first-class Need candidate

Independent source and lexical-environment typing qualify the actual candidate
machine. Fresh allocation extends cell declarations; old declarations retain
their exact computation types. Cached functions and captured values are
transported through the enlarged store rather than treated as native terms.

Silent local transitions and the unchanged ownership/commit protocol preserve
the same final computation type. Native-tagged failures and protocol-shaped
retry reasons remain distinct from administrative polarity faults, which typed
outcomes exclude. Retry qualification classifies reason shapes, not the event
that produced them. This theorem asserts neither normalization nor independent
source adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedMachine

open PrimeNeedReference
open PolarizedNeed (CTy Computation)
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

/-- A commit preserves its cell's declared result type. A consumer may change
the result type only through its independently qualified resume protocol. -/
inductive StackTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    List (Frame (Resume Head Operation Effect m)) → CTy Head m → CTy Head m → Prop where
  | nil (A : CTy Head m) : StackTyping R signature Δ types [] A A
  | commit {cell : CellId} {owner : EvaluatorId}
      {rest : List (Frame (Resume Head Operation Effect m))} {A B : CTy Head m} :
      types cell = some A → StackTyping R signature Δ types rest A B →
      StackTyping R signature Δ types (.commit cell owner :: rest) A B
  | resume {token : Resume Head Operation Effect m}
      {rest : List (Frame (Resume Head Operation Effect m))} {A B C : CTy Head m} :
      DemandTyping R signature Δ types token A B →
      StackTyping R signature Δ types rest B C →
      StackTyping R signature Δ types (.resume token :: rest) A C

theorem StackTyping.extend {before after : CellTypes Head m}
    {stack : List (Frame (Resume Head Operation Effect m))} {A B : CTy Head m}
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
      (Resume Head Operation Effect m) (Answer Head Operation Effect m) StableFault (Fault NativeFault) →
        CTy Head m → Prop where
  | force {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
      {A B : CTy Head m} :
      types cell = some A → StackTyping R signature Δ types stack A B →
      ControlTyping R signature Δ types (.force cell stack) B
  | run {state : Local Head Operation Effect StableFault NativeFault m}
      {stack : List (Frame (Resume Head Operation Effect m))} {A B : CTy Head m} :
      LocalTyping R signature Δ types state A → StackTyping R signature Δ types stack A B →
      ControlTyping R signature Δ types (.run state stack) B
  | returned {outcome : Outcome Head Operation Effect StableFault NativeFault m}
      {stack : List (Frame (Resume Head Operation Effect m))} {A B : CTy Head m} :
      OutcomeTyping R signature Δ types A outcome → StackTyping R signature Δ types stack A B →
      ControlTyping R signature Δ types (.returned outcome stack) B
  | halted {outcome : Outcome Head Operation Effect StableFault NativeFault m} {A : CTy Head m} :
      OutcomeTyping R signature Δ types A outcome → ControlTyping R signature Δ types (.halted outcome) A

theorem ControlTyping.extend {before after : CellTypes Head m}
    {control : Control (Local Head Operation Effect StableFault NativeFault m)
      (Resume Head Operation Effect m) (Answer Head Operation Effect m) StableFault (Fault NativeFault)}
    {A : CTy Head m} (typed : ControlTyping R signature Δ before control A)
    (extension : StoreExtends before after) : ControlTyping R signature Δ after control A := by
  cases typed with
  | force declared stack => exact .force (extension _ _ declared) (stack.extend extension)
  | run stateTyped stack => exact .run (stateTyped.extend extension) (stack.extend extension)
  | returned outcome stack => exact .returned (outcome.extend extension) (stack.extend extension)
  | halted outcome => exact .halted (outcome.extend extension)

structure MachineTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (A : CTy Head m) : Prop where
  heap : HeapTyping R signature Δ types machine.world.heap
  control : ControlTyping R signature Δ types machine.control A

private theorem retryMachine_typed
    {machine : NeedMachine Head Operation Effect StableFault NativeFault m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {types : CellTypes Head m} {A B : CTy Head m}
    (heap : HeapTyping R signature Δ types world.heap)
    {stack : List (Frame (Resume Head Operation Effect m))}
    (typed : StackTyping R signature Δ types stack A B)
    (cell : CellId) (reason : RetryReason (Fault NativeFault)) (allowed : RetryTyping reason)
    (lookups updates receipts allocations : Nat) :
    MachineTyping R signature Δ types
      (retryMachine machine world cell reason stack lookups updates receipts allocations) B :=
  ⟨heap, .returned (.retryableFault reason allowed) typed⟩

private theorem branchAlternatives_preservation
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    {base : NeedWorld Head Operation Effect StableFault NativeFault m}
    {types : CellTypes Head m} {A B : CTy Head m}
    (heap : HeapTyping R signature Δ types base.heap)
    (cell : CellId) (record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault)
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

/-- Every actual successor preserves the independently assigned final computation
type. Only fresh allocation extends the proof-side cell assignment. -/
theorem step_preservation
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m}
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types machine A)
    (member : next ∈ PrimeNeedLocalSteps.step (extension primitive) machine) :
    ∃ nextTypes, StoreExtends types nextTypes ∧ MachineTyping R signature Δ nextTypes next A := by
  rcases machine with ⟨world, control, work⟩
  obtain ⟨heap, controlTyped⟩ := typed
  change HeapTyping R signature Δ types world.heap at heap
  change ControlTyping R signature Δ types control A at controlTyped
  cases controlTyped with
  | halted outcome => simp [PrimeNeedLocalSteps.step, step] at member
  | force declared stackTyped =>
      rename_i cell stack B
      refine ⟨types, StoreExtends.refl types, ?_⟩
      cases present : world.heap.lookup cell with
      | none =>
          simp only [PrimeNeedLocalSteps.step, step, present, List.mem_singleton] at member
          subst next
          exact retryMachine_typed heap stackTyped _ _ (by constructor) _ _ _ _
      | some record =>
          obtain ⟨originTyped, cacheTyped⟩ := heap.lookup_typed declared present
          obtain ⟨origin, cache⟩ := record
          cases cache with
          | suspended =>
              cases choices : alternatives (StableFault := StableFault) (NativeFault := NativeFault) origin with
              | nil =>
                  simp only [PrimeNeedLocalSteps.step, extension, step, reference, present, choices, List.mem_singleton] at member
                  subst next
                  exact ⟨heap, .returned (.retryableFault (.noRule cell) (.noRule cell)) stackTyped⟩
              | cons head tail =>
                  simp only [PrimeNeedLocalSteps.step, extension, step, reference, present, choices] at member
                  exact branchAlternatives_preservation _
                    (base := { world with nextEvaluator := world.nextEvaluator + 1 })
                    heap cell ⟨origin, .suspended⟩ present declared world.nextEvaluator stackTyped
                    0 (head :: tail) (fun choice membership => originTyped.alternatives
                      (by simpa only [choices] using membership)) member
          | evaluating owner =>
              simp only [PrimeNeedLocalSteps.step, step, present, List.mem_singleton] at member
              subst next
              exact retryMachine_typed heap stackTyped _ _ (by constructor) _ _ _ _
          | value value =>
              simp only [PrimeNeedLocalSteps.step, step, present, List.mem_singleton] at member
              subst next
              cases cacheTyped with
              | value admitted => exact ⟨heap, .returned (.value admitted) stackTyped⟩
          | stableFault fault =>
              simp only [PrimeNeedLocalSteps.step, step, present, List.mem_singleton] at member
              subst next
              exact ⟨heap, .returned (.stableFault fault) stackTyped⟩
  | run stateTyped stackTyped =>
      rename_i state stack B
      cases localEq : localStep state with
      | some nextLocal =>
          simp only [PrimeNeedLocalSteps.step, extension, localEq, List.mem_singleton] at member
          subst next
          exact ⟨types, StoreExtends.refl types, heap,
            .run (stateTyped.localStep sound localEq) stackTyped⟩
      | none =>
          have actionTyped := stateTyped.action sound localEq
          cases actionEq : action primitive state with
          | done outcome =>
              rw [actionEq] at actionTyped
              cases actionTyped with
              | done admitted =>
                  simp only [PrimeNeedLocalSteps.step, extension, localEq, step, reference, actionEq, List.mem_singleton] at member
                  subst next
                  exact ⟨types, StoreExtends.refl types, heap, .returned admitted stackTyped⟩
          | demand cell resume =>
              rw [actionEq] at actionTyped
              cases actionTyped with
              | demand declared demandTyped =>
                  simp only [PrimeNeedLocalSteps.step, extension, localEq, step, reference, actionEq, List.mem_singleton] at member
                  subst next
                  exact ⟨types, StoreExtends.refl types, heap,
                    .force declared (.resume demandTyped stackTyped)⟩
          | allocate origin resume =>
              rw [actionEq] at actionTyped
              cases actionTyped with
              | allocate originTyped resumeTyped =>
                  cases allocated : world.allocate? origin with
                  | none =>
                      simp only [PrimeNeedLocalSteps.step, extension, localEq, step, reference, actionEq, allocated, List.mem_singleton] at member
                      subst next
                      exact ⟨types, StoreExtends.refl types,
                        retryMachine_typed heap stackTyped _ _ (by constructor) _ _ _ _⟩
                  | some result =>
                      obtain ⟨nextWorld, cell⟩ := result
                      simp only [PrimeNeedLocalSteps.step, extension, localEq, step, reference, actionEq, allocated, List.mem_singleton] at member
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
                  simp only [PrimeNeedLocalSteps.step, extension, localEq, step, reference, actionEq, List.mem_singleton] at member
                  subst next
                  exact ⟨types, StoreExtends.refl types, heap, .run nextTyped stackTyped⟩
  | returned outcomeTyped stackTyped =>
      rename_i outcome stack B
      refine ⟨types, StoreExtends.refl types, ?_⟩
      cases stackTyped with
      | nil =>
          simp only [PrimeNeedLocalSteps.step, step, List.mem_singleton] at member
          subst next
          exact ⟨heap, .halted outcomeTyped⟩
      | resume demandTyped restTyped =>
          simp only [PrimeNeedLocalSteps.step, step, List.mem_singleton] at member
          subst next
          exact ⟨heap, .run (demandTyped.afterDemand outcomeTyped) restTyped⟩
      | commit declared restTyped =>
          rename_i cell owner rest
          cases present : world.heap.lookup cell with
          | none =>
              simp only [PrimeNeedLocalSteps.step, step, present, List.mem_singleton] at member
              subst next
              exact retryMachine_typed heap restTyped _ _ (by constructor) _ _ _ _
          | some record =>
              obtain ⟨origin, cache⟩ := record
              cases cache with
              | evaluating actual =>
                  by_cases sameOwner : actual = owner
                  · cases outcomeTyped with
                    | value admitted =>
                        simp only [PrimeNeedLocalSteps.step, step, present, dif_pos sameOwner, List.mem_singleton] at member
                        subst next
                        exact ⟨heap.setKnownCache present declared (.value admitted),
                          .returned (.value admitted) restTyped⟩
                    | stableFault fault =>
                        simp only [PrimeNeedLocalSteps.step, step, present, dif_pos sameOwner, List.mem_singleton] at member
                        subst next
                        exact ⟨heap.setKnownCache present declared (.stableFault fault),
                          .returned (.stableFault fault) restTyped⟩
                    | retryableFault reason allowed =>
                        simp only [PrimeNeedLocalSteps.step, step, present, dif_pos sameOwner, List.mem_singleton] at member
                        subst next
                        exact retryMachine_typed
                          (heap.setKnownCache present declared .suspended) restTyped _ _ allowed _ _ _ _
                  · simp only [PrimeNeedLocalSteps.step, step, present, dif_neg sameOwner, List.mem_singleton] at member
                    subst next
                    exact retryMachine_typed heap restTyped _ _ (by constructor) _ _ _ _
              | suspended | value _ | stableFault _ =>
                  simp only [PrimeNeedLocalSteps.step, step, present, List.mem_singleton] at member
                  subst next
                  exact retryMachine_typed heap restTyped _ _ (by constructor) _ _ _ _

/-- Bounded evaluation preserves independent heap and control typing even
when the frontier remains unfinished. A returned closure may need the final
enlarged cell assignment, rather than only the initial one. -/
theorem runFrontier_preservation
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m}
    (fuel : Nat) {states : List (NeedMachine Head Operation Effect StableFault NativeFault m)}
    (qualified : ∀ machine ∈ states,
      ∃ currentTypes, StoreExtends types currentTypes ∧
        MachineTyping R signature Δ currentTypes machine A)
    {final : NeedMachine Head Operation Effect StableFault NativeFault m}
    (member : final ∈ PrimeNeedLocalSteps.runFrontier (extension primitive) fuel states) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ MachineTyping R signature Δ finalTypes final A := by
  induction fuel generalizing states final with
  | zero => exact qualified final member
  | succ fuel ih =>
      by_cases stopped : states.all isHalted
      · simp only [PrimeNeedLocalSteps.runFrontier, stopped, ↓reduceIte] at member
        exact qualified final member
      · simp only [PrimeNeedLocalSteps.runFrontier, stopped, Bool.false_eq_true, ↓reduceIte] at member
        apply ih (states := states.flatMap (PrimeNeedLocalSteps.advance (extension primitive))) _ member
        intro next nextMember
        obtain ⟨previous, previousMember, advanced⟩ := List.mem_flatMap.mp nextMember
        obtain ⟨previousTypes, priorExtension, previousTyped⟩ := qualified previous previousMember
        cases stepEq : PrimeNeedLocalSteps.step (extension primitive) previous with
        | nil =>
            simp only [PrimeNeedLocalSteps.advance, stepEq, List.mem_singleton] at advanced
            subst next
            exact ⟨previousTypes, priorExtension, previousTyped⟩
        | cons head tail =>
            have stepped : next ∈ PrimeNeedLocalSteps.step (extension primitive) previous := by
              simpa only [PrimeNeedLocalSteps.advance, stepEq] using advanced
            obtain ⟨nextTypes, grows, nextTyped⟩ := step_preservation sound previousTyped stepped
            exact ⟨nextTypes, priorExtension.trans grows, nextTyped⟩

theorem MachineTyping.haltedOutcome {types : CellTypes Head m} {A : CTy Head m}
    {machine : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types machine A)
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (observed : haltedOutcome machine = some outcome) :
    OutcomeTyping R signature Δ types A outcome := by
  rcases machine with ⟨world, state, work⟩
  obtain ⟨heap, control⟩ := typed
  change ControlTyping R signature Δ types state A at control
  cases control with
  | halted admitted => exact (Option.some.inj observed) ▸ admitted
  | force _ _ | run _ _ | returned _ _ => cases observed

/-- A returned closure's captured cells remain supported by the actual final
heap. This witness retains the machine discarded by the answer-only observer;
an existential cell declaration alone is not a reusable runtime environment. -/
theorem answers_with_state
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m}
    {initial : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types initial A)
    {fuel : Nat} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (member : outcome ∈ PrimeNeedLocalSteps.answers (extension primitive) fuel initial) :
    ∃ finalTypes final,
      final ∈ PrimeNeedLocalSteps.runFrontier (extension primitive) fuel [initial] ∧
      haltedOutcome final = some outcome ∧ StoreExtends types finalTypes ∧
      MachineTyping R signature Δ finalTypes final A := by
  obtain ⟨final, inFrontier, observed⟩ := List.mem_filterMap.mp member
  have qualified : ∀ machine ∈ [initial],
      ∃ currentTypes, StoreExtends types currentTypes ∧
        MachineTyping R signature Δ currentTypes machine A := by
    intro machine membership
    cases List.mem_singleton.mp membership
    exact ⟨types, StoreExtends.refl types, typed⟩
  obtain ⟨finalTypes, grows, finalTyped⟩ := runFrontier_preservation sound fuel qualified inFrontier
  exact ⟨finalTypes, final, inFrontier, observed, grows, finalTyped⟩

/-- Qualification is derived from the initial machine and actual bounded
execution; no typing invariant at intermediate states is an input. For
subsequent execution of a returned closure, use the retained final machine
in `answers_with_state`, rather than this answer-only type projection. -/
theorem answers_typing
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m}
    {initial : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types initial A)
    {fuel : Nat} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (member : outcome ∈ PrimeNeedLocalSteps.answers (extension primitive) fuel initial) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ OutcomeTyping R signature Δ finalTypes A outcome := by
  obtain ⟨finalTypes, final, _, observed, grows, finalTyped⟩ :=
    answers_with_state sound typed member
  exact ⟨finalTypes, grows, finalTyped.haltedOutcome observed⟩

/-- A typing-qualified run cannot produce an administrative thunk-polarity
fault. Primitive native faults and protocol retry reasons remain permitted. -/
theorem answers_no_expectedThunk
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m}
    {initial : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types initial A) (fuel : Nat) :
    .retryableFault (.domain .expectedThunk) ∉
      PrimeNeedLocalSteps.answers (extension primitive) fuel initial := by
  intro member
  obtain ⟨_, _, admitted⟩ := answers_typing sound typed member
  cases admitted with
  | retryableFault _ allowed => cases allowed

/-- Every domain fault from a qualified run comes from the native primitive
fault carrier, never from a source value/computation-polarity mismatch. -/
theorem answers_domain_fault_native
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m}
    {initial : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types initial A)
    {fuel : Nat} {fault : Fault NativeFault}
    (member : .retryableFault (.domain fault) ∈
      PrimeNeedLocalSteps.answers (extension primitive) fuel initial) :
    ∃ native, fault = .native native := by
  obtain ⟨_, _, admitted⟩ := answers_typing sound typed member
  cases admitted with
  | retryableFault _ allowed => exact (RetryTyping.domain_iff_native fault).mp allowed

/-- A native mathematical result is admitted through the independent source
and environment invariant, not from successful evaluation alone. -/
theorem answers_value_judgment
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive)
    (context : FormationSensitive.ContextFormation R Δ)
    {types : CellTypes Head m} {A value : Tm Head m}
    {initial : NeedMachine Head Operation Effect StableFault NativeFault m}
    (typed : MachineTyping R signature Δ types initial (.returns (.native A)))
    {fuel : Nat} (member : .value (.returned (.native value)) ∈
      PrimeNeedLocalSteps.answers (extension primitive) fuel initial) :
    FormationSensitive.Judgment R Δ value A := by
  obtain ⟨_, _, admitted⟩ := answers_typing sound typed member
  cases admitted with
  | value answer =>
      cases answer with
      | returned valueTyped => exact ⟨context, valueTyped.native_admitted⟩

/-- Initial loading checks every captured value independently. The runtime
stores only raw code/environments; no proof-bearing answer constructor is
used to make execution pass. -/
theorem source_initial_typing {n v : Nat} {Γ : Ctx Head n}
    {sv : Fin v → PolarizedNeed.VTy Head n}
    {code : Computation Head Operation Effect n v 0} {B : CTy Head n}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
    (source : PolarizedNeed.ComputationTyping R signature Γ sv Fin.elim0 code B)
    (environment : EnvironmentTyping R signature Γ sv Fin.elim0 Δ
      (fun _ => none) native values Fin.elim0)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (empty : world.heap = Heap.empty) (work : Work := {}) :
    MachineTyping R signature Δ (fun _ => none)
      { world := world
        control := .run (.evaluate ⟨n, v, 0, code, native, values, Fin.elim0⟩ .done) []
        work := work }
      (B.substitute native) := by
  constructor
  · simpa only [empty] using (HeapTyping.empty (R := R) (signature := signature) (Δ := Δ)
      (Effect := Effect) (StableFault := StableFault))
  · exact .run (.evaluate (.captured source environment) (.done _)) (.nil _)

theorem source_closed_initial_typing {n : Nat} {Γ : Ctx Head n}
    {code : Computation Head Operation Effect n 0 0} {B : CTy Head n}
    {native : Sub Head n m}
    (source : PolarizedNeed.ComputationTyping R signature Γ Fin.elim0 Fin.elim0 code B)
    (environment : FormationSensitive.CtxMor R Γ Δ native)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (empty : world.heap = Heap.empty) (work : Work := {}) :
    MachineTyping R signature Δ (fun _ => none)
      { world := world
        control := .run (.evaluate ⟨n, 0, 0, code, native, Fin.elim0, Fin.elim0⟩ .done) []
        work := work }
      (B.substitute native) :=
  source_initial_typing source ⟨environment, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    world empty work

#print axioms StackTyping.extend
#print axioms ControlTyping.extend
#print axioms step_preservation
#print axioms runFrontier_preservation
#print axioms answers_with_state
#print axioms answers_typing
#print axioms answers_no_expectedThunk
#print axioms answers_domain_fault_native
#print axioms answers_value_judgment
#print axioms source_initial_typing
#print axioms source_closed_initial_typing

end PolarizedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
