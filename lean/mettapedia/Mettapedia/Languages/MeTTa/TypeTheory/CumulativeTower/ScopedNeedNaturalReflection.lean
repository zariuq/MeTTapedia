import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedNaturalMachineLaws

/-!
# Reflecting completed owned-machine runs into source evaluation

The proof interprets existing consumer continuations using the independent
natural source judgments. It then reconstructs that interpretation backwards
through actual transitions. The interpretation contains no machine execution
premise, and retains the full source world, including cache and receipts.
Neither source typing nor a derivation of the initial computation is assumed.
The conclusion concerns completed finite paths. It does not count derivations
or identify source observations with the machine's work counters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedNaturalSemantics
namespace Reflection

open PrimeNeedReference ScopedNeedMachine
open ScopedNeedComputation (Code)

variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}

def EvalMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (closure : Closure Head Operation Effect m) (kont : Kont Head m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  ∃ raw, Nonempty (Eval primitive closure world raw final) ∧ finish raw kont = outcome

def ResumeMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (resume : Resume Head Operation Effect m)
    (input : Outcome Head StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  match resume, input with
  | .finish kont, input => finish input kont = outcome ∧ world = final
  | .bindValue body kont, .value value =>
      EvalMeaning primitive (body.open value) kont world outcome final
  | .bindSigma body kont, .value value =>
      ∃ raw, Nonempty (Eval primitive (body.open value) world raw final) ∧
        finish (pairOutcome value raw) kont = outcome
  | .bindValue _ _, .stableFault fault | .bindSigma _ _, .stableFault fault =>
      outcome = .stableFault fault ∧ world = final
  | .bindValue _ _, .retryableFault reason | .bindSigma _ _, .retryableFault reason =>
      outcome = .retryableFault reason ∧ world = final
  | .bindNeed _ _, _ =>
      outcome = .retryableFault (.domain .allocationResumeDemanded) ∧ world = final

def LocalMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (state : Local Head Operation Effect StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  match state with
  | .evaluate closure kont => EvalMeaning primitive closure kont world outcome final
  | .demand cell resume =>
      ∃ input selected, Nonempty (Force primitive cell world input selected) ∧
        ResumeMeaning primitive resume input selected outcome final
  | .complete result => result = outcome ∧ world = final

def StackMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    List (Frame (Resume Head Operation Effect m)) →
      Outcome Head StableFault NativeFault m →
      NeedWorld Head Operation Effect StableFault NativeFault m →
      Outcome Head StableFault NativeFault m →
      NeedWorld Head Operation Effect StableFault NativeFault m → Prop
  | [], input, world, outcome, final => input = outcome ∧ world = final
  | .commit cell owner :: rest, input, world, outcome, final =>
      StackMeaning primitive rest (finalize world cell owner input).1
        (finalize world cell owner input).2 outcome final
  | .resume token :: rest, input, world, outcome, final =>
      ∃ result selected, ResumeMeaning primitive token input world result selected ∧
        StackMeaning primitive rest result selected outcome final

def ControlMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (control : NeedControl Head Operation Effect StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  match control with
  | .run state stack =>
      ∃ result selected, LocalMeaning primitive state world result selected ∧
        StackMeaning primitive stack result selected outcome final
  | .force cell stack =>
      ∃ result selected, Nonempty (Force primitive cell world result selected) ∧
        StackMeaning primitive stack result selected outcome final
  | .returned result stack => StackMeaning primitive stack result world outcome final
  | .halted result => result = outcome ∧ world = final

theorem finish_pair (first : Tm Head m) (input : Outcome Head StableFault NativeFault m)
    (kont : Kont Head m) :
    finish input (.pair first kont) = finish (pairOutcome first input) kont := by
  cases input <;> simp only [finish, pairOutcome, finish_stableFault, finish_retryableFault]

theorem afterDemand_meaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (resume : Resume Head Operation Effect m) (input : Outcome Head StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) :
    LocalMeaning primitive (afterDemand resume input) world outcome final ↔
      ResumeMeaning primitive resume input world outcome final := by
  cases resume <;> cases input <;>
    simp only [afterDemand, LocalMeaning, ResumeMeaning, EvalMeaning, finish_pair, eq_comm]

theorem sequence_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {first : Code Head Operation Effect n k} {body : Code Head Operation Effect (n + 1) k}
    {values : Sub Head n m} {needs : Fin k → CellId} {kont : Kont Head m}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell))
    (meaning : LocalMeaning primitive
      (.demand cell (.bindValue ⟨n, k, body, values, needs⟩ kont)) allocated outcome final) :
    EvalMeaning primitive ⟨n, k, .sequence first body, values, needs⟩ kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨forced⟩, resumed⟩
  cases input with
  | value value =>
      rcases resumed with ⟨raw, ⟨evaluated⟩, result⟩
      exact ⟨raw, ⟨.sequenceValue allocation forced evaluated⟩, result⟩
  | stableFault fault =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨.stableFault fault, ⟨.sequenceStable body allocation forced⟩, finish_stableFault _ _⟩
  | retryableFault reason =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨.retryableFault reason, ⟨.sequenceRetry body allocation forced⟩, finish_retryableFault _ _⟩

theorem sequenceSigma_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {first : Code Head Operation Effect n k} {body : Code Head Operation Effect (n + 1) k}
    {values : Sub Head n m} {needs : Fin k → CellId} {kont : Kont Head m}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell))
    (meaning : LocalMeaning primitive
      (.demand cell (.bindSigma ⟨n, k, body, values, needs⟩ kont)) allocated outcome final) :
    EvalMeaning primitive ⟨n, k, .sequenceSigma first body, values, needs⟩ kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨forced⟩, resumed⟩
  cases input with
  | value value =>
      rcases resumed with ⟨raw, ⟨evaluated⟩, result⟩
      exact ⟨pairOutcome value raw, ⟨.sequenceSigmaValue allocation forced evaluated⟩, result⟩
  | stableFault fault =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨.stableFault fault, ⟨.sequenceSigmaStable body allocation forced⟩, finish_stableFault _ _⟩
  | retryableFault reason =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨.retryableFault reason, ⟨.sequenceSigmaRetry body allocation forced⟩, finish_retryableFault _ _⟩

theorem choose_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (left right : Code Head Operation Effect n k)
    {values : Sub Head n m} {needs : Fin k → CellId} {kont : Kont Head m}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, k, .choose left right, values, needs⟩ = some (allocated, cell))
    (meaning : LocalMeaning primitive (.demand cell (.finish kont)) allocated outcome final) :
    EvalMeaning primitive ⟨n, k, .choose left right, values, needs⟩ kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨forced⟩, result, rfl⟩
  exact ⟨input, ⟨.choose left right allocation forced⟩, result⟩

theorem evaluate_step_backward
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) (work : Work)
    (closure : Closure Head Operation Effect m) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (member : next ∈ step (spec primitive) ⟨world, .run (.evaluate closure kont) stack, work⟩)
    (meaning : ControlMeaning primitive next.control next.world outcome final) :
    ControlMeaning primitive (.run (.evaluate closure kont) stack) world outcome final := by
  rcases closure with ⟨n, k, code, values, needs⟩
  cases code with
  | returnValue term =>
      simp only [step, spec, action, List.mem_singleton] at member
      subst next
      exact ⟨_, world, ⟨_, ⟨.returnValue term values needs world⟩, rfl⟩, meaning⟩
  | call operation argument =>
      simp only [step, spec, action, List.mem_singleton] at member
      subst next
      exact ⟨_, world, ⟨_, ⟨.call operation argument values needs world⟩, rfl⟩, meaning⟩
  | emit effect body =>
      simp only [step, spec, action, List.mem_singleton] at member
      subst next
      rcases meaning with ⟨result, selected, ⟨raw, ⟨evaluated⟩, completed⟩, remaining⟩
      exact ⟨result, selected, ⟨raw, ⟨.emit effect evaluated⟩, completed⟩, remaining⟩
  | force reference =>
      simp only [step, spec, action, List.mem_singleton] at member
      subst next
      rcases meaning with ⟨input, selected, ⟨forced⟩, result, completed, resumed, remaining⟩
      rcases resumed with ⟨finished, rfl⟩
      exact ⟨result, selected, ⟨input, ⟨.force reference forced⟩, finished⟩, remaining⟩
  | sequence first body =>
      cases allocation : world.allocate? ⟨n, k, first, values, needs⟩ with
      | none =>
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          refine ⟨_, _, ?_, meaning⟩
          exact ⟨_, ⟨.sequenceAllocationFailure body allocation⟩, finish_retryableFault _ _⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, demanded, remaining⟩
          exact ⟨result, selected, sequence_meaning allocation demanded, remaining⟩
  | sequenceSigma first body =>
      cases allocation : world.allocate? ⟨n, k, first, values, needs⟩ with
      | none =>
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          refine ⟨_, _, ?_, meaning⟩
          exact ⟨_, ⟨.sequenceSigmaAllocationFailure body allocation⟩, finish_retryableFault _ _⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, demanded, remaining⟩
          exact ⟨result, selected, sequenceSigma_meaning allocation demanded, remaining⟩
  | choose left right =>
      cases allocation : world.allocate? ⟨n, k, .choose left right, values, needs⟩ with
      | none =>
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          refine ⟨_, _, ?_, meaning⟩
          exact ⟨_, ⟨.chooseAllocationFailure left right allocation⟩, finish_retryableFault _ _⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, demanded, remaining⟩
          exact ⟨result, selected, choose_meaning left right allocation demanded, remaining⟩
  | letNeed suspended body =>
      cases allocation : world.allocate? ⟨n, k, suspended, values, needs⟩ with
      | none =>
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          refine ⟨_, _, ?_, meaning⟩
          exact ⟨_, ⟨.letNeedAllocationFailure body allocation⟩, finish_retryableFault _ _⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, spec, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, ⟨raw, ⟨evaluated⟩, completed⟩, remaining⟩
          exact ⟨result, selected, ⟨raw, ⟨.letNeed allocation evaluated⟩, completed⟩, remaining⟩

theorem force_step_backward
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) (work : Work)
    (cell : CellId) (stack : List (Frame (Resume Head Operation Effect m)))
    {next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (member : next ∈ step (spec primitive) ⟨world, .force cell stack, work⟩)
    (meaning : ControlMeaning primitive next.control next.world outcome final) :
    ControlMeaning primitive (.force cell stack) world outcome final := by
  cases present : world.heap.lookup cell with
  | none =>
      simp only [step, present, List.mem_singleton] at member
      subst next
      exact ⟨_, _, ⟨.missing present⟩, meaning⟩
  | some record =>
      rcases record with ⟨origin, cache⟩
      cases cache with
      | value value =>
          simp only [step, present, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨.cachedValue present⟩, meaning⟩
      | stableFault fault =>
          simp only [step, present, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨.cachedStable present⟩, meaning⟩
      | evaluating owner =>
          simp only [step, present, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨.evaluating present⟩, meaning⟩
      | suspended =>
          rcases force_suspended_successor primitive rfl present member with
            ⟨position, rule, selected, ⟨selection⟩, entered, control⟩
          rw [control, entered] at meaning
          rcases meaning with ⟨bodyOutcome, bodyFinal, ⟨raw, ⟨evaluated⟩, completed⟩, remaining⟩
          change raw = bodyOutcome at completed
          subst bodyOutcome
          exact ⟨_, _, ⟨.suspended present selection evaluated⟩, remaining⟩

/-- Every actual transition reconstructs independent source meaning. The
worlds quantified by that meaning are semantic intermediates, not asserted
runtime invariants or supplied source derivations. -/
theorem step_backward
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (member : next ∈ step (spec primitive) machine)
    (meaning : ControlMeaning primitive next.control next.world outcome final) :
    ControlMeaning primitive machine.control machine.world outcome final := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted result => simp only [step, List.not_mem_nil] at member
  | force cell stack => exact force_step_backward primitive world work cell stack member meaning
  | run state stack =>
      cases state with
      | evaluate closure kont =>
          exact evaluate_step_backward primitive world work closure kont stack member meaning
      | complete result =>
          simp only [step, spec, action, List.mem_singleton] at member
          subst next
          exact ⟨result, world, ⟨rfl, rfl⟩, meaning⟩
      | demand cell resume =>
          simp only [step, spec, action, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨input, selected, forced, result, completed, resumed, remaining⟩
          exact ⟨result, completed, ⟨input, selected, forced, resumed⟩, remaining⟩
  | returned result stack =>
      cases stack with
      | nil =>
          simp only [step, List.mem_singleton] at member
          subst next
          exact meaning
      | cons frame rest =>
          cases frame with
          | resume token =>
              simp only [step, List.mem_singleton] at member
              subst next
              rcases meaning with ⟨result, selected, resumed, remaining⟩
              exact ⟨result, selected,
                (afterDemand_meaning primitive token _ world result selected).mp resumed, remaining⟩
          | commit cell owner =>
              obtain ⟨completed, returned⟩ := finalize_successor primitive rfl member
              rw [returned, completed] at meaning
              exact meaning

theorem steps_backward
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {length : Nat} {initial terminal : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (execution : Steps (spec primitive) length initial terminal)
    (meaning : ControlMeaning primitive terminal.control terminal.world outcome final) :
    ControlMeaning primitive initial.control initial.world outcome final := by
  induction execution with
  | refl => exact meaning
  | cons occurrence rest ih =>
      exact step_backward primitive (occurrence.mem (spec primitive)) (ih meaning)

/-- A completed actual execution supplies a natural source derivation. This
does not require a formed source, a typed heap, or a preselected branch. -/
theorem eval_of_steps
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} {length : Nat} {work finalWork : Work}
    (execution : Steps (spec primitive) length
      ⟨world, .run (.evaluate closure .done) [], work⟩ ⟨final, .halted outcome, finalWork⟩) :
    Nonempty (Eval primitive closure world outcome final) := by
  have meaning := steps_backward execution (show ControlMeaning primitive (.halted outcome) final
    outcome final from ⟨rfl, rfl⟩)
  rcases meaning with ⟨result, selected, ⟨raw, evaluated, completed⟩, rfl, rfl⟩
  simp only [finish_done] at completed
  cases completed
  exact evaluated

theorem force_of_steps
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {cell : CellId} {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} {length : Nat} {work finalWork : Work}
    (execution : Steps (spec primitive) length
      ⟨world, .force cell [], work⟩ ⟨final, .halted outcome, finalWork⟩) :
    Nonempty (Force primitive cell world outcome final) := by
  have meaning := steps_backward execution (show ControlMeaning primitive (.halted outcome) final
    outcome final from ⟨rfl, rfl⟩)
  rcases meaning with ⟨result, selected, forced, rfl, rfl⟩
  exact forced

theorem eval_of_runSegment
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (execution : RunSegment primitive world (.run (.evaluate closure .done) []) final (.halted outcome)) :
    Nonempty (Eval primitive closure world outcome final) := by
  obtain ⟨length, finalWork, path⟩ := execution {}
  exact eval_of_steps path

theorem force_of_runSegment
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {cell : CellId} {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (execution : RunSegment primitive world (.force cell []) final (.halted outcome)) :
    Nonempty (Force primitive cell world outcome final) := by
  obtain ⟨length, finalWork, path⟩ := execution {}
  exact force_of_steps path

/-- A real cached force and halt supply source evidence through reflection,
including the newly appended observation receipt. -/
theorem cached_value_reflected
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {cell : CellId} {origin : Closure Head Operation Effect m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {value : Tm Head m}
    (cached : world.heap.lookup cell = some ⟨origin, .value value⟩) :
    Nonempty (Force primitive cell world (.value value)
      (world.record (.observe cell (.value value))).1) := by
  apply force_of_steps (work := {}) (length := 2)
  exact .cons ⟨0, by simp only [step, cached, List.getElem?_cons_zero]; rfl⟩
    (.cons ⟨0, rfl⟩ (.refl _))

/-- The reflected natural cache law excludes a different machine result for
every finite path, not just a particular bounded execution. -/
theorem no_cached_other_halt
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {cell : CellId} {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {value other : Tm Head m} {length : Nat} {work finalWork : Work}
    (cached : world.heap.lookup cell = some ⟨origin, .value value⟩) (different : other ≠ value) :
    ¬ Steps (spec primitive) length ⟨world, .force cell [], work⟩
      ⟨final, .halted (.value other), finalWork⟩ := by
  intro execution
  obtain ⟨derived⟩ := force_of_steps execution
  have same := (derived.cachedValue_exact cached).1
  exact different (Produced.value.inj same)

#print axioms afterDemand_meaning
#print axioms evaluate_step_backward
#print axioms force_step_backward
#print axioms step_backward
#print axioms steps_backward
#print axioms eval_of_steps
#print axioms force_of_steps
#print axioms eval_of_runSegment
#print axioms force_of_runSegment
#print axioms cached_value_reflected
#print axioms no_cached_other_halt

end Reflection
end ScopedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
