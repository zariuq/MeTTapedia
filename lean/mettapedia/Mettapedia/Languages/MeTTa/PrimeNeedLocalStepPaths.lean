import Mettapedia.Languages.MeTTa.PrimeNeedLocalSteps

/-!
# Finite occurrence paths for the local-step Need extension

Paths use the actual extended successor list, including intercepted local
steps. Each edge retains a list position. Frontier membership and finite
completed paths agree; this existential correspondence is not a claim about
uniqueness, branch multiplicity, termination, or equality of work costs.
Extra fuel preserves completed endpoints, not arbitrary running controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeNeedLocalSteps

open PrimeNeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

structure StepOccurrence
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) where
  index : Nat
  successorAt : (step extension machine)[index]? = some next

namespace StepOccurrence

theorem mem
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (occurrence : StepOccurrence extension machine next) : next ∈ step extension machine := by
  obtain ⟨bounded, selected⟩ := List.getElem?_eq_some_iff.mp occurrence.successorAt
  exact List.mem_iff_getElem.mpr ⟨occurrence.index, bounded, selected⟩

theorem of_mem
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : next ∈ step extension machine) : Nonempty (StepOccurrence extension machine next) := by
  obtain ⟨index, bounded, selected⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨index, List.getElem?_eq_some_iff.mpr ⟨bounded, selected⟩⟩⟩

end StepOccurrence

inductive Steps
    (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat → Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → Prop where
  | refl (machine) : Steps extension 0 machine machine
  | cons {length machine next final}
      (occurrence : StepOccurrence extension machine next)
      (rest : Steps extension length next final) :
      Steps extension (Nat.succ length) machine final

variable
  (extension : Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)

theorem successor_not_halted
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : next ∈ step extension machine) : isHalted machine = false := by
  cases control : machine.control with
  | run state stack => simp only [isHalted, control]
  | force cell stack => simp only [isHalted, control]
  | returned outcome stack => simp only [isHalted, control]
  | halted outcome =>
      simp only [step_halted extension machine control, List.not_mem_nil] at member

theorem step_increments_transition
    (machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (member : next ∈ step extension machine) :
    next.work.transitions = machine.work.transitions + 1 := by
  cases control : machine.control with
  | run state stack =>
      cases selected : extension.localStep state with
      | none =>
          exact PrimeNeedReference.step_increments_transition extension.reference machine next
            (by simpa only [step, control, selected] using member)
      | some successor =>
          exact (local_successor_work extension machine control selected member).1
  | force cell stack =>
      exact PrimeNeedReference.step_increments_transition extension.reference machine next
        (by simpa only [step, control] using member)
  | returned outcome stack =>
      exact PrimeNeedReference.step_increments_transition extension.reference machine next
        (by simpa only [step, control] using member)
  | halted outcome =>
      simp only [step_halted extension machine control, List.not_mem_nil] at member

namespace Steps

theorem trans {leftLength rightLength : Nat}
    {initial middle final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (earlier : Steps extension leftLength initial middle)
    (later : Steps extension rightLength middle final) :
    Steps extension (leftLength + rightLength) initial final := by
  induction earlier with
  | refl => simpa using later
  | cons occurrence _ ih =>
      simpa only [Nat.succ_add] using Steps.cons occurrence (ih later)

theorem transitions_eq {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps extension length initial final) :
    final.work.transitions = initial.work.transitions + length := by
  induction execution with
  | refl => rfl
  | cons occurrence _ ih =>
      rw [ih, step_increments_transition extension _ _ (occurrence.mem extension)]
      omega

theorem halted_endpoint {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps extension length initial final)
    (halted : isHalted initial = true) : final = initial ∧ length = 0 := by
  cases execution with
  | refl => exact ⟨rfl, rfl⟩
  | cons occurrence _ =>
      have notHalted := successor_not_halted extension (occurrence.mem extension)
      rw [halted] at notHalted
      cases notHalted

/-- At the exact path length, the endpoint occurs in the actual ordered
frontier. Other branches need not halt or have the same length. -/
theorem mem_runFrontier {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps extension length initial final)
    {states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (initialMember : initial ∈ states) : final ∈ runFrontier extension length states := by
  induction execution generalizing states with
  | refl => exact initialMember
  | @cons length initial next final occurrence rest ih =>
      have nextMember := occurrence.mem extension
      have notHalted := successor_not_halted extension nextMember
      by_cases stopped : states.all isHalted = true
      · have halted := List.all_eq_true.mp stopped initial initialMember
        rw [notHalted] at halted
        cases halted
      · simp only [runFrontier, stopped]
        exact ih (List.mem_flatMap.mpr ⟨initial, initialMember, by
          cases successors : step extension initial with
          | nil => simp only [successors, List.not_mem_nil] at nextMember
          | cons first remaining => simpa only [advance, successors] using nextMember⟩)

end Steps

theorem halted_mem_runFrontier (fuel : Nat)
    {states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : machine ∈ states) (halted : isHalted machine = true) :
    machine ∈ runFrontier extension fuel states := by
  induction fuel generalizing states with
  | zero => exact member
  | succ fuel ih =>
      by_cases stopped : states.all isHalted = true
      · simpa only [runFrontier, stopped, ↓reduceIte] using member
      · simp only [runFrontier, stopped]
        apply ih (List.mem_flatMap.mpr ⟨machine, member, ?_⟩)
        cases control : machine.control with
        | run state stack => simp [isHalted, control] at halted
        | force cell stack => simp [isHalted, control] at halted
        | returned outcome stack => simp [isHalted, control] at halted
        | halted outcome =>
            simp only [advance, step_halted extension machine control, List.mem_singleton]

namespace Steps

/-- Extra fuel is valid here because the displayed endpoint is completed. -/
theorem mem_runFrontier_of_le {length fuel : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps extension length initial final) (bounded : length ≤ fuel)
    (halted : isHalted final = true)
    {states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (initialMember : initial ∈ states) : final ∈ runFrontier extension fuel states := by
  induction execution generalizing fuel states with
  | refl => exact halted_mem_runFrontier extension fuel initialMember halted
  | @cons length initial next final occurrence rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have nextMember := occurrence.mem extension
          have notHalted := successor_not_halted extension nextMember
          by_cases stopped : states.all isHalted = true
          · have impossible := List.all_eq_true.mp stopped initial initialMember
            rw [notHalted] at impossible
            cases impossible
          · simp only [runFrontier, stopped]
            apply ih (Nat.le_of_succ_le_succ bounded) halted
            exact List.mem_flatMap.mpr ⟨initial, initialMember, by
              cases successors : step extension initial with
              | nil => simp only [successors, List.not_mem_nil] at nextMember
              | cons first remaining => simpa only [advance, successors] using nextMember⟩

end Steps

/-- Extract an actual finite occurrence path. Retained halted or stuck
frontier entries contribute no fictitious transition. -/
theorem runFrontier_reachable {fuel : Nat}
    {states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : final ∈ runFrontier extension fuel states) :
    ∃ initial ∈ states, ∃ length ≤ fuel, Steps extension length initial final := by
  induction fuel generalizing states final with
  | zero => exact ⟨final, member, 0, Nat.le_refl 0, .refl _⟩
  | succ fuel ih =>
      by_cases stopped : states.all isHalted = true
      · simp only [runFrontier, stopped] at member
        exact ⟨final, member, 0, Nat.zero_le _, .refl _⟩
      · simp only [runFrontier, stopped] at member
        obtain ⟨middle, advanced, length, bounded, path⟩ := ih member
        obtain ⟨initial, initialMember, advancedFrom⟩ := List.mem_flatMap.mp advanced
        cases successors : step extension initial with
        | nil =>
            simp only [advance, successors, List.mem_singleton] at advancedFrom
            subst middle
            exact ⟨initial, initialMember, length,
              Nat.le_trans bounded (Nat.le_succ fuel), path⟩
        | cons first remaining =>
            have successor : middle ∈ step extension initial := by
              simpa only [advance, successors] using advancedFrom
            obtain ⟨occurrence⟩ := StepOccurrence.of_mem extension successor
            exact ⟨initial, initialMember, length + 1, Nat.succ_le_succ bounded,
              .cons occurrence path⟩

theorem answers_iff_steps (fuel : Nat)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault) :
    outcome ∈ answers extension fuel initial ↔
      ∃ length ≤ fuel, ∃ finalWorld finalWork,
        Steps extension length initial ⟨finalWorld, .halted outcome, finalWork⟩ := by
  constructor
  · intro member
    obtain ⟨final, finalMember, observation⟩ := List.mem_filterMap.mp member
    obtain ⟨source, sourceMember, length, bounded, path⟩ :=
      runFrontier_reachable extension finalMember
    simp only [List.mem_singleton] at sourceMember
    subst source
    rcases final with ⟨finalWorld, control, finalWork⟩
    cases control with
    | run state stack => cases observation
    | force cell stack => cases observation
    | returned result stack => cases observation
    | halted result =>
        simp only [haltedOutcome, Option.some.injEq] at observation
        subst result
        exact ⟨length, bounded, finalWorld, finalWork, path⟩
  · rintro ⟨length, bounded, finalWorld, finalWork, path⟩
    exact List.mem_filterMap.mpr ⟨⟨finalWorld, .halted outcome, finalWork⟩,
      path.mem_runFrontier_of_le extension bounded rfl (by simp only [List.mem_singleton]), rfl⟩

namespace Examples

theorem intercepted_answer_has_actual_path :
    ∃ length ≤ 4, ∃ finalWorld finalWork,
      Steps candidate length initial ⟨finalWorld, .halted (.value 2), finalWork⟩ := by
  apply (answers_iff_steps candidate 4 initial (.value 2)).mp
  simp only [silent_controls_reach_answer, List.mem_singleton]

theorem too_short_has_no_completed_path :
    ¬ ∃ length ≤ 2, ∃ finalWorld finalWork,
      Steps candidate length initial ⟨finalWorld, .halted (.value 2), finalWork⟩ := by
  intro execution
  have member := (answers_iff_steps candidate 2 initial (.value 2)).mpr execution
  simp only [unfinished_has_no_answer_yet, List.not_mem_nil] at member

end Examples

#print axioms Steps.trans
#print axioms Steps.transitions_eq
#print axioms Steps.mem_runFrontier
#print axioms Steps.mem_runFrontier_of_le
#print axioms runFrontier_reachable
#print axioms answers_iff_steps
#print axioms Examples.intercepted_answer_has_actual_path
#print axioms Examples.too_short_has_no_completed_path

end Mettapedia.Languages.MeTTa.PrimeNeedLocalSteps
