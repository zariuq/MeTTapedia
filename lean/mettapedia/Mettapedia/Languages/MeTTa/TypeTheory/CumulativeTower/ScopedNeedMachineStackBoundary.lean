import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics

/-!
# First returns to an owned Need-machine stack boundary

A saved continuation is a suffix of the actual machine stack. Before its
return, the machine may push and discharge any number of inner frames. Its
first exit from that region is a returned outcome at precisely the saved
stack, not an execution of that continuation. The finite-path decomposition
retains the exact intermediate machine, including the world and work account.

These are laws of the existing machine for an arbitrary source specification.
They do not define a source evaluator or assert termination. Ordinary paths
may continue past a return and change its outcome; `FirstReturn` excludes that
overshoot explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeNeedReference
namespace StackBoundary

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

/-- The delimiter has not been consumed. A returned state at the delimiter
itself is the boundary, whereas a returned state above it still has work. -/
inductive Above (delimiter : List (Frame Resume)) :
    Control Local Resume Value StableFault RetryableFault → Prop where
  | force (cell : CellId) (pending : List (Frame Resume)) :
      Above delimiter (.force cell (pending ++ delimiter))
  | run (state : Local) (pending : List (Frame Resume)) :
      Above delimiter (.run state (pending ++ delimiter))
  | returned (outcome : Produced Value StableFault RetryableFault)
      (frame : Frame Resume) (pending : List (Frame Resume)) :
      Above delimiter (.returned outcome ((frame :: pending) ++ delimiter))

def AtBoundary (delimiter : List (Frame Resume))
    (control : Control Local Resume Value StableFault RetryableFault) : Prop :=
  ∃ outcome, control = .returned outcome delimiter

theorem boundary_not_above {delimiter : List (Frame Resume)}
    {control : Control Local Resume Value StableFault RetryableFault}
    (boundary : AtBoundary delimiter control) : ¬ Above delimiter control := by
  intro above
  cases above with
  | force cell pending =>
      rcases boundary with ⟨_, impossible⟩
      cases impossible
  | run state pending =>
      rcases boundary with ⟨_, impossible⟩
      cases impossible
  | returned result frame pending =>
      rcases boundary with ⟨_, equality⟩
      have stackEquality := (Control.returned.inj equality).2
      have lengths := congrArg List.length stackEquality
      simp only [List.length_append, List.length_cons] at lengths
      omega

theorem halted_not_above (delimiter : List (Frame Resume))
    (outcome : Produced Value StableFault RetryableFault) :
    ¬ Above (Local := Local) delimiter (.halted outcome) := by
  intro above
  cases above

theorem returned_above_or_boundary (delimiter pending : List (Frame Resume))
    (outcome : Produced Value StableFault RetryableFault) :
    Above (Local := Local) delimiter (.returned outcome (pending ++ delimiter)) ∨
      AtBoundary (Local := Local) delimiter (.returned outcome (pending ++ delimiter)) := by
  cases pending with
  | nil => exact .inr ⟨outcome, rfl⟩
  | cons frame pending => exact .inl (.returned outcome frame pending)

private theorem branchAlternatives_above
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (delimiter pending : List (Frame Resume))
    (index : Nat) (alternatives : List (Rule × Local))
    {candidate : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : candidate ∈ branchAlternatives machine base cell record owner
      (pending ++ delimiter) index alternatives) : Above delimiter candidate.control := by
  induction alternatives generalizing index with
  | nil => simp [branchAlternatives] at member
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at member
      rcases member with rfl | member
      · exact .run head.2 (.commit cell owner :: pending)
      · exact ih (index + 1) member

/-- An actual transition cannot skip a saved return boundary. This includes
allocation failure, cache failure and all commit-ownership cases. -/
theorem step_above_or_boundary
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {delimiter : List (Frame Resume)}
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (above : Above delimiter machine.control) (member : next ∈ step spec machine) :
    Above delimiter next.control ∨ AtBoundary delimiter next.control := by
  rcases machine with ⟨world, control, work⟩
  cases above with
  | force cell pending =>
      simp only [step] at member
      split at member
      · simp only [List.mem_singleton] at member
        subst next
        exact returned_above_or_boundary delimiter pending _
      · rename_i record lookup
        cases cacheEquality : record.cache with
        | suspended =>
          simp only [cacheEquality] at member
          split at member
          · simp only [List.mem_singleton] at member
            subst next
            exact returned_above_or_boundary delimiter pending _
          · exact .inl (branchAlternatives_above _ _ _ _ _ delimiter pending _ _ member)
        | evaluating owner =>
          simp only [cacheEquality, List.mem_singleton] at member
          subst next
          exact returned_above_or_boundary delimiter pending _
        | value value =>
          simp only [cacheEquality, List.mem_singleton] at member
          subst next
          exact returned_above_or_boundary delimiter pending _
        | stableFault fault =>
          simp only [cacheEquality, List.mem_singleton] at member
          subst next
          exact returned_above_or_boundary delimiter pending _
  | run state pending =>
      simp only [step] at member
      split at member
      · simp only [List.mem_singleton] at member
        subst next
        exact returned_above_or_boundary delimiter pending _
      · simp only [List.mem_singleton] at member
        subst next
        exact .inl (.force _ (.resume _ :: pending))
      · split at member
        · simp only [List.mem_singleton] at member
          subst next
          exact returned_above_or_boundary delimiter pending _
        · simp only [List.mem_singleton] at member
          subst next
          exact .inl (.run _ pending)
      · split at member
        · simp only [List.mem_singleton] at member
          subst next
          exact returned_above_or_boundary delimiter pending _
        · split at member
          · simp only [List.mem_singleton] at member
            subst next
            exact returned_above_or_boundary delimiter pending _
          · simp only [List.mem_singleton] at member
            subst next
            exact .inl (.run _ pending)
      · simp only [List.mem_singleton] at member
        subst next
        exact .inl (.run _ pending)
  | returned outcome frame pending =>
      cases frame with
      | resume token =>
          simp only [step, List.cons_append, List.mem_singleton] at member
          subst next
          exact .inl (.run _ pending)
      | commit cell owner =>
          simp only [step, List.cons_append] at member
          repeat' first
            | split at member
            | simp only [List.mem_singleton] at member
              subst next
              exact returned_above_or_boundary delimiter pending _

/-- A finite path stopped at its first returned outcome at `delimiter`. -/
inductive FirstReturn
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (delimiter : List (Frame Resume)) : Nat →
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → Prop where
  | stop {machine} (boundary : AtBoundary delimiter machine.control) :
      FirstReturn spec delimiter 0 machine machine
  | cons {length machine next final} (above : Above delimiter machine.control)
      (occurrence : StepOccurrence spec machine next)
      (rest : FirstReturn spec delimiter length next final) :
      FirstReturn spec delimiter (length + 1) machine final

namespace FirstReturn

theorem toSteps
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {delimiter : List (Frame Resume)} {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : FirstReturn spec delimiter length initial final) :
    Steps spec length initial final := by
  induction execution with
  | stop => exact .refl _
  | cons _ occurrence _ ih => exact .cons occurrence ih

theorem target_boundary
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {delimiter : List (Frame Resume)} {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : FirstReturn spec delimiter length initial final) :
    AtBoundary delimiter final.control := by
  induction execution with
  | stop boundary => exact boundary
  | cons _ _ _ ih => exact ih

theorem boundary_start_length_zero
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {delimiter : List (Frame Resume)} {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : FirstReturn spec delimiter length initial final)
    (boundary : AtBoundary delimiter initial.control) : length = 0 := by
  cases execution with
  | stop => rfl
  | cons above _ _ => exact (boundary_not_above boundary above).elim

end FirstReturn

/-- Split at the first return, before executing the saved continuation.
The suffix is the original residual execution, not a reconstructed run. -/
theorem extract_firstReturn
    {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {delimiter : List (Frame Resume)} {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final)
    (above : Above delimiter initial.control)
    (outside : ¬ Above delimiter final.control) :
    ∃ prefixLength suffixLength middle,
      prefixLength + suffixLength = length ∧
      FirstReturn spec delimiter prefixLength initial middle ∧
      Steps spec suffixLength middle final := by
  induction execution with
  | refl => exact (outside above).elim
  | cons occurrence rest ih =>
      rcases step_above_or_boundary spec above (occurrence.mem spec) with nextAbove | boundary
      · rcases ih nextAbove outside with ⟨pending, suffix, middle, total, segment, remaining⟩
        exact ⟨pending + 1, suffix, middle, by omega,
          .cons above occurrence segment, remaining⟩
      · exact ⟨1, _, _, by omega, .cons above occurrence (.stop boundary), rest⟩

/-- Direct local return is a first return, for any world and saved stack. -/
theorem done_firstReturn
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (work : Work) (state : Local) (delimiter : List (Frame Resume))
    (outcome : Produced Value StableFault RetryableFault)
    (done : spec.action state = .done outcome) :
    FirstReturn spec delimiter 1
      ⟨world, .run state delimiter, work⟩
      ⟨world, .returned outcome delimiter, work.bump 0 0 0 0⟩ := by
  exact .cons (.run state []) ⟨0, by simp [step, done, finished]⟩ (.stop ⟨outcome, rfl⟩)

/-- A saved commit can change an already returned outcome if its cell is
missing. Such an overshooting transition is not a first-return segment. -/
theorem missing_commit_is_not_firstReturn
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (work : Work) (cell : CellId) (owner : EvaluatorId)
    (outcome : Produced Value StableFault RetryableFault)
    (missing : world.heap.lookup cell = none) :
    let initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect :=
      ⟨world, .returned outcome [.commit cell owner], work⟩
    let final := retryMachine initial world cell (.outOfScope cell) [] 1 0 0 0
    Steps spec 1 initial final ∧
      ¬ FirstReturn spec [.commit cell owner] 1 initial final := by
  dsimp only
  constructor
  · exact .cons ⟨0, by simp [step, missing]⟩ (.refl _)
  · intro execution
    have impossible := execution.boundary_start_length_zero ⟨outcome, rfl⟩
    omega

#print axioms boundary_not_above
#print axioms step_above_or_boundary
#print axioms FirstReturn.toSteps
#print axioms FirstReturn.target_boundary
#print axioms extract_firstReturn
#print axioms done_firstReturn
#print axioms missing_commit_is_not_firstReturn

end StackBoundary
end Mettapedia.Languages.MeTTa.PrimeNeedReference
