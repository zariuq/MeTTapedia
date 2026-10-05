import Mettapedia.GSLT.Distinction.OrderedSimulationSpans

/-!
# Controls for ordered simulations as span relations

* **A lockstep instance** (`chain_simulation`, `chain_future`).  A two-state
  system and a relabelled copy on another carrier are related by a map; the
  span reading transfers a future formula about the successor at position
  zero.
* **Fibre matching is more than the modal laws** (`merged_control`).  A state
  with two equal successors and a state with one satisfy both endpoint source
  laws, yet no ordered simulation relates them, and they have different
  numbers of successor occurrences.
* **Stuttering misaligns lockstep frontiers** (`stutter_branches`,
  `stutter_misaligns`, `stutter_realigns`).  Each branch of the source is
  matched within one or two target steps, the slow branch through an
  administrative state related to the same source state.  After one source
  step and two target steps the frontiers are not related position by
  position, although they are after one target step, and again at
  completion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.OrderedSimulationSpansControls

open Mettapedia.GSLT.Distinction.SpanTransport

/-! ## A lockstep instance -/

/-- One step to a halted state. -/
def single : OrderedSystem Bool where
  step
    | false => [true]
    | true => []
  halted state := state

/-- The same shape on another carrier. -/
def chain : OrderedSystem (Option Unit) where
  step
    | none => [some ()]
    | some () => []
  halted state := state.isSome

def relabel : Bool → Option Unit
  | false => none
  | true => some ()

theorem chain_simulation : OrderedSimulation single chain (fun state state' => state' = relabel state) :=
  OrderedSimulation.ofMap relabel (by intro state; cases state <;> rfl) (by intro state; cases state <;> rfl)

/-- The successor at position zero halts. -/
def haltsNext : Tense Bool ℕ :=
  .future 0 (.atom true)

/-- **The formula agrees on related states**; it holds at the start. -/
theorem chain_future :
    (Tense.sat single.occurrences haltsNext false ↔ Tense.sat chain.occurrences haltsNext none) ∧
      Tense.sat single.occurrences haltsNext false :=
  ⟨chain_simulation.future_related (.future 0 (.atom true)) rfl,
    ⟨⟨false, 0, by decide⟩, rfl, rfl, rfl⟩⟩

/-! ## Fibre matching is more than the modal laws -/

/-- Two equal successors. -/
def doubled : OrderedSystem Bool where
  step
    | false => [true, true]
    | true => []
  halted state := state

theorem doubled_next (occurrence : doubled.Occurrence) : occurrence.next = true := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false =>
      rcases position with _ | _ | position
      · rfl
      · rfl
      · simp [doubled] at inRange
  | true => simp [doubled] at inRange

theorem single_next (occurrence : single.Occurrence) : occurrence.next = true := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false =>
      rcases position with _ | position
      · rfl
      · simp [single] at inRange
  | true => simp [single] at inRange

theorem doubled_state (occurrence : doubled.Occurrence) : occurrence.state = false := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false => rfl
  | true => simp [doubled] at inRange

theorem single_state (occurrence : single.Occurrence) : occurrence.state = false := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false => rfl
  | true => simp [single] at inRange

/-- **Both endpoint source laws hold, no ordered simulation exists, and the
numbers of successor occurrences differ.** -/
theorem merged_control :
    SourceForth doubled.occurrenceSpan single.occurrenceSpan Eq ∧
      SourceBack doubled.occurrenceSpan single.occurrenceSpan Eq ∧
      ¬ OrderedSimulation doubled single Eq ∧
      (∃ occurrence : doubled.Occurrence, occurrence.position = 1) ∧
      ¬ ∃ occurrence : single.Occurrence, occurrence.position = 1 := by
  refine ⟨?_, ?_, ?_, ⟨⟨false, 1, by decide⟩, rfl⟩, ?_⟩
  · rintro x _ rfl occurrence rfl
    refine ⟨⟨false, 0, by decide⟩, (doubled_state occurrence).symm, ?_⟩
    exact (doubled_next occurrence).trans (single_next _).symm
  · rintro x _ rfl occurrence rfl
    refine ⟨⟨false, 0, by decide⟩, (single_state occurrence).symm, ?_⟩
    exact (doubled_next _).trans (single_next occurrence).symm
  · intro simulation
    have lengths := (simulation.step (state := false) (state' := false) rfl).length_eq
    simp [doubled, single] at lengths
  · rintro ⟨⟨state, position, inRange⟩, rfl⟩
    cases state <;> simp [single] at inRange

/-! ## Stuttering misaligns lockstep frontiers -/

inductive Source where
  | root
  | left
  | right
  | leftDone
  | rightDone
  deriving DecidableEq

inductive Target where
  | root
  | left
  | rightAdmin
  | right
  | leftDone
  | rightDone
  deriving DecidableEq

def source : OrderedSystem Source where
  step
    | .root => [.left, .right]
    | .left => [.leftDone]
    | .right => [.rightDone]
    | _ => []
  halted
    | .leftDone => true
    | .rightDone => true
    | _ => false

/-- The right branch takes an administrative step first. -/
def target : OrderedSystem Target where
  step
    | .root => [.left, .rightAdmin]
    | .left => [.leftDone]
    | .rightAdmin => [.right]
    | .right => [.rightDone]
    | _ => []
  halted
    | .leftDone => true
    | .rightDone => true
    | _ => false

/-- The stuttering relation: the right source state is related to the
administrative target state and to its successor. -/
def stutter : Source → Target → Prop
  | .root, .root => True
  | .left, .left => True
  | .right, .rightAdmin => True
  | .right, .right => True
  | .leftDone, .leftDone => True
  | .rightDone, .rightDone => True
  | _, _ => False

/-- **Each branch is matched within one or two target steps**: related states
agree on halting, and either both have no successors, or the source successors
are related position by position to the target frontier after one or two
steps. -/
theorem stutter_branches :
    ∀ state state', stutter state state' →
      target.halted state' = source.halted state ∧
        ((source.step state = [] ∧ target.step state' = []) ∨
          ∃ k, 1 ≤ k ∧ k ≤ 2 ∧
            List.Forall₂ stutter (source.step state) (target.runFrontier k [state'])) := by
  intro state state' related
  cases state <;> cases state' <;> simp only [stutter] at related
  · exact ⟨rfl, Or.inr ⟨1, le_rfl, by omega, .cons trivial (.cons trivial .nil)⟩⟩
  · exact ⟨rfl, Or.inr ⟨1, le_rfl, by omega, .cons trivial .nil⟩⟩
  · exact ⟨rfl, Or.inr ⟨2, by omega, le_rfl, .cons trivial .nil⟩⟩
  · exact ⟨rfl, Or.inr ⟨1, le_rfl, by omega, .cons trivial .nil⟩⟩
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **After one source step and two target steps the frontiers are not related
position by position.** -/
theorem stutter_misaligns :
    ¬ List.Forall₂ stutter (source.runFrontier 1 [.root]) (target.runFrontier (2 * 1) [.root]) := by
  intro related
  cases related with
  | cons head _ => exact head

/-- They are after one target step, and at completion. -/
theorem stutter_realigns :
    List.Forall₂ stutter (source.runFrontier 1 [.root]) (target.runFrontier 1 [.root]) ∧
      List.Forall₂ stutter (source.runFrontier 2 [.root]) (target.runFrontier (2 * 2) [.root]) :=
  ⟨.cons trivial (.cons trivial .nil), .cons trivial (.cons trivial .nil)⟩

end Mettapedia.GSLT.Distinction.OrderedSimulationSpansControls
