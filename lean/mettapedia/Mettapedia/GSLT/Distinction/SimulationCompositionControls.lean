import Mettapedia.GSLT.Distinction.SimulationComposition
import Mettapedia.GSLT.Distinction.ProductiveBlocksControls

/-!
# Controls for composing cost simulations

* **The product, not the sum** (`product_holds`, `sum_bound_fails`,
  `product_bound_tight`).  A source publishing in one transition, a middle
  machine taking three, and a target taking three for each middle transition:
  the stages cost three each, the composite costs nine, and no bound below nine
  holds, in particular not the sum six.  The composite carries the final
  observation (`composite_final`), and the two stages, which move their targets
  on every transition, compose as stages with reflected completion
  (`chain`, `chain_reflected`).
* **A middle stage that stutters silently** (`spin_done`,
  `stutter_composite`, `stutter_not_reflected`, `stutter_no_progress`).  A
  silently looping middle machine is matched by a finishing target without any
  target transition.  Both stages and their composite are forward
  simulations, yet the target finishes while the source never completes.  The
  first stage has progress; the stuttering stage has none at any cost and any
  rank, and the composite has no backward simulation at any cost.
* **A source-only stage** (`halfway_forward`, `source_only_composite`,
  `source_only_not_reflected`, `halfway_no_backward`).  A source that publishes
  and then is stuck is simulated by a target that publishes and finishes; the
  second stage is the identity, with both laws.  The composite does not reflect
  completion, and the first stage has no backward simulation at any cost.
* **Reflection without a backward simulation** (`checker_progress`,
  `checker_interpreter_reflected`, `interpreter_progress`,
  `check_interpret_final_forward`).  The checker and the three-step
  interpreter of `ProductiveBlocksControls`: the forward simulation moves the
  interpreter on every checker transition, so it reflects completion by
  itself; the interpreter's two administrative transitions stutter in the
  checker under a decreasing rank.  Final observations coincide under the
  forward simulation alone.
* **Middle states are data** (`two_middles`): one composite pair is reached
  through different middle states.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.CompositionControls

open Mettapedia.GSLT.Dynamics.OrderedDemand (Status Observation)
open Mettapedia.GSLT.Distinction.SpanTransport (compose)
open Mettapedia.GSLT.Distinction.DependentComposition (Path)

/-! ## The product, not the sum -/

/-- One publication, then finishing. -/
def quick : Machine Bool ℕ Unit Empty where
  step
    | false => some (.publish [1] true)
    | true => some (.finish ())

/-- Two administrative transitions, then the same publication. -/
def medium : Machine ℕ ℕ Unit Empty where
  step
    | 0 => some (.silent 1)
    | 1 => some (.silent 2)
    | 2 => some (.publish [1] 3)
    | 3 => some (.finish ())
    | _ => none

/-- Eight administrative transitions, then the same publication. -/
def slow : Machine ℕ ℕ Unit Empty where
  step state :=
    if state < 8 then some (.silent (state + 1))
    else if state = 8 then some (.publish [1] 9)
    else if state = 9 then some (.finish ())
    else none

def quickMedium : Bool → ℕ → Prop
  | false, state => state = 0
  | true, state => state = 3

def mediumSlow (state state' : ℕ) : Prop := state ≤ 3 ∧ state' = 3 * state

theorem stage_one : CostSimulation quick medium quickMedium 3 where
  silent := by
    intro state _ _ _ stepped
    cases state <;> simp [quick] at stepped
  publish := by
    intro state state' events next relatedStates stepped
    cases state with
    | false =>
        simp only [quick, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        change state' = 0 at relatedStates
        subst relatedStates
        exact ⟨3, le_rfl, 3, rfl, rfl⟩
    | true => simp [quick] at stepped
  finish := by
    intro state state' verdict relatedStates stepped
    cases state with
    | false => simp [quick] at stepped
    | true =>
        change state' = 3 at relatedStates
        subst relatedStates
        exact ⟨1, by omega, rfl⟩
  fail := by
    intro state _ _ _ stepped
    cases state <;> simp [quick] at stepped
  call := by
    intro state _ _ _ _ stepped
    cases state <;> simp [quick] at stepped

theorem stage_two : CostSimulation medium slow mediumSlow 3 where
  silent := by
    rintro state _ next ⟨bounded, rfl⟩ stepped
    interval_cases state
    · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
      subst stepped
      exact ⟨3, le_rfl, 3, rfl, by omega, rfl⟩
    · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
      subst stepped
      exact ⟨3, le_rfl, 6, rfl, by omega, rfl⟩
    · simp [medium] at stepped
    · simp [medium] at stepped
  publish := by
    rintro state _ events next ⟨bounded, rfl⟩ stepped
    interval_cases state
    · simp [medium] at stepped
    · simp [medium] at stepped
    · simp only [medium, Option.some.injEq, Transition.publish.injEq] at stepped
      obtain ⟨rfl, rfl⟩ := stepped
      exact ⟨3, le_rfl, 9, rfl, by omega, rfl⟩
    · simp [medium] at stepped
  finish := by
    rintro state _ verdict ⟨bounded, rfl⟩ stepped
    interval_cases state
    · simp [medium] at stepped
    · simp [medium] at stepped
    · simp [medium] at stepped
    · exact ⟨1, by omega, rfl⟩
  fail := by
    rintro state _ events ⟨bounded, rfl⟩ stepped
    interval_cases state <;> simp [medium] at stepped
  call := by
    rintro state _ request saved ⟨bounded, rfl⟩ stepped
    interval_cases state <;> simp [medium] at stepped

/-- **The composite holds at the product of the costs.** -/
theorem product_holds : CostSimulation quick slow (compose quickMedium mediumSlow) 9 :=
  stage_one.comp stage_two

theorem slow_quiet (k : ℕ) (small : k ≤ 8) : (slow.run k 0).1 = [] := by
  interval_cases k <;> rfl

/-- **No bound below the product holds**: the target publishes only after nine
transitions. -/
theorem product_bound_tight (cost : ℕ) (small : cost < 9) :
    ¬ CostSimulation quick slow (compose quickMedium mediumSlow) cost := by
  intro simulation
  obtain ⟨k, bound, _, ran, _⟩ :=
    simulation.publish (state := false) (state' := 0) ⟨0, rfl, by omega, rfl⟩ rfl
  have quiet := slow_quiet k (by omega)
  rw [ran] at quiet
  cases quiet

/-- **The naive bound, the sum of the costs, fails.** -/
theorem sum_bound_fails : ¬ CostSimulation quick slow (compose quickMedium mediumSlow) (3 + 3) :=
  product_bound_tight (3 + 3) (by omega)

/-- The composite carries the final observation. -/
theorem composite_final :
    quick.observe 2 false = slow.observe 10 0 ∧ quick.observe 2 false = ⟨[1], .finished ()⟩ :=
  ⟨stage_one.comp_final_eq stage_two (state := false) (state'' := 0) ⟨0, rfl, by omega, rfl⟩
    trivial trivial, rfl⟩

theorem quick_progress : Progress quick medium quickMedium 3 (fun _ => 0) :=
  Progress.of_positive _
    (by
      intro state _ _
      cases state <;> simp [quick])
    (by
      intro state _ _ _ stepped
      cases state <;> simp [quick] at stepped)
    (by
      intro state state' events next relatedStates stepped
      cases state with
      | false =>
          simp only [quick, Option.some.injEq, Transition.publish.injEq] at stepped
          obtain ⟨rfl, rfl⟩ := stepped
          change state' = 0 at relatedStates
          subst relatedStates
          exact ⟨3, le_rfl, by omega, 3, rfl, rfl⟩
      | true => simp [quick] at stepped)

theorem medium_progress : Progress medium slow mediumSlow 3 (fun _ => 0) :=
  Progress.of_positive _
    (by
      rintro state _ ⟨bounded, rfl⟩
      interval_cases state <;> simp [medium])
    (by
      rintro state _ next ⟨bounded, rfl⟩ stepped
      interval_cases state
      · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        exact ⟨3, le_rfl, by omega, 3, rfl, by omega, rfl⟩
      · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        exact ⟨3, le_rfl, by omega, 6, rfl, by omega, rfl⟩
      · simp [medium] at stepped
      · simp [medium] at stepped)
    (by
      rintro state _ events next ⟨bounded, rfl⟩ stepped
      interval_cases state
      · simp [medium] at stepped
      · simp [medium] at stepped
      · simp only [medium, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        exact ⟨3, le_rfl, by omega, 9, rfl, by omega, rfl⟩
      · simp [medium] at stepped)

/-- **The two stages as a chain**: composite relation, cost nine, and
reflected completion. -/
def chain : Stage quick slow :=
  (Stage.ofProgress quickMedium 3 stage_one quick_progress).comp
    (Stage.ofProgress mediumSlow 3 stage_two medium_progress)

theorem chain_cost : chain.cost = 9 :=
  rfl

theorem chain_reflected (fuel' : ℕ) (final : (slow.observe fuel' 0).status.Final) :
    ∃ fuel, quick.observe fuel false = slow.observe fuel' 0 :=
  chain.reflected (state := false) (state' := 0) ⟨0, rfl, by omega, rfl⟩ final

/-! ## A middle stage that stutters silently -/

/-- A machine that only steps silently. -/
def spin : Machine Unit ℕ Unit Empty where
  step _ := some (.silent ())

/-- A machine that finishes at once. -/
def done : Machine Unit ℕ Unit Empty where
  step _ := some (.finish ())

def anyPair : Unit → Unit → Prop := fun _ _ => True

/-- The first stage moves its target on every transition. -/
theorem spin_spin : CostSimulation spin spin anyPair 1 where
  silent := by
    intro _ _ _ _ _
    exact ⟨1, le_rfl, (), rfl, trivial⟩
  publish := by
    intro _ _ _ _ _ stepped
    cases stepped
  finish := by
    intro _ _ _ _ stepped
    cases stepped
  fail := by
    intro _ _ _ _ stepped
    cases stepped
  call := by
    intro _ _ _ _ _ stepped
    cases stepped

/-- **The stuttering stage**: every silent transition of the middle machine is
matched by a finishing target without a transition. -/
theorem spin_done : CostSimulation spin done anyPair 0 where
  silent := by
    intro _ _ _ _ _
    exact ⟨0, le_rfl, (), rfl, trivial⟩
  publish := by
    intro _ _ _ _ _ stepped
    cases stepped
  finish := by
    intro _ _ _ _ stepped
    cases stepped
  fail := by
    intro _ _ _ _ stepped
    cases stepped
  call := by
    intro _ _ _ _ _ stepped
    cases stepped

/-- The composite of the two stages is a forward simulation. -/
theorem stutter_composite : CostSimulation spin done (compose anyPair anyPair) 0 :=
  spin_spin.comp spin_done

theorem spin_spin_progress : Progress spin spin anyPair 1 (fun _ => 0) :=
  Progress.of_positive _ (fun _ stepped => by cases stepped)
    (fun _ _ => ⟨1, le_rfl, by omega, (), rfl, trivial⟩)
    (fun _ stepped => by cases stepped)

/-- **The stuttering stage has no progress**, at any cost and any rank. -/
theorem stutter_no_progress (cost : ℕ) (rank : Unit → ℕ) : ¬ Progress spin done anyPair cost rank := by
  intro progress
  obtain ⟨k, _, _, ran, _, decreases⟩ :=
    progress.silent (state := ()) (state' := ()) (next := ()) trivial rfl
  cases k with
  | zero => exact lt_irrefl _ (decreases rfl)
  | succ k =>
      have finished : done.run (k + 1) () = ([], .finished ()) := rfl
      rw [finished] at ran
      cases ran

theorem spin_incomplete (fuel : ℕ) : spin.observe fuel () = ⟨[], .incomplete⟩ :=
  spin.silent_region_incomplete (fun _ => True) (fun _ _ => ⟨(), rfl, trivial⟩) fuel () trivial

/-- **The composite does not reflect completion**: the target finishes while the
source never completes. -/
theorem stutter_not_reflected : ¬ ReflectsCompletion spin done (compose anyPair anyPair) := by
  intro reflects
  obtain ⟨fuel, reached⟩ := reflects (state := ()) (state' := ()) ⟨(), trivial, trivial⟩ 1 trivial
  rw [spin_incomplete] at reached
  cases reached

/-- Nor does the composite have a backward simulation, at any cost. -/
theorem stutter_no_backward (back : ℕ) :
    ¬ CostSimulation done spin (fun state'' state => compose anyPair anyPair state state'') back :=
  fun backward => stutter_not_reflected (reflectsCompletion_of_backward backward)

/-! ## A source-only stage -/

/-- Publishes, then is stuck. -/
def halfway : Machine Bool ℕ Unit Empty where
  step
    | false => some (.publish [1] true)
    | true => none

/-- **The source-only stage**: every transition of `halfway` is matched by
`quick`. -/
theorem halfway_forward : CostSimulation halfway quick Eq 1 where
  silent := by
    intro state _ _ _ stepped
    cases state <;> simp [halfway] at stepped
  publish := by
    rintro state _ events next rfl stepped
    cases state with
    | false =>
        simp only [halfway, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        exact ⟨1, le_rfl, true, rfl, rfl⟩
    | true => simp [halfway] at stepped
  finish := by
    intro state _ _ _ stepped
    cases state <;> simp [halfway] at stepped
  fail := by
    intro state _ _ _ stepped
    cases state <;> simp [halfway] at stepped
  call := by
    intro state _ _ _ _ stepped
    cases state <;> simp [halfway] at stepped

/-- The composite with the identity stage, which has both laws. -/
theorem source_only_composite : CostSimulation halfway quick (compose Eq Eq) 1 :=
  halfway_forward.comp (CostSimulation.refl quick)

theorem halfway_incomplete (fuel : ℕ) : (halfway.observe fuel false).status = .incomplete := by
  rcases fuel with _ | _ | fuel <;> rfl

/-- **The composite does not reflect completion.** -/
theorem source_only_not_reflected : ¬ ReflectsCompletion halfway quick (compose Eq Eq) := by
  intro reflects
  obtain ⟨fuel, reached⟩ := reflects (state := false) (state' := false) ⟨false, rfl, rfl⟩ 2 trivial
  have status := congrArg Observation.status reached
  rw [halfway_incomplete] at status
  cases status

/-- **The first stage has no backward simulation**, at any cost. -/
theorem halfway_no_backward (back : ℕ) :
    ¬ CostSimulation quick halfway (fun state' state => state = state') back := by
  intro backward
  obtain ⟨fuel, reached⟩ :=
    reflectsCompletion_of_backward backward (state := false) (state' := false) rfl 2 trivial
  have status := congrArg Observation.status reached
  rw [halfway_incomplete] at status
  cases status

/-! ## Reflection without a backward simulation -/

open Controls (checker interpreter related)

/-- The forward simulation moves the interpreter on every checker transition. -/
theorem checker_progress : Progress checker interpreter related 3 (fun _ => 0) :=
  Progress.of_positive _
    (by
      intro state _ _
      cases state <;> simp [checker])
    (by
      intro state _ _ _ stepped
      cases state <;> simp [checker] at stepped)
    (by
      intro state state' events next relatedStates stepped
      cases state with
      | start =>
          simp only [checker, Option.some.injEq, Transition.publish.injEq] at stepped
          obtain ⟨rfl, rfl⟩ := stepped
          cases state' with
          | start => exact ⟨3, le_rfl, by omega, .emitted, rfl, trivial⟩
          | first => exact ⟨2, by omega, by omega, .emitted, rfl, trivial⟩
          | second => exact ⟨1, by omega, by omega, .emitted, rfl, trivial⟩
          | emitted => exact relatedStates.elim
      | verdict => simp [checker] at stepped)

/-- **Completion is reflected by the forward simulation alone.** -/
theorem checker_interpreter_reflected : ReflectsCompletion checker interpreter related :=
  Controls.forward.reflectsCompletion checker_progress

/-- The rank of the interpreter's administrative states. -/
def interpreterRank : Controls.Interpret → ℕ
  | .start => 2
  | .first => 1
  | _ => 0

/-- **Stuttering under a decreasing rank**: the interpreter's two administrative
transitions are matched without a checker transition. -/
theorem interpreter_progress :
    Progress interpreter checker (fun state' state => related state state') 1 interpreterRank where
  moves := by
    intro state' _ _
    cases state' <;> simp [interpreter]
  silent := by
    intro state' state next relatedStates stepped
    cases state' with
    | start =>
        simp only [interpreter, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨0, by omega, .start, rfl, trivial, fun _ => by decide⟩
    | first =>
        simp only [interpreter, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨0, by omega, .start, rfl, trivial, fun _ => by decide⟩
    | second => simp [interpreter] at stepped
    | emitted => simp [interpreter] at stepped
  publish := by
    intro state' state events next relatedStates stepped
    cases state' with
    | second =>
        simp only [interpreter, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨1, le_rfl, .verdict, rfl, trivial, fun zero => absurd zero (by omega)⟩
    | start => simp [interpreter] at stepped
    | first => simp [interpreter] at stepped
    | emitted => simp [interpreter] at stepped

theorem interpreter_checker_reflected :
    ReflectsCompletion interpreter checker (fun state' state => related state state') :=
  Controls.backward.reflectsCompletion interpreter_progress

/-- Final observations coincide under the forward simulation alone. -/
theorem check_interpret_final_forward : checker.observe 2 .start = interpreter.observe 4 .start :=
  Controls.forward.final_eq_forward (state := .start) (state' := .start) trivial trivial trivial

/-! ## Middle states are data -/

/-- **One composite pair, two middle states**: the checker's start reaches the
checker's start through the interpreter's start and through its first
administrative state. -/
theorem two_middles : ∃ first second : Path related (fun state' state => related state state')
    Controls.Check.start Controls.Check.start, first.1 ≠ second.1 :=
  ⟨⟨.start, trivial, trivial⟩, ⟨.first, trivial, trivial⟩, by decide⟩

end Mettapedia.GSLT.Distinction.ProductiveBlocks.CompositionControls
