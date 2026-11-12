import Mathlib.Algebra.FreeMonoid.Basic
import Mettapedia.Logic.LinearLogic.KnowledgeTensorControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Interchange

/-!
# Controls for interchange cells of the two-zone calculus

* **Knowledge grades the interchange** (`teller_asker_cell_iff`): a teller of `true` and an asker
  that waits for it have an interchange cell exactly at the knowledge where `true` is already known,
  that is, where the teller's tell is quiet. Positive: `teller_asker_cell_known`; negative:
  `teller_asker_no_cell_unknown`.
* **Takes and makes interchange** (`takers_interchange`, `takers_interchange_events`): a taker of
  `a` and a taker of `b` side by side have the interchange cell, and it exchanges their events.
  Placed beside more atoms under more knowledge it is a cell with the same event map
  (`takers_interchange_placed`).
* **Event identity** (`cycle_symmetry_two_tokens`, `cycle_cells_one_token`): a use that takes `a`
  and makes `a` again, twice, at two copies of `a`, has a symmetry cell that exchanges its two
  events; at one copy the second firing takes what the first made, the two are not independent,
  and every cell from the word to itself is the identity on events, although both orders of the
  two firings run.
* **Models and cells** (`free_weights_separate`): words related by a cell have one product of
  weights in every commutative monoid (`weights_invariant`) and different products in the free
  monoid.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.InterchangeControls

open Mettapedia.Logic.LinearLogic.KnowledgeTensor
open Mettapedia.Logic.LinearLogic.KnowledgeTensorControls
open Item Decl

/-! ## Knowledge grades the interchange -/

/-- **The teller and the asker are independent at the start exactly where `true` is known.** -/
theorem teller_asker_independent_iff (k : Knowledge) :
    askTell.Independent teller asker k start ↔ k ≤ {true} := by
  constructor
  · rintro ⟨_, _, _, _, _, asked⟩
    have held : k ⊓ Set.univ ≤ ({true} : Set Bool) := asked
    simpa using held
  · intro known
    refine ⟨0, ?_, le_refl _, le_refl _, True.intro, ?_⟩
    · show askTell.premises asker + askTell.premises teller = {d} + {a} + 0
      simp only [System.premises, askTell, add_zero]
      exact add_comm _ _
    · show k ⊓ Set.univ ≤ ({true} : Set Bool)
      exact inf_le_left.trans known

/-- **The interchange cell of the teller and the asker exists exactly where the teller is quiet.** -/
theorem teller_asker_cell_iff (k : Knowledge) :
    Nonempty (Cell askTell (k, start) [teller, asker] [asker, teller]) ↔ k ≤ {true} := by
  constructor
  · rintro ⟨cell⟩
    obtain ⟨before, mid, x, y, after, shape, reach, admissible⟩ := cell.first_swap (by decide)
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Rearrangement.split_two shape.symm
    cases reach
    exact (teller_asker_independent_iff k).mp admissible
  · intro known
    exact ⟨Rearrangement.swap [] (k, start) teller asker [] (Runs.nil _)
      ((teller_asker_independent_iff k).mpr known) (Rearrangement.refl _ _)⟩

/-- Positive: where `true` is known, the cell exists. -/
theorem teller_asker_cell_known : Nonempty (Cell askTell ({true}, start) [teller, asker] [asker, teller]) :=
  (teller_asker_cell_iff {true}).mpr le_rfl

/-- Negative: from no knowledge there is no cell; the asker waits for the tell. -/
theorem teller_asker_no_cell_unknown :
    IsEmpty (Cell askTell (Set.univ, start) [teller, asker] [asker, teller]) := by
  refine ⟨fun cell => ?_⟩
  have known : (Set.univ : Knowledge) ≤ {true} := (teller_asker_cell_iff Set.univ).mp ⟨cell⟩
  have impossible : false = true := known (Set.mem_univ false)
  exact absurd impossible (by decide)

/-! ## Takes and makes -/

/-- Three uses: take `a`, take `b`, and take `a` to make `a` again. -/
inductive Use where
  | eatA | eatB | cycle
  deriving DecidableEq

open Use

/-- The takers: no reads, no tells, no guards. -/
def takers : System Knowledge Item Use where
  take := fun
    | eatA => {a}
    | eatB => {b}
    | cycle => {a}
  read := fun _ => 0
  make := fun
    | eatA => 0
    | eatB => 0
    | cycle => {a}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem eatA_runs : ∃ (k : Knowledge) (Γ : Multiset Item), takers.Run Set.univ {a} [eatA] k Γ :=
  ⟨_, _, System.Run.fire ⟨0, by simp [System.premises, takers], True.intro, rfl, rfl⟩
    (System.Run.done _ _)⟩

theorem eatB_runs : ∃ (k : Knowledge) (Γ : Multiset Item), takers.Run Set.univ {b} [eatB] k Γ :=
  ⟨_, _, System.Run.fire ⟨0, by simp [System.premises, takers], True.intro, rfl, rfl⟩
    (System.Run.done _ _)⟩

/-- **The interchange cell of a taker of `a` and a taker of `b`.** -/
def takers_interchange : Cell takers (Set.univ, {a} + {b}) [eatA, eatB] [eatB, eatA] :=
  interchange [eatB] [eatA] Set.univ {a} {b} eatA_runs eatB_runs

/-- **It exchanges the two events.** -/
theorem takers_interchange_events :
    takers_interchange.events 0 = 1 ∧ takers_interchange.events 1 = 0 := by
  have distinct : ([eatB] ++ [eatA]).Nodup := by decide
  exact ⟨interchange_events [eatB] [eatA] Set.univ {a} {b} eatA_runs eatB_runs distinct (by decide),
    interchange_events [eatB] [eatA] Set.univ {a} {b} eatA_runs eatB_runs distinct (by decide)⟩

/-- **Placed beside `c` under the knowledge `{true}`, it is a cell with the same event map.** -/
theorem takers_interchange_placed :
    (takers_interchange.place {c} {true}).events 0 = 1 ∧
      (takers_interchange.place {c} {true}).events 1 = 0 := by
  rw [events_place]
  exact takers_interchange_events

/-! ## Event identity -/

/-- At two copies of `a`, two firings of `cycle` are independent. -/
theorem cycle_independent_two_tokens : independent takers (Set.univ, {a} + {a}) cycle cycle :=
  ⟨0, by simp [takers], le_refl _, le_refl _, True.intro, True.intro⟩

/-- At one copy of `a`, they are not: the second takes what the first made. -/
theorem cycle_not_independent_one_token : ¬ independent takers (Set.univ, {a}) cycle cycle := by
  rintro ⟨shared, source, _, _, _, _⟩
  have sizes := congrArg Multiset.card source
  simp [takers] at sizes

/-- At one copy of `a`, both orders of the two firings run: they form a square. -/
theorem cycle_square_one_token : Square (fires takers) (Set.univ, {a}) cycle cycle := by
  have once : fires takers (Set.univ, {a}) cycle (Set.univ ⊓ Set.univ, {a}) :=
    ⟨0, by simp [System.premises, takers], True.intro, rfl, by simp [System.conclusions, takers]⟩
  have twice : fires takers (Set.univ ⊓ Set.univ, {a}) cycle (Set.univ ⊓ Set.univ ⊓ Set.univ, {a}) :=
    ⟨0, by simp [System.premises, takers], True.intro, rfl, by simp [System.conclusions, takers]⟩
  exact ⟨_, Runs.cons once (Runs.cons twice (Runs.nil _)), Runs.cons once (Runs.cons twice (Runs.nil _))⟩

/-- **The symmetry cell at two copies of `a`**: it exchanges the two events of a word with itself. -/
def cycle_symmetry : Cell takers (Set.univ, {a} + {a}) [cycle, cycle] [cycle, cycle] :=
  Rearrangement.symmetry [] (Runs.nil _) cycle [] cycle_independent_two_tokens

theorem cycle_symmetry_two_tokens :
    cycle_symmetry.events 0 = 1 ∧
      (Rearrangement.refl _ _ : Cell takers (Set.univ, {a} + {a}) [cycle, cycle] [cycle, cycle]).events 0 = 0 :=
  Rearrangement.symmetry_events [] (Runs.nil _) cycle [] cycle_independent_two_tokens

/-- **At one copy of `a`, every cell from the word to itself is the identity on events.** -/
theorem cycle_cells_one_token {w w' : List Use} (cell : Cell takers (Set.univ, {a}) w w')
    (shape : w = [cycle, cycle]) : cell.events = id := by
  cases cell with
  | refl => rfl
  | swap before mid x y after reach admissible rest =>
      exfalso
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Rearrangement.split_two shape
      cases reach
      exact cycle_not_independent_one_token admissible

/-! ## Models and cells -/

/-- **The free monoid separates words that a cell relates**; every commutative monoid identifies
them (`weights_invariant`). -/
theorem free_weights_separate :
    Nonempty (Cell takers (Set.univ, {a} + {b}) [eatA, eatB] [eatB, eatA]) ∧
      ([eatA, eatB].map (FreeMonoid.of : Use → FreeMonoid Use)).prod ≠
        ([eatB, eatA].map (FreeMonoid.of : Use → FreeMonoid Use)).prod := by
  refine ⟨⟨takers_interchange⟩, fun same => ?_⟩
  have lists := congrArg FreeMonoid.toList same
  simp at lists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.InterchangeControls
