import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.Firings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Embedding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Interaction

/-!
# Boundaries of the world correspondences

The earlier list-of-worlds candidate has a forward operational translation
into full bag moves at the explicit `events X O E` instance. Merging prevents
a general reverse translation through that same representation. Likewise, the singleton correspondence for firings
does not extend to full moves: fork leaves every singleton image.

The concrete sharing control fires a published closed row at an otherwise
rule-free reader. Erasing the shared rule space removes that transition.
Thus a comparison must retain the shared rule environment it actually uses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open FragmentsOfTheStep.TransitionMaps
open RuleSyntax RuleSyntax.Worlds
open RuleSyntax.Equivalence (System)
open Hosting.Alternatives.Worlds (WState WStep)

universe uO uT uH uE uOcc

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O]
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)

abbrev moves (joining : Joining X O) : GSLT := theoryOf (Bag Tm O) (Move X joining (events X O E))

def oldWorldTranslation (program : Program Tm) (joining : Joining X O) :
    OperationalTranslation (theoryOf (WState Tm O) (WStep X E program)) (moves X E joining) where
  mapTerm := ofWState program
  mapEquiv same := congrArg (ofWState program) same
  mapStep := move_of_wstep joining

/-- Full moves can leave the singleton image immediately, independently
of which rules the one world holds. -/
theorem fork_outside_singleton (program shared : Program Tm) (joining : Joining X O)
    (state : State Tm O) :
    Move X joining (events X O E) (singleton program shared state)
      ⟨(⟨program, state⟩ : System Tm O) ::ₘ {(⟨program, state⟩ : System Tm O)}, shared⟩ ∧
      ∀ after : State Tm O, singleton program shared after ≠
        ⟨(⟨program, state⟩ : System Tm O) ::ₘ {(⟨program, state⟩ : System Tm O)}, shared⟩ := by
  refine ⟨Move.fork (X := X) (J := joining) (family := events X O E) 0 shared ⟨program, state⟩, ?_⟩
  intro after same
  have counts := congrArg (fun bag : Bag Tm O => bag.worlds.card) same
  simp [singleton] at counts

theorem singleton_full_moves_not_bisimulation (program shared : Program Tm)
    (joining : Joining X O) (state : State Tm O) :
    ¬ FunctionalBisimulation (Steps X O E (program ∪ shared)) (Move X joining (events X O E))
      (singleton program shared) := by
  intro comparison
  obtain ⟨moved, outside⟩ := fork_outside_singleton X E program shared joining state
  obtain ⟨after, _, same⟩ := comparison.zag moved
  exact outside after same

/-- The unrestricted layer can keep copying a world forever. This is an
actual sequence of its fork moves, independent of that world's admission. -/
theorem infinite_forks (program shared : Program Tm) (joining : Joining X O)
    (state : State Tm O) :
    ∃ bags : Nat → Bag Tm O, bags 0 = singleton program shared state ∧
      ∀ n, Move X joining (events X O E) (bags n) (bags (n + 1)) := by
  let world : System Tm O := ⟨program, state⟩
  refine ⟨fun n => ⟨Multiset.replicate (n + 1) world, shared⟩, ?_, ?_⟩
  · simp [singleton, world]
  · intro n
    simpa only [Multiset.replicate_succ] using
      Move.fork (X := X) (J := joining) (family := events X O E) (Multiset.replicate n world) shared world

theorem full_moves_not_normalizing (program shared : Program Tm) (joining : Joining X O)
    (state : State Tm O) :
    ¬ Acc (fun after before => Move X joining (events X O E) before after) (singleton program shared state) :=
  not_acc_iff_exists_descending_chain.mpr (infinite_forks X E program shared joining state)

/-- Old world moves can copy but cannot reduce the number of worlds. -/
theorem oldWorld_count_mono {program : Program Tm} {before after : WState Tm O}
    (moved : WStep X E program before after) : before.worlds.length ≤ after.worlds.length := by
  cases moved <;> simp

/-- A legal merge between two identical worlds reaches an image with one
world, which the old move system cannot reach in one step. -/
theorem merge_prevents_oldWorld_reflection (program : Program Tm) (joining : Joining X O)
    (state : State Tm O) (alive : X.Solvable (joining.join state state).knowledge) :
    ¬ FunctionalBisimulation (WStep X E program) (Move X joining (events X O E)) (ofWState program) := by
  intro comparison
  let before : WState Tm O := ⟨[state, state], []⟩
  let after : Bag Tm O := ⟨{(⟨program, joining.join state state⟩ : System Tm O)}, ∅⟩
  have merged : Move X joining (events X O E) (ofWState program before) after := by
    simpa [before, after, ofWState, Set.union_self, ← Multiset.cons_coe] using
      Move.merge (X := X) (family := events X O E) (J := joining) 0 ∅
        (⟨program, state⟩ : System Tm O) (⟨program, state⟩ : System Tm O) alive
  obtain ⟨next, moved, same⟩ := comparison.zag merged
  have monotone := oldWorld_count_mono X E moved
  have counts := congrArg (fun bag : Bag Tm O => bag.worlds.card) same
  have one : next.worlds.length = 1 := by simpa [after, ofWState] using counts
  change 2 ≤ next.worlds.length at monotone
  omega

def eraseSpace (bag : Bag Tm O) : Bag Tm O := ⟨bag.worlds, ∅⟩

end General

namespace Controls

open RuleSyntax.Examples (Tm X E shift everywhere)
open RuleSyntax.Worlds.Controls (fiveRow emptyReader importFiring import_admitted besideJoining deadPublisher deadPublisher_dead)

/-- The actual snapshot import, with the shared row as its only rule. -/
def isolatedImport : Firing Nat E ((∅ : Program Tm) ∪ {fiveRow}) PUnit.unit :=
  ⟨fiveRow, Set.mem_union_right _ (Set.mem_singleton _), PUnit.unit,
    shift, ⟨[], [], [0]⟩, []⟩

theorem isolatedImport_admitted : isolatedImport.Admits X emptyReader := import_admitted

def sharedReader : Bag Tm Nat := singleton ∅ {fiveRow} emptyReader
def sharedResult : Bag Tm Nat := singleton ∅ {fiveRow} (isolatedImport.result X emptyReader)

/-- Shared rules are semantically observable even when all private
programs are empty. The target after erasing the space has no firing. -/
theorem erasing_shared_space_loses_firing :
    Fires (events X Nat E) sharedReader sharedResult ∧
      ¬ Fires (events X Nat E) (eraseSpace sharedReader) (eraseSpace sharedResult) := by
  refine ⟨Fires.fire (family := events X Nat E) 0 {fiveRow} ⟨∅, emptyReader⟩
    ⟨isolatedImport, isolatedImport_admitted⟩, ?_⟩
  intro fired
  obtain ⟨firing, _, _⟩ := (one_world_fires (X := X) (E := E) (⟨∅, emptyReader⟩ : System Tm Nat)
    ∅ (eraseSpace sharedResult)).mp fired
  simpa using firing.member

theorem live_merge_instance :
    ¬ FunctionalBisimulation (WStep X E (∅ : Program Tm)) (Move X besideJoining (events X Nat E))
      (ofWState (∅ : Program Tm)) := by
  apply merge_prevents_oldWorld_reflection X E ∅ besideJoining emptyReader
  refine ⟨PUnit.unit, everywhere 0, ?_⟩
  intro equation member
  change equation ∈ ([] : EquationStore (Tm PUnit.unit)) at member
  cases member

/-- Even an unsolvable world can be copied by a full move. Its event
confinement theorem therefore cannot be extended by erasing all moves. -/
theorem dead_fork_is_a_move :
    ¬ X.Solvable deadPublisher.knowledge ∧
      Move X besideJoining (events X Nat E) (singleton ∅ ∅ deadPublisher)
        ⟨(⟨∅, deadPublisher⟩ : System Tm Nat) ::ₘ {(⟨∅, deadPublisher⟩ : System Tm Nat)}, ∅⟩ :=
  ⟨deadPublisher_dead, (fork_outside_singleton X E ∅ ∅ besideJoining deadPublisher).1⟩

theorem dead_fork_has_infinite_moves :
    ¬ X.Solvable deadPublisher.knowledge ∧
      ∃ bags : Nat → Bag Tm Nat, bags 0 = singleton ∅ ∅ deadPublisher ∧
        ∀ n, Move X besideJoining (events X Nat E) (bags n) (bags (n + 1)) :=
  ⟨deadPublisher_dead, infinite_forks X E ∅ ∅ besideJoining deadPublisher⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.oldWorldTranslation
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.singleton_full_moves_not_bisimulation
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.full_moves_not_normalizing
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.merge_prevents_oldWorld_reflection
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.Controls.erasing_shared_space_loses_firing
