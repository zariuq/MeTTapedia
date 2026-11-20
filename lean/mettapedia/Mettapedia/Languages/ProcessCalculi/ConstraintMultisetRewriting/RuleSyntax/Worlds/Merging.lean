import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Confinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.SystemsCalculus

/-!
# Side by side, and merged: the two compositions at the twin-binder frames

The calculus of systems of `Encodings.Strict` composes two systems by the union of their programs and
the tensor of their states: one world that holds both. In a bag of worlds that composite is one move
away from the two systems side by side: the **merge** by the tensor (`tensorJoining`), admitted
exactly under the condition `stepParallelSolvable` asks of a composable pair, solvable joint knowledge
(`merge_of_composable`).

## What each composition does to the two witnesses

* **A neighbour whose knowledge has no solution** (`junk_as_a_world`): side by side with the junk
  system, the system with the row `ω!(0)` reaches success; the merge of the two is refused; and their
  tensor, the composite when every pair is composable, never reaches success (`Encodings.junk_switches`).
  In every bag, with every space, the junk system is no neighbour (`junk_is_no_neighbour`).
* **A rule guarded by the none query of a row** (`none_as_worlds`): side by side with the system
  that holds the row `*@0`, the guarded spawn reaches success; the merge of the two is admitted
  (`spawn_blocker_mergeable`); and merged they never reach success
  (`Encodings.blocked_never_succeeds`). A none check reads the rows of its own world.

## The fate of the separation

* `worldsParallel ω`: bags of worlds at the twin-binder frames, side by side, success the output barb on
  `ω` in some world. It is persistent (`worldsParallel_persistent`), so it has no switching pair, for
  any rules, none checks included.
* `incumbent_not_into_worlds`: by the tree's separation theorem, **the calculus of systems under the
  tensor has no uniform translation into the calculus of worlds side by side**, although both run the
  same step with the same rules: the criterion separates two compositions of one calculus. Under the
  tensor a none check reads the neighbour's rows; side by side it does not.
* `image_par_is_one_merge`: the translation of a parallel composition of the reflective calculus is one
  merge away from the translations of its two components side by side. The composition of the
  reflective calculus corresponds to the merge, not to side by side.
* `succeeds_of_merged`: whatever a composable pair reaches when merged, the two side by side reach.
* `merge_gives_a_reduction`: two worlds of which neither has a reduction, and whose merge has one.
  Worlds side by side do interact, through the merge.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
  (tensor tensor_solvable_iff stepParallel stepParallelSolvable OutBarb spawnSystem blockerSystem
    outputSystem junkSystem spawnSystem_succeeds blocked_never_succeeds single_output_barb decl
    solvable_not_into_persistent tensor_junk_unsolvable system_inert rhoParallel rhoIntoStepSolvable
    image_composable solvable_switchable SystemReduces encode nil encode_nil_present receiverSenderRows
    image_nil_not_unit junk_unsolvable)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
  (sig G Closed knowledge outputT zeroT mem_program)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open NullsOnTheStep.ParallelClosed (ParallelCalculus UniformTranslation)

/-- Systems of the step at the twin-binder frames. -/
abbrev TwinSystem := Equivalence.System (Contextual.Terms sig) ℕ

/-- **Merging by the tensor**: the joining of two states at the twin-binder frames is their tensor; it
is alive exactly when both are (`Encodings.tensor_solvable_iff`). -/
def tensorJoining : Joining knowledge ℕ where
  join := tensor
  left_alive s t alive := ((tensor_solvable_iff s t).mp alive).1
  right_alive s t alive := ((tensor_solvable_iff s t).mp alive).2

/-- **Bags of worlds at the twin-binder frames, as a calculus with a parallel composition**: side by
side; success the output barb on `ω` in some world. -/
def worldsParallel (ω : G [] .nm) : ParallelCalculus.{1} :=
  bagParallel knowledge tensorJoining (events knowledge ℕ decl) (OutBarb ω)

/-- **Persistent**, for every program. -/
theorem worldsParallel_persistent (ω : G [] .nm) : (worldsParallel ω).Persistent :=
  bagParallel_persistent (X := knowledge) (J := tensorJoining)
    (family := events knowledge ℕ decl) (events_program_monotone knowledge decl) (OutBarb ω)

/-- **The calculus of systems under the tensor has no uniform translation into the calculus of worlds
side by side.** The first is switchable by none queries (`Encodings.solvable_switchable`); the second is
persistent. -/
theorem incumbent_not_into_worlds (ω : G [] .nm) :
    IsEmpty (UniformTranslation (stepParallelSolvable ω) (worldsParallel ω)) :=
  solvable_not_into_persistent ω (worldsParallel ω) (worldsParallel_persistent ω)

/-- **The composite of a composable pair is one merge away from the pair side by side**: the merge is
admitted under the condition that makes the pair composable. -/
theorem merge_of_composable {ω : G [] .nm} {S T : TwinSystem}
    (composable : (stepParallelSolvable ω).composable S T) :
    Move knowledge tensorJoining (events knowledge ℕ decl) ⟨S ::ₘ T ::ₘ 0, ∅⟩
      ⟨((stepParallelSolvable ω).par S T : TwinSystem) ::ₘ 0, ∅⟩ :=
  Move.merge (family := events knowledge ℕ decl) 0 ∅ S T composable

/-- **Whatever a composable pair reaches when merged, the two side by side reach.** -/
theorem succeeds_of_merged {ω : G [] .nm} {S T : TwinSystem}
    (composable : (stepParallelSolvable ω).composable S T)
    (succeeds : (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par S T)) :
    (worldsParallel ω).Succeeds ⟨S ::ₘ T ::ₘ 0, ∅⟩ := by
  obtain ⟨U, run, shows⟩ := succeeds
  exact (worldsParallel ω).succeeds_of_step (merge_of_composable composable)
    (succeeds_of_world (OutBarb ω) run shows 0 ∅)

/-- **The translation of a parallel composition is one merge away from the translations side by
side.** -/
theorem image_par_is_one_merge {ω : G [] .nm} (closed : Closed ω) (P Q : (rhoParallel ω).Term) :
    Move knowledge tensorJoining (events knowledge ℕ decl)
      ⟨((rhoIntoStepSolvable closed).map P : TwinSystem) ::ₘ
        ((rhoIntoStepSolvable closed).map Q : TwinSystem) ::ₘ 0, ∅⟩
      ⟨((rhoIntoStepSolvable closed).map ((rhoParallel ω).par P Q) : TwinSystem) ::ₘ 0, ∅⟩ := by
  have same : (rhoIntoStepSolvable closed).map ((rhoParallel ω).par P Q) =
      (stepParallelSolvable ω).par ((rhoIntoStepSolvable closed).map P)
        ((rhoIntoStepSolvable closed).map Q) :=
    (rhoIntoStepSolvable closed).homomorphic P Q trivial
  rw [same]
  exact merge_of_composable (image_composable closed P Q)

/-- One world is not two worlds side by side. -/
theorem one_world_ne_two (a b c : TwinSystem) (R R₁ R₂ : Program (Contextual.Terms sig)) :
    (⟨{a}, R⟩ : Bag (Contextual.Terms sig) ℕ) ≠
      (⟨{b}, R₁⟩ : Bag (Contextual.Terms sig) ℕ).beside ⟨{c}, R₂⟩ := by
  intro same
  have cards : Multiset.card ({a} : Multiset TwinSystem) =
      Multiset.card (({b} : Multiset TwinSystem) + {c}) :=
    congrArg (fun W : Bag (Contextual.Terms sig) ℕ => Multiset.card W.worlds) same
  rw [Multiset.card_singleton, Multiset.card_add, Multiset.card_singleton,
    Multiset.card_singleton] at cards
  omega

/-- **With equality as the static equivalence, the translation of the reflective calculus is not
homomorphic for side by side**: the translation of a parallel composition is one world, and the
translations of its components side by side are two. It is homomorphic for the merge
(`Encodings.encode_par`, `image_par_is_one_merge`). -/
theorem image_par_not_side_by_side {ω : G [] .nm} (closed : Closed ω) (P Q : (rhoParallel ω).Term) :
    (⟨{((rhoIntoStepSolvable closed).map ((rhoParallel ω).par P Q) : TwinSystem)}, ∅⟩ :
        Bag (Contextual.Terms sig) ℕ) ≠
      (⟨{((rhoIntoStepSolvable closed).map P : TwinSystem)}, ∅⟩ :
        Bag (Contextual.Terms sig) ℕ).beside
          ⟨{((rhoIntoStepSolvable closed).map Q : TwinSystem)}, ∅⟩ :=
  one_world_ne_two _ _ _ _ _ _

/-! ## The two witnesses, side by side and merged -/

/-- **A neighbour whose knowledge has no solution, as a world.** Side by side with the junk system,
the system with the row `ω!(0)` reaches success; the merge of the two is refused; and their tensor
never reaches success. -/
theorem junk_as_a_world {ω : G [] .nm} (closed : Closed ω) :
    (worldsParallel ω).Succeeds ⟨outputSystem ω ::ₘ junkSystem ::ₘ 0, ∅⟩ ∧
      ¬ knowledge.Solvable (tensorJoining.join (outputSystem ω).state junkSystem.state).knowledge ∧
      ¬ (stepParallel ω).Succeeds ((stepParallel ω).par (outputSystem ω) junkSystem) :=
  ⟨succeeds_of_world (OutBarb ω) .refl (single_output_barb closed) (junkSystem ::ₘ 0) ∅,
    tensor_junk_unsolvable _, system_inert ω (tensor_junk_unsolvable (outputSystem ω).state)⟩

/-- **The junk system is no neighbour**: beside it, in any bag and with any space, the bag reaches
success on `ω` exactly when it does without it. An instance of `dead_world_is_no_neighbour`. -/
theorem junk_is_no_neighbour (ω : G [] .nm) (ws : Multiset TwinSystem)
    (R : Program (Contextual.Terms sig)) :
    (worldsParallel ω).Succeeds ⟨junkSystem ::ₘ ws, R⟩ ↔ (worldsParallel ω).Succeeds ⟨ws, R⟩ :=
  dead_world_is_no_neighbour
    (fun _ unsolvable => Equivalence.not_mayBarb_of_unsolvable unsolvable) junk_unsolvable ws R

/-- The guarded spawn and the system with the row `*@0` can be merged: neither has knowledge. -/
theorem spawn_blocker_mergeable (ω : G [] .nm) :
    knowledge.Solvable (tensorJoining.join (spawnSystem ω).state blockerSystem.state).knowledge := by
  refine ⟨_, knowledge.id _, fun e member => ?_⟩
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  exact absurd member List.not_mem_nil

/-- **A rule guarded by the none query of a row, as a world.** Side by side with the system that holds
the row `*@0`, the guarded spawn reaches success; the merge of the two is admitted; and merged they
never reach success. A none check reads the rows of its own world. -/
theorem none_as_worlds (ω : G [] .nm) :
    (worldsParallel ω).Succeeds ⟨spawnSystem ω ::ₘ blockerSystem ::ₘ 0, ∅⟩ ∧
      knowledge.Solvable (tensorJoining.join (spawnSystem ω).state blockerSystem.state).knowledge ∧
      ¬ (stepParallel ω).Succeeds ((stepParallel ω).par (spawnSystem ω) blockerSystem) := by
  obtain ⟨T, run, shows⟩ := spawnSystem_succeeds ω
  exact ⟨succeeds_of_world (OutBarb ω) run shows (blockerSystem ::ₘ 0) ∅, spawn_blocker_mergeable ω,
    blocked_never_succeeds ω⟩

/-! ## A merge gives a reduction that was not there -/

/-- The four-rule program of the reflective calculus. -/
abbrev fourRules : Program (Contextual.Terms sig) :=
  FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.program

/-- The translation of `0`, the four-rule program with no row, has no reduction: each of its rules
takes a row. -/
theorem image_nil_stuck (T : TwinSystem) : ¬ SystemReduces ⟨fourRules, encode nil⟩ T := by
  rintro ⟨-, f, admitted, -⟩
  obtain ⟨⟨-, -, -, takeLength, -⟩, enabled, -⟩ := admitted
  have takes : f.rule.body.take ≠ [] := by
    rcases mem_program.mp f.member with h | h | h | h <;> rw [h] <;> simp
  have taken : f.selection.taken ≠ [] := by
    intro empty
    rw [empty] at takeLength
    exact takes (List.eq_nil_of_length_eq_zero takeLength)
  obtain ⟨o, inTaken⟩ := List.exists_mem_of_ne_nil _ taken
  have present : o ∈ (encode nil).present := enabled.taken_subset (List.mem_toFinset.mpr inTaken)
  rw [encode_nil_present] at present
  exact absurd present (Finset.notMem_empty o)

/-- **A merge gives a reduction that was not there.** The system with the rows of `@0(y).0 | @0!(0)`
and no rule has no reduction; the four-rule program with no row has none; side by side neither world
fires; they can be merged; and the merged world has a reduction. Worlds interact through a merge. -/
theorem merge_gives_a_reduction (ω : G [] .nm) :
    (∀ T, ¬ SystemReduces ⟨∅, receiverSenderRows⟩ T) ∧
      (∀ T, ¬ SystemReduces ⟨fourRules, encode nil⟩ T) ∧
      Move knowledge tensorJoining (events knowledge ℕ decl)
        ⟨(⟨∅, receiverSenderRows⟩ : TwinSystem) ::ₘ (⟨fourRules, encode nil⟩ : TwinSystem) ::ₘ 0, ∅⟩
        ⟨((stepParallelSolvable ω).par ⟨∅, receiverSenderRows⟩ ⟨fourRules, encode nil⟩ : TwinSystem) ::ₘ
          0, ∅⟩ ∧
      ∃ T, SystemReduces
        ((stepParallelSolvable ω).par ⟨∅, receiverSenderRows⟩ ⟨fourRules, encode nil⟩) T :=
  ⟨(image_nil_not_unit ω).1, image_nil_stuck, merge_of_composable (image_nil_not_unit ω).2.1,
    (image_nil_not_unit ω).2.2⟩

/-- **The switching pair of the tensor is no switching pair side by side**: the calculus of systems
under the tensor is switchable, and the calculus of worlds is not. -/
theorem switching_is_of_the_composition (ω : G [] .nm) :
    (stepParallelSolvable ω).Switchable ∧ ¬ (worldsParallel ω).Switchable :=
  ⟨solvable_switchable ω, (worldsParallel_persistent ω).not_switchable⟩

#print axioms tensorJoining
#print axioms worldsParallel_persistent
#print axioms incumbent_not_into_worlds
#print axioms merge_of_composable
#print axioms succeeds_of_merged
#print axioms image_par_is_one_merge
#print axioms image_par_not_side_by_side
#print axioms junk_as_a_world
#print axioms junk_is_no_neighbour
#print axioms spawn_blocker_mergeable
#print axioms none_as_worlds
#print axioms image_nil_stuck
#print axioms merge_gives_a_reduction
#print axioms switching_is_of_the_composition

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
