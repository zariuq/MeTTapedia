import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Maximal

/-!
# `unique`, and a neighbour that switches `every`, `unique` and maximal bags off

## `unique`

**`unique` over a set of rules** (`Bag.AdmitsUnique`): a bag admitted as `every` over the rules that has
one member: the match of the rules when there is exactly one. Its steps are steps of the program
(`Bag.AdmitsUnique.succ`), and every admitted firing of the rules has the key of its member
(`Bag.AdmitsUnique.key_eq`).

## A private neighbour (`Neighbour`)

Beside the one-token state, put a neighbour holding one more token: a ground row, so the neighbour shares
no unknown with anything (`neighbour_private`, by `Scope.independent_of_fixed`), and the state beside it is
the two-token state (`beside_tokens`).

* **The one-match firing stays admitted** (`one_stays`): it is an instance of the composition theorem
  `Scope.admits_beside` (a positive firing is admitted beside a private neighbour).
* **`every` is switched off** (`every_switched_off`): the bag of the one match is `every` alone and not
  beside the neighbour, where `every` must take both tokens.
* **`unique` is switched off** (`unique_switched_off`): it fires alone and has no step beside the
  neighbour.
* **A maximal bag is switched off** (`maximal_switched_off`, from `MaximalControls`).

Completeness, uniqueness and maximality ask the absence of a further match, and a private neighbour can
hold one; they behave as an absence check does (`Scope.admits_beside` is stated for positive rules for
the same reason).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

universe uO uT uH uE uOcc

/-! ## `unique` -/

section UniqueStep

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Bag

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O)

/-- **`unique` over a set of rules**: `every` over the rules, with one member. -/
def AdmitsUnique (Q : Set (Rule Tm)) (f : Bag O E P s.frame) : Prop :=
  f.AdmitsEvery X s Q ∧ f.members.length = 1

variable {X s}

/-- **A step of `unique` is a step of the program.** -/
theorem AdmitsUnique.succ {Q : Set (Rule Tm)} {f : Bag O E P s.frame} (unique : f.AdmitsUnique X s Q) :
    Succ (step X O E P).toStep s (f.result X s) := by
  have nonempty : f.members ≠ [] := fun empty => by
    have one := unique.2
    rw [empty] at one
    simp at one
  exact (succ_iff_single X O E P s _).mpr
    ⟨f, unique.2, ⟨nonempty, admits_of_admitsOwn X unique.1.1⟩, rfl⟩

/-- **Every admitted firing of the rules has the key of the one member.** -/
theorem AdmitsUnique.key_eq {Q : Set (Rule Tm)} {f : Bag O E P s.frame} (unique : f.AdmitsUnique X s Q)
    {m : Member O E P f.ext} (only : f.members = [m]) {g : Firing O E P s.frame} (inQ : g.rule ∈ Q)
    (admitted : g.Admits X s) : firingKey g = m.key := by
  have listed := unique.1.2.2.2 g inQ admitted
  rw [only] at listed
  exact List.mem_singleton.mp listed

end Bag

end UniqueStep

/-! ## A private neighbour -/

namespace Neighbour

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open EveryControls (tokens tokensAt twoTokens takeAt takeAt_admitted firing_shape spendBoth
  spendBoth_every)
open MaximalControls (lone lone_maximal lone_not_maximal lone_admitted)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- What a state of tokens mentions is fixed. -/
theorem tokens_fixed (W : Finset ℕ) : Scope.Fixed action (tokensAt W).Mentions := by
  rintro t (member | member | ⟨o, -, rfl⟩) σ
  · exact absurd member List.not_mem_nil
  · exact absurd member List.not_mem_nil
  · exact action.equivalence.refl _

/-- **The neighbour is private**: it shares no unknown with the one-token state. -/
theorem neighbour_private : Scope.PrivateFrom action (tokensAt {1}) (tokensAt {0}) :=
  Scope.independent_of_fixed (tokens_fixed {0})

/-- **Beside the neighbour, the state is the two-token state.** -/
theorem beside_tokens : Scope.beside (tokensAt {1}) (tokensAt {0}) = twoTokens := by
  apply Scope.state_ext
  · rfl
  · decide
  · funext o
    show (if o ∈ ({1} : Finset ℕ) then c 1 else c 1) = c 1
    split <;> rfl

theorem consume_positive : Scope.Positive Examples.consume :=
  ⟨fun _ member => absurd member List.not_mem_nil, rfl⟩

/-- **The footprint of a firing of the program at a state of tokens is fixed.** -/
theorem footprint_fixed (W : Finset ℕ) (g : Firing ℕ E tokens PUnit.unit) :
    Scope.Fixed action (Scope.Footprint action (tokensAt W) g) := by
  rintro t (mentioned | opened) σ
  · exact tokens_fixed W t mentioned σ
  · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
    have isConsume : g.rule = Examples.consume := g.member
    rw [isConsume] at member
    rw [EveryControls.consume_ground t₀ member g.opening, EveryControls.consume_ground t₀ member σ]
    exact action.equivalence.refl _

/-- **The one-match firing stays admitted beside the neighbour**, by the composition theorem. -/
theorem one_stays : (takeAt 0 10).firing.Admits X (Scope.beside (tokensAt {1}) (tokensAt {0})) :=
  Scope.admits_beside action consume_positive (takeAt_admitted (by decide) (by decide))
    (by decide) (by decide) ⟨Subst.id atoms, fun _ member => absurd member List.not_mem_nil⟩
    (Scope.independent_of_fixed (footprint_fixed {0} (takeAt 0 10).firing))

/-- With one token, the bag that spends it is `every`. -/
theorem lone_every : Bag.AdmitsEvery X (tokensAt {0}) tokens lone := by
  refine ⟨(Bag.admitsOwn_single X (tokensAt {0}) (takeAt 0 10)).mpr
    (takeAt_admitted (by decide) (by decide)), fun m inside => m.member, List.nodup_singleton _,
    fun g _ admitted => ?_⟩
  obtain ⟨o, n, present, rule, selection⟩ := firing_shape g admitted
  have isZero : o = 0 := Finset.mem_singleton.mp present
  have key : firingKey g = (Examples.consume, [0], []) := by
    unfold firingKey
    rw [rule, selection, isZero]
  rw [key]
  exact List.mem_singleton_self _

/-- **`every` is switched off by the neighbour**: beside it, every bag admitted as `every` takes both
tokens, so the bag of the one match is not `every`. -/
theorem every_switched_off :
    Bag.AdmitsEvery X (tokensAt {0}) tokens lone ∧
      ¬ Bag.AdmitsEvery X (Scope.beside (tokensAt {1}) (tokensAt {0})) tokens lone := by
  refine ⟨lone_every, fun every => ?_⟩
  rw [beside_tokens] at every
  have lengths := every.length_eq (fun _ _ => ⟨Subst.id atoms⟩) spendBoth_every
  exact absurd lengths (by decide)

/-- With one token, `unique` fires. -/
theorem lone_unique : Bag.AdmitsUnique X (tokensAt {0}) tokens lone := ⟨lone_every, rfl⟩

/-- **`unique` is switched off by the neighbour**: beside it, `unique` has no step. -/
theorem unique_switched_off :
    Bag.AdmitsUnique X (tokensAt {0}) tokens lone ∧
      ¬ ∃ f : Bag ℕ E tokens PUnit.unit,
        Bag.AdmitsUnique X (Scope.beside (tokensAt {1}) (tokensAt {0})) tokens f := by
  refine ⟨lone_unique, fun ⟨f, unique⟩ => ?_⟩
  rw [beside_tokens] at unique
  have lengths := unique.1.length_eq (fun _ _ => ⟨Subst.id atoms⟩) spendBoth_every
  rw [unique.2] at lengths
  exact absurd lengths (by decide)

/-- **A maximal bag is switched off by the neighbour.** -/
theorem maximal_switched_off :
    Bag.AdmitsMaximal X (tokensAt {0}) lone ∧
      ¬ Bag.AdmitsMaximal X (Scope.beside (tokensAt {1}) (tokensAt {0})) lone := by
  refine ⟨lone_maximal, fun maximal => ?_⟩
  rw [beside_tokens] at maximal
  exact lone_not_maximal.2 maximal

end Neighbour

#print axioms Bag.AdmitsUnique.succ
#print axioms Bag.AdmitsUnique.key_eq
#print axioms Neighbour.neighbour_private
#print axioms Neighbour.beside_tokens
#print axioms Neighbour.one_stays
#print axioms Neighbour.lone_every
#print axioms Neighbour.every_switched_off
#print axioms Neighbour.unique_switched_off
#print axioms Neighbour.maximal_switched_off

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
