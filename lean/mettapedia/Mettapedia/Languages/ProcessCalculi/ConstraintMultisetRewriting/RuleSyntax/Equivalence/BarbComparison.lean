import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Controls

/-!
# A success row against the may-barbs, at one frame

The **success barb** is one may-barb: a row `1` may be present (`success`). It is one of the may-barbs,
so the congruence for all may-barbs is contained in the congruence for the success barb
(`Congruent.of_barbs`), and likewise for closed bisimilarity.

* **Closed, the success barb is blind** (`success_closed_blind`): a row `5` and a row `6`, with no rules,
  show no success and never move; they are closed bisimilar for the success barb, while the may-barb of
  `5` tells them apart (`may_tells_five_from_six`).
* **In context, it is not** (`success_separates_in_context`): the rule that reads a `5` and makes a `1`
  fires beside the row `5` only, so the success-barb congruence separates them. Here the contexts make
  the one success barb as discriminating as the pattern barbs; a general theorem that the two
  congruences coincide needs a success row no program can make, and is not claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame

open Interface (Frames)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)

/-- **The success barb**: a row `1` may be present. -/
def success : Unit → State Tm ℕ → Prop := fun _ s => MayBarb X (pat (c 1)) s

/-- The success barb is one of the may-barbs, so the may-barb congruence is contained in its
congruence. -/
theorem success_of_may {S T : Sys} (related : Cong S T) : Congruent X ℕ E success S T :=
  Congruent.of_barbs (obs := MayBarb X) (fun _ => pat (c 1)) (fun _ _ => Iff.rfl) related

theorem not_success_constant (n : ℕ) (different : n ≠ 1) :
    ¬ MayBarb X (pat (c 1)) (⟨PUnit.unit, [], {0}, fun _ => c n⟩ : State Tm ℕ) := by
  rintro ⟨o, -, b, σ, h, -, equated⟩
  have same : (c n : Term atoms) = c 1 := equated
  exact different (Term.const.inj same)

/-- **Closed, the success barb cannot tell a row `5` from a row `6`.** -/
theorem success_closed_blind : Bisimilar X ℕ E success ⟨∅, rowFive⟩ ⟨∅, rowSix⟩ := by
  refine ⟨fun A B => (A = ⟨∅, rowFive⟩ ∧ B = ⟨∅, rowSix⟩) ∨ (A = ⟨∅, rowSix⟩ ∧ B = ⟨∅, rowFive⟩),
    ⟨?_, ?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · rintro A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) β holds
    · exact absurd holds (not_success_constant 5 (by decide))
    · exact absurd holds (not_success_constant 6 (by decide))
  · rintro A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) A' moved
    · exact absurd ⟨A', moved⟩ (empty_stuck rowFive)
    · exact absurd ⟨A', moved⟩ (empty_stuck rowSix)

/-- **The may-barb of `5` tells them apart.** -/
theorem may_tells_five_from_six : MayBarb X (pat (c 5)) rowFive ∧ ¬ MayBarb X (pat (c 5)) rowSix := by
  refine ⟨⟨0, Finset.mem_singleton_self 0, PUnit.unit, Subst.id atoms, Subst.id atoms,
    Frames.models_nil (X := X) _, rfl⟩, ?_⟩
  rintro ⟨o, -, b, σ, h, -, equated⟩
  have same : (c 6 : Term atoms) = c 5 := equated
  exact absurd (Term.const.inj same) (by decide)

/-- Read a `5`, make a `1`. -/
def readFiveMakeOne : Rule Tm := ⟨PUnit.unit, ⟨[], [c 5], [], [], [c 1]⟩, []⟩

theorem readFive_moves : Moves ⟨∅ ∪ {readFiveMakeOne}, rowFive⟩ := by
  let f : Firing ℕ E (∅ ∪ {readFiveMakeOne}) rowFive.frame :=
    ⟨readFiveMakeOne, Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id atoms, ⟨[], [0], [1]⟩, []⟩
  have admitted : f.Admits X rowFive := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
      ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action rowFive f
      intro t member σ
      simp [f, readFiveMakeOne, Rule.terms] at member
      rcases member with rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, rowFive]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, rowFive]
      · intro q inside
        simp [f, Selection.commit] at inside
    · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++
          [(c 5, Subst.applyTerm (Subst.id atoms) (c 5))] ++ [] := inside
      simp only [List.nil_append, List.append_nil, List.mem_singleton] at unfolded
      subst unfolded
      rfl
    · intro check inside
      exact absurd inside List.not_mem_nil
    · intro q inside
      exact absurd inside List.not_mem_nil
  exact ⟨_, reduces_of_admits f admitted⟩

theorem readFive_stuck : ¬ Moves ⟨∅ ∪ {readFiveMakeOne}, rowSix⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = readFiveMakeOne := isRule
  subst same
  obtain ⟨-, ⟨-, -, -, readLength, -, -⟩, enabled, ⟨b, σ, solved⟩, -, -⟩ := (admits_iff _).mp admitted
  obtain ⟨o, read⟩ := List.length_eq_one_iff.mp readLength.symm
  have read' : selection.read = [o] := read
  have equated := Firing.read_solved _ solved (p := Subst.applyTerm ι (c 5)) (o := o) (by
    show (Subst.applyTerm ι (c 5), o) ∈ [Subst.applyTerm ι (c 5)].zip selection.read
    rw [read']
    exact List.mem_cons_self)
  have six : Subst.applyTerm σ (Subst.applyTerm ι (c 5)) =
      Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (c 6)) := equated
  exact absurd (Term.const.inj six) (by decide)

/-- **In context, the success-barb congruence separates a row `5` from a row `6`**: a rule context
turns the row `5` into a success. -/
theorem success_separates_in_context :
    Bisimilar X ℕ E success ⟨∅, rowFive⟩ ⟨∅, rowSix⟩ ∧
      ¬ Congruent X ℕ E success ⟨∅, rowFive⟩ ⟨∅, rowSix⟩ :=
  ⟨success_closed_blind, fun related =>
    readFive_stuck ((related.addRules {readFiveMakeOne}).moves readFive_moves)⟩

#print axioms success_of_may
#print axioms not_success_constant
#print axioms success_closed_blind
#print axioms may_tells_five_from_six
#print axioms readFive_moves
#print axioms readFive_stuck
#print axioms success_separates_in_context

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame
