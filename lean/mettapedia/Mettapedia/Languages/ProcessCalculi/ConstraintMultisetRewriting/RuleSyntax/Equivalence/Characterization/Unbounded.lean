import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Absorption

/-!
# The bound is sufficient, not the dividing line

`Bounded P` asks that the constants of the rules of `P` lie below a bound. `bounded_needed` shows
that the characterization of states fails for one program that is not bounded (every positive rule).
Here: programs that are not bounded and for which it holds.

* `deadAll`: one rule per numeral `k`, telling `k = k + 1`. It is not bounded
  (`not_bounded_deadAll`), none of its rules fires, and it may be dropped beside every program
  (`deadAll_cong`).
* `unbounded_characterized`: beside `deadAll`, and beside `deadAll` with the rule that makes `5` (a
  program that moves at every state with solvable knowledge), two states are congruent exactly when
  they are statically equivalent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Unbounded

open Interface (Frames)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong spawn)

/-- The rule that tells `k = k + 1`. -/
def deadAt (k : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[], [], [(c k, c (k + 1))], [], []⟩, []⟩

theorem deadAt_neverFires (k : ℕ) : NeverFires X (deadAt k) := by
  intro b h told
  have same : Subst.applyTerm h (c k) = Subst.applyTerm h (c (k + 1)) :=
    told (c k, c (k + 1)) (List.mem_singleton_self _)
  have values : k = k + 1 := Term.const.inj same
  omega

/-- One rule per numeral. -/
def deadAll : Program Tm := {r | ∃ k, r = deadAt k}

/-- **The program mentions every constant.** -/
theorem not_bounded_deadAll : ¬ Bounded deadAll := by
  rintro ⟨B, bound⟩
  have inside : c B ∈ (deadAt B).terms := by simp [deadAt, Rule.terms]
  exact absurd (bound (deadAt B) ⟨B, rfl⟩ (c B) inside B rfl) (lt_irrefl B)

theorem deadAll_answers : AnswersStatic deadAll ∅ ∧ AnswersStatic ∅ deadAll := by
  refine ⟨fun s f admitted => ?_, fun _ f _ => absurd f.member (Set.notMem_empty _)⟩
  obtain ⟨k, isDead⟩ := f.member
  exact absurd admitted (not_admits_of_neverFires (deadAt_neverFires k) f isDead)

/-- The program may be dropped beside every program, at every state. -/
theorem deadAll_cong (Q : Program Tm) (s : State Tm ℕ) : Cong ⟨deadAll ∪ Q, s⟩ ⟨∅ ∪ Q, s⟩ :=
  congruent_of_answersStatic deadAll_answers.1 deadAll_answers.2 Q s

/-- A program that mentions every constant and makes a row `5` at every state with solvable
knowledge. -/
def liveAll : Program Tm := deadAll ∪ {spawn}

theorem not_bounded_liveAll : ¬ Bounded liveAll := by
  rintro ⟨B, bound⟩
  exact not_bounded_deadAll ⟨B, fun r member => bound r (Or.inl member)⟩

/-- **The characterization of states holds beside programs that are not bounded.** -/
theorem unbounded_characterized :
    (¬ Bounded deadAll ∧ ∀ s t : State Tm ℕ, Cong ⟨deadAll, s⟩ ⟨deadAll, t⟩ ↔ Static s t) ∧
      (¬ Bounded liveAll ∧ ∀ s t : State Tm ℕ, Cong ⟨liveAll, s⟩ ⟨liveAll, t⟩ ↔ Static s t) := by
  refine ⟨⟨not_bounded_deadAll, fun s t => ⟨fun related => ?_, congruent_of_static deadAll⟩⟩,
    ⟨not_bounded_liveAll, fun s t => ⟨fun related => ?_, congruent_of_static liveAll⟩⟩⟩
  · have dropS := deadAll_cong ∅ s
    have dropT := deadAll_cong ∅ t
    rw [Set.union_empty, Set.union_empty] at dropS dropT
    exact (static_iff s t).mp (dropS.symm.trans (related.trans dropT))
  · have dropS := deadAll_cong {spawn} s
    have dropT := deadAll_cong {spawn} t
    exact (congruent_iff_static (bounded_union_singleton spawn) s t).mp
      (dropS.symm.trans (related.trans dropT))

#print axioms deadAt_neverFires
#print axioms not_bounded_deadAll
#print axioms deadAll_cong
#print axioms not_bounded_liveAll
#print axioms unbounded_characterized

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Unbounded
