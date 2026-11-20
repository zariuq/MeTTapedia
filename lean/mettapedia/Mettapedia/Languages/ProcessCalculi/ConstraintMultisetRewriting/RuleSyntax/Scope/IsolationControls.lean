import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Isolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.CompositionControls

/-!
# Controls for isolation: a shared unknown crosses spaces, a private one does not

Two spaces: the left holds row `0`, the right holds row `1`. Two positive rules: `tellOne` reads any
row and tells it equal to `1`, `tellTwo` tells it equal to `2`.

* **A shared unknown crosses spaces** (`shared_unknown_crosses_spaces`): both rows are labelled by
  the same unknown `x`. The two footprints are not independent; the right space's read-and-tell is
  admitted, and refused after the left space's read-and-tell has bound `x`. This is the tree's
  `Spaces.Controls.shared_variable_crosses_spaces` on the rule syntax, where rule unknowns are always
  fresh and only rows and knowledge can share an unknown.
* **Private unknowns are isolated** (`private_unknowns_isolated`): with the right row labelled by its
  own unknown `x₇`, `isolation` applies, and the right space's read-and-tell is admitted before and
  after the left space fires.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.IsolationControls

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Examples (Tm X E x c shift everywhere)
open CompositionControls (freeVars_var freeVars_const)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- Read any row and tell it equal to `n`. -/
def tellRow (n : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [(x, c n)], [], []⟩, []⟩

theorem tellRow_positive (n : ℕ) : Positive (tellRow n) :=
  ⟨fun _ member => absurd member List.not_mem_nil, rfl⟩

theorem tellRow_terms {n : ℕ} {t : Term atoms} (member : t ∈ (tellRow n).terms) : t = x ∨ t = c n := by
  simp only [tellRow, Rule.terms, List.map_cons, List.map_nil, List.flatMap_nil, List.nil_append,
    List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The program of the two rules. -/
def spacesProgram : Program Tm := {tellRow 1, tellRow 2}

/-- The left space: row `0` labelled `x`. -/
def leftSpace : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => x⟩

/-- The right space sharing `x`: row `1` labelled `x`. -/
def rightShared : State Tm ℕ := ⟨PUnit.unit, [], {1}, fun _ => x⟩

/-- The right space with its own unknown: row `1` labelled `x₇`. -/
def rightOwn : State Tm ℕ := ⟨PUnit.unit, [], {1}, fun _ => Term.var 7⟩

/-- The opening that renames each unknown `n` to `n + 2`. -/
def shiftTwo : Subst atoms := fun v => Term.var (v + 2)

/-- The left read-and-tell: row `0`, told `1`, opened as `x₁`. -/
def oneAt : Firing ℕ E spacesProgram PUnit.unit := ⟨tellRow 1, Or.inl rfl, PUnit.unit, shift, ⟨[], [0], []⟩, []⟩

/-- The right read-and-tell: row `1`, told `2`, opened as `x₂`. -/
def twoAt : Firing ℕ E spacesProgram PUnit.unit :=
  ⟨tellRow 2, Or.inr rfl, PUnit.unit, shiftTwo, ⟨[], [1], []⟩, []⟩

theorem apart_shared : Disjoint leftSpace.present rightShared.present := by
  show Disjoint ({0} : Finset ℕ) ({1} : Finset ℕ)
  exact Finset.disjoint_singleton.mpr (by decide)

theorem apart_own : Disjoint leftSpace.present rightOwn.present := by
  show Disjoint ({0} : Finset ℕ) ({1} : Finset ℕ)
  exact Finset.disjoint_singleton.mpr (by decide)

/-- The two shared spaces side by side, written out. -/
def bothX : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, fun _ => x⟩

theorem bothX_eq : beside leftSpace rightShared = bothX := by
  apply state_ext
  · rfl
  · show ({0} ∪ {1} : Finset ℕ) = {0, 1}
    decide
  · funext o
    show (if o ∈ ({0} : Finset ℕ) then x else x) = x
    split_ifs <;> rfl

theorem bothX_mentions {t : Term atoms} (mentioned : bothX.Mentions t) : t = x := by
  rcases mentioned with first | second | ⟨o, -, rfl⟩
  · simp [bothX] at first
  · simp [bothX] at second
  · rfl

theorem oneAt_admitted_both : (step X ℕ E spacesProgram).Admits (s := bothX) oneAt := by
  refine (admits_iff oneAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 1 then h 0 else g v, fun t mentioned => ?_, fun t member => ?_⟩
    · rw [bothX_mentions mentioned]
      rfl
    · rcases tellRow_terms member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [oneAt, bothX, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 1, fun e member => ?_⟩
    have known : oneAt.information X bothX = [((Term.var 1 : Term atoms), x), ((Term.var 1 : Term atoms), c 1)] :=
      rfl
    rw [known] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [oneAt, tellRow, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [oneAt, tellRow, Firing.collectOpened] at member

theorem twoAt_admitted_both : (step X ℕ E spacesProgram).Admits (s := bothX) twoAt := by
  refine (admits_iff twoAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 2 then h 0 else g v, fun t mentioned => ?_, fun t member => ?_⟩
    · rw [bothX_mentions mentioned]
      rfl
    · rcases tellRow_terms member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [twoAt, bothX, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 2, fun e member => ?_⟩
    have known : twoAt.information X bothX = [((Term.var 2 : Term atoms), x), ((Term.var 2 : Term atoms), c 2)] :=
      rfl
    rw [known] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [twoAt, tellRow, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [twoAt, tellRow, Firing.collectOpened] at member

theorem twoAt_refused_after : ¬ (step X ℕ E spacesProgram).Admits (s := oneAt.result X bothX) twoAt := by
  intro admitted
  obtain ⟨-, -, -, ⟨_, σ, solved⟩, -, -⟩ := (admits_iff (s := oneAt.result X bothX) twoAt).mp admitted
  have known : twoAt.information X (oneAt.result X bothX) =
      [((Term.var 1 : Term atoms), x), ((Term.var 1 : Term atoms), c 1), ((Term.var 2 : Term atoms), x),
        ((Term.var 2 : Term atoms), c 2)] := rfl
  rw [known] at solved
  have one : σ 1 = σ 0 := solved ((Term.var 1 : Term atoms), x) (by simp)
  have told : σ 1 = c 1 := solved ((Term.var 1 : Term atoms), c 1) (by simp)
  have two : σ 2 = σ 0 := solved ((Term.var 2 : Term atoms), x) (by simp)
  have toldTwo : σ 2 = c 2 := solved ((Term.var 2 : Term atoms), c 2) (by simp)
  have same : (c 1 : Term atoms) = c 2 := told.symm.trans (one.trans (two.symm.trans toldTwo))
  exact absurd (Term.const.inj same) (by decide)

/-- **A shared unknown crosses spaces**: the two footprints share `x`, the right read-and-tell is
admitted beside the left space, and refused after the left read-and-tell has fired. -/
theorem shared_unknown_crosses_spaces :
    ¬ Independent action (Footprint action leftSpace oneAt) (Footprint action rightShared twoAt) ∧
      (step X ℕ E spacesProgram).Admits (s := beside leftSpace rightShared) twoAt ∧
      ¬ (step X ℕ E spacesProgram).Admits (s := oneAt.result X (beside leftSpace rightShared)) twoAt := by
  rw [bothX_eq]
  refine ⟨?_, twoAt_admitted_both, twoAt_refused_after⟩
  exact not_independent_of_shared (a := c 0) (b := c 1) (v := 0) (by simp [c])
    ⟨x, Or.inl (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)), by simp [x, Term.freeVars]⟩
    ⟨x, Or.inl (Or.inr (Or.inr ⟨1, Finset.mem_singleton_self 1, rfl⟩)), by simp [x, Term.freeVars]⟩

/-! ## Private unknowns are isolated -/

theorem leftSpace_mentions {t : Term atoms} (mentioned : leftSpace.Mentions t) : t = x := by
  rcases mentioned with first | second | ⟨o, -, rfl⟩
  · simp [leftSpace] at first
  · simp [leftSpace] at second
  · rfl

theorem rightOwn_mentions {t : Term atoms} (mentioned : rightOwn.Mentions t) :
    t = (Term.var 7 : Term atoms) := by
  rcases mentioned with first | second | ⟨o, -, rfl⟩
  · simp [rightOwn] at first
  · simp [rightOwn] at second
  · rfl

theorem oneAt_admitted_left : (step X ℕ E spacesProgram).Admits (s := leftSpace) oneAt := by
  refine (admits_iff oneAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 1 then h 0 else g v, fun t mentioned => ?_, fun t member => ?_⟩
    · rw [leftSpace_mentions mentioned]
      rfl
    · rcases tellRow_terms member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [oneAt, leftSpace, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 1, fun e member => ?_⟩
    have known : oneAt.information X leftSpace =
        [((Term.var 1 : Term atoms), x), ((Term.var 1 : Term atoms), c 1)] := rfl
    rw [known] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [oneAt, tellRow, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [oneAt, tellRow, Firing.collectOpened] at member

theorem leftFootprint_unknowns {v : ℕ} (inside : UnknownsOf (Footprint action leftSpace oneAt) v) :
    v = 0 ∨ v = 1 := by
  obtain ⟨t, foot, member⟩ := inside
  rcases foot with mentioned | opened
  · rw [leftSpace_mentions mentioned] at member
    exact Or.inl (freeVars_var 0 member)
  · obtain ⟨t₀, member₀, rfl⟩ := List.mem_map.mp opened
    rcases tellRow_terms member₀ with rfl | rfl
    · exact Or.inr (freeVars_var 1 member)
    · exact (freeVars_const 1 member).elim

theorem rightFootprint_unknowns {v : ℕ} (inside : UnknownsOf (Footprint action rightOwn twoAt) v) :
    v = 7 ∨ v = 2 := by
  obtain ⟨t, foot, member⟩ := inside
  rcases foot with mentioned | opened
  · rw [rightOwn_mentions mentioned] at member
    exact Or.inl (freeVars_var 7 member)
  · obtain ⟨t₀, member₀, rfl⟩ := List.mem_map.mp opened
    rcases tellRow_terms member₀ with rfl | rfl
    · exact Or.inr (freeVars_var 2 member)
    · exact (freeVars_const 2 member).elim

theorem rightOwn_unknowns {v : ℕ} (inside : UnknownsOf rightOwn.Mentions v) : v = 7 := by
  obtain ⟨t, mentioned, member⟩ := inside
  rw [rightOwn_mentions mentioned] at member
  exact freeVars_var 7 member

/-- **Private unknowns are isolated**: with the right row labelled by its own unknown, the left
read-and-tell is admitted beside the right space, and the right read-and-tell is admitted beside the
left space exactly when it is admitted after the left one has fired. -/
theorem private_unknowns_isolated :
    (step X ℕ E spacesProgram).Admits (s := beside leftSpace rightOwn) oneAt ∧
      ((step X ℕ E spacesProgram).Admits (s := beside leftSpace rightOwn) twoAt ↔
        (step X ℕ E spacesProgram).Admits (s := oneAt.result X (beside leftSpace rightOwn)) twoAt) :=
  isolation apart_own ⟨everywhere 0, fun e member => by cases member⟩
    ⟨everywhere 0, fun e member => by cases member⟩ (tellRow_positive 1) (tellRow_positive 2)
    oneAt_admitted_left (by simp [oneAt])
    (by
      rintro o (inside | inside)
      · simp [twoAt] at inside
      · simp only [twoAt, List.mem_singleton] at inside
        subst inside
        exact Finset.mem_singleton_self 1)
    (by simp [twoAt])
    (by
      apply independent_of_disjoint
      intro v inC inFoot
      have seven := rightOwn_unknowns inC
      rcases leftFootprint_unknowns inFoot with zero | one <;> omega)
    (by
      apply independent_of_disjoint
      intro v inLeft inRight
      rcases leftFootprint_unknowns inLeft with zero | one <;>
        rcases rightFootprint_unknowns inRight with seven | two <;> omega)

#print axioms shared_unknown_crosses_spaces
#print axioms private_unknowns_isolated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.IsolationControls
