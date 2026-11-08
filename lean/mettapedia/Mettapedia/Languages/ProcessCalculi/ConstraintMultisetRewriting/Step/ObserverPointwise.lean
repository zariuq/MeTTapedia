import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloControls

/-!
# Solution-indexed transport: the obstruction

Without a principal answer, pointwise equivalence (`Observation.PointwiseEquivalent`) relates states by
a renaming chosen at each solution. A transport whose isomorphisms carried such a renaming would move
a firing to a firing at the other state and relate the results again. In the one-frame instance this
fails already for one firing, and not only because the renamings disagree on what to select.

At `{1, 2}` labelled `x, y` and `{3, 4}` labelled `u, v`, under the knowledge `x = 0` whose two
solutions read `x, y, u, v` as `0, 1, 0, 1` and `0, 1, 1, 0` (`Observation.NonPrincipal`), the states
are pointwise equivalent. The firing that takes `1` with the pattern `x` keeps both solutions
(`left_result_solved`). Every firing of the same rule admitted at `{3, 4}` takes `3` or `4`, and
then keeps only one solution (`no_counterpart`). So pointwise equivalence is not a congruence for
firings (`pointwise_not_congruence`): no transport that moves firings by renaming, keeping the rule,
can carry it.

What exists instead is a **cover** (`counterparts_cover`): taking `3` is admitted and keeps the first
solution, taking `4` is admitted and keeps the second, and together they keep the solutions the
original firing keeps. A solution-indexed transport must therefore move a firing to a family of
firings indexed by a cover of the solutions, not to one firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

namespace NonPrincipalFirings

open AnnotatedRuns
open NonPrincipal

/-- The rule that takes one occurrence with the pattern `x`. -/
def takeRule : RuleInstance Atom := ⟨[.x], [], [], [], []⟩

/-- Take occurrence `o` with the pattern `x`. -/
def takeX (o : ℕ) : Firing Atom Choice ℕ := ⟨takeRule, [], ⟨[o], [], []⟩⟩

theorem knowledge_solutions (σ : Choice) (solved : action.Models σ knowledge) :
    σ = .first ∨ σ = .second := by
  cases σ with
  | identity => exact absurd solved not_identity
  | first => exact Or.inl rfl
  | second => exact Or.inr rfl

/-- The equations after taking `o` from a configuration with the knowledge `x = 0`. -/
theorem result_equations (o : ℕ) (C : Configuration Atom ℕ) (known : C.equations = knowledge) :
    ((takeX o).result label C).equations = [(.x, .zero), (.x, label o)] := by
  show (takeX o).selection.problem label (takeX o).rule C = _
  simp [Selection.problem, Selection.equations, known, knowledge, takeX, takeRule]

theorem models_pair_iff (σ : Choice) (t : Atom) :
    action.Models σ [(.x, .zero), (.x, t)] ↔ Choice.apply σ .x = Choice.apply σ .zero ∧
      Choice.apply σ .x = Choice.apply σ t := by
  constructor
  · intro solved
    exact ⟨solved _ List.mem_cons_self, solved _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · rintro ⟨first, second⟩ e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

/-- Taking `1` at `{1, 2}` is admitted. -/
theorem takeOne_valid : (takeX 1).Valid action label left := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨.first, ?_⟩, by simp [takeX, takeRule]⟩,
    by simp [takeX]⟩
  show action.Models .first ((takeX 1).result label left).equations
  rw [result_equations 1 left rfl, models_pair_iff]
  exact ⟨rfl, rfl⟩

/-- **Taking `1` keeps both solutions.** -/
theorem left_result_solved (σ : Choice) (solved : action.Models σ knowledge) :
    action.Models σ ((takeX 1).result label left).equations := by
  rw [result_equations 1 left rfl, models_pair_iff]
  exact ⟨solved _ (List.mem_singleton_self _), rfl⟩

/-- **No firing of the same rule at `{3, 4}` keeps the same solutions.** -/
theorem no_counterpart (g : Firing Atom Choice ℕ) (rule : g.rule = takeRule)
    (valid : g.Valid action label right) :
    ¬ action.Equivalent ((takeX 1).result label left).equations (g.result label right).equations := by
  intro same
  have length : g.selection.taken.length = 1 := by
    rw [← valid.firing.take_length, rule]
    rfl
  obtain ⟨o, single⟩ := List.length_eq_one_iff.mp length
  have present : o ∈ right.present :=
    valid.firing.occurrences.taken_subset (by simp [Selection.commit, single])
  have member : ((Atom.x, label o) : Atom × Atom) ∈ (g.result label right).equations := by
    show _ ∈ g.selection.problem label g.rule right
    simp [Selection.problem, Selection.equations, rule, single, takeRule]
  have three_or_four : o = 3 ∨ o = 4 := by simpa [right] using present
  rcases three_or_four with rfl | rfl
  · have held := (same .second).mp (left_result_solved .second second_solves) _ member
    have clash : Atom.zero = Atom.one := held
    exact absurd clash (by decide)
  · have held := (same .first).mp (left_result_solved .first first_solves) _ member
    have clash : Atom.zero = Atom.one := held
    exact absurd clash (by decide)

/-- **Pointwise equivalence is not a congruence for firings without a principal answer**: the two
states are pointwise equivalent, taking `1` is admitted at the first, and no firing of the same rule
admitted at the second has a result pointwise equivalent to its result. -/
theorem pointwise_not_congruence :
    PointwiseEquivalent action label ∅ left right ∧ (takeX 1).Valid action label left ∧
      ∀ g : Firing Atom Choice ℕ, g.rule = takeRule → g.Valid action label right →
        ¬ PointwiseEquivalent action label ∅ ((takeX 1).result label left) (g.result label right) :=
  ⟨pointwise, takeOne_valid, fun g rule valid equivalent => no_counterpart g rule valid equivalent.1⟩

theorem take_valid (o : ℕ) (present : o ∈ right.present) (σ : Choice)
    (solved : Choice.apply σ .x = Choice.apply σ (label o)) (known : action.Models σ knowledge) :
    (takeX o).Valid action label right := by
  have inside : o = 3 ∨ o = 4 := by simpa [right] using present
  refine ⟨⟨List.nodup_singleton o, List.nodup_nil, rfl, rfl, rfl, ?_, ⟨σ, ?_⟩, by simp [takeX, takeRule]⟩,
    by simp [takeX]⟩
  · rcases inside with rfl | rfl <;> decide
  · show action.Models σ ((takeX o).result label right).equations
    rw [result_equations o right rfl, models_pair_iff]
    exact ⟨known _ (List.mem_singleton_self _), solved⟩

/-- **The counterparts cover the solutions**: taking `3` is admitted and keeps the first solution,
taking `4` is admitted and keeps the second, and every solution the original firing keeps is kept by
one of them. -/
theorem counterparts_cover :
    (takeX 3).Valid action label right ∧ (takeX 4).Valid action label right ∧
      ∀ σ, action.Models σ ((takeX 1).result label left).equations →
        action.Models σ ((takeX 3).result label right).equations ∨
          action.Models σ ((takeX 4).result label right).equations := by
  refine ⟨take_valid 3 (by decide) .first rfl first_solves, take_valid 4 (by decide) .second rfl second_solves,
    fun σ solved => ?_⟩
  have known : action.Models σ knowledge := fun e member =>
    solved e (by
      rw [result_equations 1 left rfl]
      simp only [knowledge, List.mem_singleton] at member
      rw [member]
      exact List.mem_cons_self)
  rw [result_equations 3 right rfl, result_equations 4 right rfl, models_pair_iff, models_pair_iff]
  rcases knowledge_solutions σ known with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

end NonPrincipalFirings

#print axioms NonPrincipalFirings.takeOne_valid
#print axioms NonPrincipalFirings.left_result_solved
#print axioms NonPrincipalFirings.no_counterpart
#print axioms NonPrincipalFirings.pointwise_not_congruence
#print axioms NonPrincipalFirings.counterparts_cover

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
