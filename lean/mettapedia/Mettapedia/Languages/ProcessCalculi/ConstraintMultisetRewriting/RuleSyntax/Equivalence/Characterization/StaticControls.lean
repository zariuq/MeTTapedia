import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.StaticIff

/-!
# The static characterization at work: corollaries, a related pair, and one control per clause

## Finite programs are bounded (`bounded_of_finite`)

## The clauses (`static_iff_clauses`)

`Static s t` exactly when both knowledges are unsolvable, or some renaming `π` of identities sends the
present rows of `s` onto those of `t`, the two knowledges have the same solutions, `s.label o` and
`t.label (π o)` are equal at every solution, and the two states mention the same unknowns
(`mentions_iff_of_supports` turns the support clause into the last one).

## Corollaries of `static_iff` and `static_of_congruent`

The folder's separations of states become failures of one clause of `Static`:

* `tautology_observable_static`: the empty knowledge and `y = y` differ in support;
* `support_separates_static`: the same beside the rule that tells `x = 5` (a finite program);
* `count_separates_static`: one row `7` and two rows `7` differ in their rows;
* `tell_separates_static`: a row `x` and a row `y` differ in support.

## A related pair (`renamed_modulo_example`)

`x = 5` with a row `x` at identity `0`, and `5 = x` with a row `5` at identity `3`: different
knowledge, labels and identities, statically equivalent, hence congruent.

## Each clause of `Static` is needed, and the unsolvable disjunct

* **Unsolvable knowledge** (`unsolvable_example`): one row with knowledge `1 = 2`, and no row with
  knowledge `3 = 4`, are congruent, and no bijection relates their rows. A characterization without
  the first disjunct of `Static` is false.
* **Solutions** (`solutions_clause`): `x = x` and `x = 5`, no rows: the same rows and the same mentioned
  unknown, different solutions; not congruent.
* **Rows, by number** (`rows_count_clause`) and **by label** (`rows_label_clause`): one row `7`
  against two; one row `5` against one row `6`; the same knowledge and support; not congruent.
* **Support** (`support_clause`): the empty knowledge and `y = y`, no rows; the same solutions and
  rows; not congruent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong pat y tellX unmentioned mentionsY oneSeven twoSevens rowX rowY rowFive
  rowSix boundX contradictory)

/-! ## Finite programs are bounded -/

/-- **A finite program leaves the constants from a bound on unused.** -/
theorem bounded_of_finite {P : Program Tm} (finite : P.Finite) : Bounded P := by
  classical
  refine ⟨∑ r ∈ finite.toFinset, sizeBound r.terms, fun r member t inside k same => ?_⟩
  have one : size t ≤ sizeBound r.terms := size_le_sizeBound inside
  have two : sizeBound r.terms ≤ ∑ r ∈ finite.toFinset, sizeBound r.terms :=
    Finset.single_le_sum (f := fun r => sizeBound r.terms) (fun _ _ => Nat.zero_le _)
      (finite.mem_toFinset.mpr member)
  rw [same] at one
  simp only [size] at one
  omega

theorem bounded_singleton (r : Rule Tm) : Bounded {r} := bounded_of_finite (Set.finite_singleton r)

/-! ## Solvable, and not -/

theorem solvable_nil {s : State Tm ℕ} (empty : s.knowledge = []) :
    X.Solvable (a := PUnit.unit) s.knowledge :=
  ⟨PUnit.unit, Subst.id atoms, by rw [empty]; exact Frames.models_nil _⟩

/-- A static equivalence between states with solvable knowledge renames the present rows onto each
other. -/
theorem present_of_static {s t : State Tm ℕ} (solvable : X.Solvable (a := PUnit.unit) s.knowledge)
    (static : Static s t) : ∃ π : Equiv.Perm ℕ, s.present.map π.toEmbedding = t.present ∧
      Modulo X (renameState π s) t := by
  rcases static with ⟨unsolvable, -⟩ | ⟨π, modulo⟩
  · exact absurd solvable unsolvable
  · obtain ⟨K, ℓ, -, rfl⟩ := id modulo
    exact ⟨π, rfl, modulo⟩

/-- A static equivalence has the same support: for solvable knowledge, an unknown the one mentions
and the other does not breaks it. -/
theorem not_static_of_mentions {s t : State Tm ℕ}
    (solvable : X.Solvable (a := PUnit.unit) s.knowledge) {w : ℕ} (mentions : t.Mentions (.var w))
    (unmentioned : ¬ s.Mentions (.var w)) : ¬ Static s t := by
  intro static
  obtain ⟨π, -, K, ℓ, ⟨-, -, support⟩, same⟩ := present_of_static solvable static
  rw [← same] at support
  let φ : Subst atoms := fun _ => c 0
  let ψ : Subst atoms := fun v => if v = w then c 1 else c 0
  have agree := (support PUnit.unit φ ψ).mp
    (fun u mentioned => by
      cases u with
      | var v =>
          have other : v ≠ w := fun equal => unmentioned (equal ▸ (mentions_renameState π s _).mp
            mentioned)
          show (c 0 : Term atoms) = (if v = w then c 1 else c 0)
          rw [if_neg other]
      | const _ => rfl
      | app fn _ => exact nomatch fn)
  have atW : (c 0 : Term atoms) = (if w = w then c 1 else c 0) := agree (.var w) mentions
  rw [if_pos rfl] at atW
  exact absurd (Term.const.inj atW) (by decide)

/-- Two states whose supports agree for every pair of substitutions mention the same unknowns. -/
theorem mentions_iff_of_supports {s₁ s₂ : State Tm ℕ}
    (support : ∀ φ ψ : Subst atoms,
      Supports X (b := PUnit.unit) s₁ φ ψ ↔ Supports X (b := PUnit.unit) s₂ φ ψ)
    (w : ℕ) : s₁.Mentions (.var w) ↔ s₂.Mentions (.var w) := by
  have one : ∀ {u₁ u₂ : State Tm ℕ}, (∀ φ ψ : Subst atoms, Supports X (b := PUnit.unit) u₂ φ ψ →
      Supports X (b := PUnit.unit) u₁ φ ψ) → u₁.Mentions (.var w) → u₂.Mentions (.var w) := by
    intro u₁ u₂ back mentions
    by_contra unmentioned
    let φ : Subst atoms := fun _ => c 0
    let ψ : Subst atoms := fun v => if v = w then c 1 else c 0
    have agree := back φ ψ ((supports_iff_vars u₂ φ ψ).mpr fun v mentioned => by
      have other : v ≠ w := fun equal => unmentioned (equal ▸ mentioned)
      show (c 0 : Term atoms) = (if v = w then c 1 else c 0)
      rw [if_neg other])
    have atW : (c 0 : Term atoms) = (if w = w then c 1 else c 0) :=
      (supports_iff_vars u₁ φ ψ).mp agree w mentions
    rw [if_pos rfl] at atW
    exact absurd (Term.const.inj atW) (by decide)
  exact ⟨one fun φ ψ => (support φ ψ).mpr, one fun φ ψ => (support φ ψ).mp⟩

/-- **The static equivalence, clause by clause**: both knowledges unsolvable, or a renaming of the
identities under which the present rows correspond, the knowledges have the same solutions, each label
equals the label of its image at every solution, and the two states mention the same unknowns. -/
theorem static_iff_clauses (s t : State Tm ℕ) :
    Static s t ↔ (¬ X.Solvable s.knowledge ∧ ¬ X.Solvable t.knowledge) ∨
      ∃ π : Equiv.Perm ℕ, t.present = s.present.map π.toEmbedding ∧
        (∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ s.knowledge ↔
          X.Models (a := PUnit.unit) (b := PUnit.unit) σ t.knowledge) ∧
        (∀ o ∈ s.present, ∀ σ : Subst atoms,
          X.Models (a := PUnit.unit) (b := PUnit.unit) σ s.knowledge →
            Subst.applyTerm σ (s.label o) = Subst.applyTerm σ (t.label (π o))) ∧
        ∀ w, s.Mentions (.var w) ↔ t.Mentions (.var w) := by
  constructor
  · rintro (unsolvable | ⟨π, K, ℓ, ⟨equivalent, labels, support⟩, same⟩)
    · exact Or.inl unsolvable
    · subst same
      refine Or.inr ⟨π, rfl, fun σ => equivalent PUnit.unit σ, fun o present σ solved => ?_,
        fun w => ?_⟩
      · have agree : Subst.applyTerm σ (s.label (π.symm (π o))) = Subst.applyTerm σ (ℓ (π o)) :=
          labels (π o) (Finset.mem_map_of_mem _ present) PUnit.unit σ solved
        rwa [Equiv.symm_apply_apply] at agree
      · have both := mentions_iff_of_supports (fun φ ψ => support PUnit.unit φ ψ) w
        rwa [mentions_renameState] at both
  · rintro (unsolvable | ⟨π, present, equivalent, labels, mentions⟩)
    · exact Or.inl unsolvable
    · obtain ⟨tf, tk, tp, tl⟩ := t
      simp only at present
      subst present
      refine Or.inr ⟨π, tk, tl, ⟨fun _ σ => equivalent σ, fun o inside _ σ solved => ?_,
        fun b φ ψ => ?_⟩, rfl⟩
      · obtain ⟨o', present', rfl⟩ := Finset.mem_map.mp inside
        show Subst.applyTerm σ (s.label (π.symm (π o'))) = Subst.applyTerm σ (tl (π o'))
        rw [Equiv.symm_apply_apply]
        exact labels o' present' σ solved
      · cases b
        rw [supports_iff_vars, supports_iff_vars]
        constructor
        · intro agree w mentioned
          exact agree w ((mentions_renameState π s _).mpr ((mentions w).mpr mentioned))
        · intro agree w mentioned
          exact agree w ((mentions w).mp ((mentions_renameState π s _).mp mentioned))

/-! ## Corollaries: the folder's separations of states, by clause -/

/-- **The tautology `y = y` is observed because it is support**: a corollary of `static_iff`. -/
theorem tautology_observable_static : ¬ Cong ⟨∅, unmentioned⟩ ⟨∅, mentionsY⟩ := fun related =>
  not_static_of_mentions (solvable_nil rfl) (w := 1) (Or.inl (List.mem_singleton_self _))
    (by rintro (inside | inside | ⟨o, present, -⟩)
        · exact absurd inside List.not_mem_nil
        · exact absurd inside List.not_mem_nil
        · exact absurd present (Finset.notMem_empty o))
    ((static_iff _ _).mp related)

/-- **The support separation, as a corollary**: beside the rule that tells `x = 5`, a finite
program, congruent states have the same support. -/
theorem support_separates_static : ¬ Cong ⟨{tellX}, unmentioned⟩ ⟨{tellX}, mentionsY⟩ :=
  fun related => not_static_of_mentions (solvable_nil rfl) (w := 1)
    (Or.inl (List.mem_singleton_self _))
    (by rintro (inside | inside | ⟨o, present, -⟩)
        · exact absurd inside List.not_mem_nil
        · exact absurd inside List.not_mem_nil
        · exact absurd present (Finset.notMem_empty o))
    (static_of_congruent (bounded_singleton tellX) (bounded_singleton tellX) related)

/-- **One row `7` and two rows `7` differ in their rows.** -/
theorem rows_count_clause : ¬ Static oneSeven twoSevens := by
  intro static
  obtain ⟨π, present, -⟩ := present_of_static (solvable_nil rfl) static
  have cards := congrArg Finset.card present
  rw [Finset.card_map] at cards
  exact absurd cards (by decide)

/-- **A corollary**: one row `7` and two rows `7` are not congruent. -/
theorem count_separates_static : ¬ Cong ⟨∅, oneSeven⟩ ⟨∅, twoSevens⟩ := fun related =>
  rows_count_clause ((static_iff _ _).mp related)

/-- **A row `x` and a row `y` differ in support.** -/
theorem tell_separates_static : ¬ Cong ⟨∅, rowX⟩ ⟨∅, rowY⟩ := fun related =>
  not_static_of_mentions (solvable_nil rfl) (w := 1)
    (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩))
    (by
      rintro (inside | inside | ⟨o, -, same⟩)
      · exact absurd inside List.not_mem_nil
      · exact absurd inside List.not_mem_nil
      · have values : (0 : ℕ) = 1 := Term.var.inj same
        exact absurd values (by decide))
    ((static_iff _ _).mp related)

/-! ## A related pair -/

/-- `5 = x` with a row `5` at identity `3`. -/
def boundFive : State Tm ℕ := ⟨PUnit.unit, [(c 5, x)], {3}, fun _ => c 5⟩

/-- **Different knowledge, labels and identities, statically equivalent, hence congruent**, with every
program. -/
theorem renamed_modulo_example (P : Program Tm) :
    boundX ≠ boundFive ∧ Static boundX boundFive ∧ Cong ⟨P, boundX⟩ ⟨P, boundFive⟩ := by
  have static : Static boundX boundFive := by
    refine Or.inr ⟨Equiv.swap 0 3, [(c 5, x)], fun _ => c 5, ⟨fun b σ => ?_, ?_, fun b φ ψ => ?_⟩, ?_⟩
    · constructor
      · intro solved e inside
        have same : e = (c 5, x) := List.mem_singleton.mp inside
        subst same
        exact (solved (x, c 5) (List.mem_singleton_self _)).symm
      · intro solved e inside
        have same : e = (x, c 5) := List.mem_singleton.mp inside
        subst same
        exact (solved (c 5, x) (List.mem_singleton_self _)).symm
    · intro o _ b σ solved
      exact solved (x, c 5) (List.mem_singleton_self _)
    · cases b
      rw [supports_iff_vars, supports_iff_vars]
      have sameMentions : ∀ w, (renameState (Equiv.swap 0 3) boundX).Mentions (.var w) ↔
          (⟨(renameState (Equiv.swap 0 3) boundX).frame, [(c 5, x)],
            (renameState (Equiv.swap 0 3) boundX).present, fun _ => c 5⟩ :
            State Tm ℕ).Mentions (.var w) := by
        intro w
        rw [mentions_renameState]
        constructor
        · rintro (inside | inside | ⟨o, -, same⟩)
          · exact Or.inr (Or.inl (by simpa [boundX] using inside))
          · simp [boundX, c] at inside
          · exact Or.inr (Or.inl (by simpa [boundX] using same.symm))
        · rintro (inside | inside | ⟨o, -, same⟩)
          · simp [c] at inside
          · exact Or.inl (by simpa [boundX] using inside)
          · simp [c] at same
      constructor
      · intro agree w mentions
        exact agree w ((sameMentions w).mpr mentions)
      · intro agree w mentions
        exact agree w ((sameMentions w).mp mentions)
    · show (⟨PUnit.unit, [(c 5, x)], {3}, fun _ => c 5⟩ : State Tm ℕ) =
        ⟨PUnit.unit, [(c 5, x)], ({0} : Finset ℕ).map (Equiv.swap 0 3).toEmbedding, fun _ => c 5⟩
      rw [Finset.map_singleton, Equiv.toEmbedding_apply, Equiv.swap_apply_left]
  refine ⟨fun same => ?_, static, congruent_of_static P static⟩
  have rows := congrArg (fun s : State Tm ℕ => s.present) same
  simp [boundX, boundFive] at rows

/-! ## Each clause is needed -/

/-- No rows, knowledge `3 = 4`. -/
def contradictoryEmpty : State Tm ℕ := ⟨PUnit.unit, [(c 3, c 4)], ∅, fun _ => c 0⟩

theorem not_solvable_const {m n : ℕ} (different : m ≠ n) {K : EquationStore (Term atoms)}
    (inside : (c m, c n) ∈ K) : ¬ X.Solvable (a := PUnit.unit) K := by
  rintro ⟨b, σ, solved⟩
  have same : (Term.const m : Term atoms) = Term.const n := solved _ inside
  exact different (Term.const.inj same)

/-- **Unsolvable knowledge**: one row with `1 = 2` and no row with `3 = 4` are congruent, and no
bijection relates their rows. The first disjunct of `Static` is needed. -/
theorem unsolvable_example :
    Cong ⟨∅, contradictory⟩ ⟨∅, contradictoryEmpty⟩ ∧
      ¬ ∃ π : Equiv.Perm ℕ, contradictory.present.map π.toEmbedding = contradictoryEmpty.present := by
  refine ⟨(static_iff _ _).mpr (Or.inl ⟨not_solvable_const (by decide) (List.mem_singleton_self _),
    not_solvable_const (by decide) (List.mem_singleton_self _)⟩), ?_⟩
  rintro ⟨π, same⟩
  have cards := congrArg Finset.card same
  rw [Finset.card_map] at cards
  exact absurd cards (by decide)

/-- No rows, knowledge `x = x`. -/
def tautologyX : State Tm ℕ := ⟨PUnit.unit, [(x, x)], ∅, fun _ => c 0⟩

/-- No rows, knowledge `x = 5`. -/
def boundXEmpty : State Tm ℕ := ⟨PUnit.unit, [(x, c 5)], ∅, fun _ => c 0⟩

/-- **Solutions**: the same rows (none) and the same mentioned unknown `x`, different solutions; not
congruent. -/
theorem solutions_clause :
    (∀ w, tautologyX.Mentions (.var w) ↔ boundXEmpty.Mentions (.var w)) ∧
      ¬ X.Equivalent (a := PUnit.unit) tautologyX.knowledge boundXEmpty.knowledge ∧
      ¬ Cong ⟨∅, tautologyX⟩ ⟨∅, boundXEmpty⟩ := by
  have notEquivalent : ¬ X.Equivalent (a := PUnit.unit) tautologyX.knowledge boundXEmpty.knowledge := by
    intro equivalent
    have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (fun _ => c 6) tautologyX.knowledge :=
      fun e inside => by
        rw [show tautologyX.knowledge = [(x, x)] from rfl, List.mem_singleton] at inside
        subst inside
        rfl
    have five := (equivalent PUnit.unit (fun _ => c 6)).mp solved (x, c 5) (List.mem_singleton_self _)
    have six : (c 6 : Term atoms) = c 5 := five
    exact absurd (Term.const.inj six) (by decide)
  refine ⟨fun w => ?_, notEquivalent, fun related => notEquivalent (equivalent_of_congruent related)⟩
  constructor
  · rintro (inside | inside | ⟨o, present, -⟩)
    · exact Or.inl (by simpa [tautologyX, boundXEmpty] using inside)
    · exact Or.inl (by simpa [tautologyX, boundXEmpty] using inside)
    · exact absurd present (Finset.notMem_empty o)
  · rintro (inside | inside | ⟨o, present, -⟩)
    · exact Or.inl (by simpa [tautologyX, boundXEmpty] using inside)
    · simp [boundXEmpty, c] at inside
    · exact absurd present (Finset.notMem_empty o)

/-- **Rows, by label**: one row `5` and one row `6`, the same knowledge (none) and support (none);
not congruent. -/
theorem rows_label_clause : ¬ Static rowFive rowSix ∧ ¬ Cong ⟨∅, rowFive⟩ ⟨∅, rowSix⟩ := by
  have notStatic : ¬ Static rowFive rowSix := by
    intro static
    obtain ⟨π, -, K, ℓ, ⟨-, labels, -⟩, same⟩ := present_of_static (solvable_nil rfl) static
    have inside : π 0 ∈ (renameState π rowFive).present :=
      Finset.mem_map_of_mem _ (Finset.mem_singleton_self 0)
    have agree := labels (π 0) inside PUnit.unit (Subst.id atoms) (Frames.models_nil _)
    have labelSix : ℓ (π 0) = c 6 := by
      have h := congrArg (fun s : State Tm ℕ => s.label (π 0)) same
      exact h.symm
    have five : (c 5 : Term atoms) = c 6 := by
      have h : Subst.applyTerm (Subst.id atoms) (rowFive.label (π.symm (π 0))) =
          Subst.applyTerm (Subst.id atoms) (ℓ (π 0)) := agree
      rw [labelSix] at h
      exact h
    exact absurd (Term.const.inj five) (by decide)
  exact ⟨notStatic, fun related => notStatic ((static_iff _ _).mp related)⟩

/-- **Support**: the empty knowledge and `y = y`, no rows; the same solutions and rows; not
congruent. -/
theorem support_clause :
    X.Equivalent (a := PUnit.unit) unmentioned.knowledge mentionsY.knowledge ∧
      unmentioned.present = mentionsY.present ∧ ¬ Cong ⟨∅, unmentioned⟩ ⟨∅, mentionsY⟩ := by
  refine ⟨fun b σ => ⟨fun _ e inside => ?_, fun _ e inside => absurd inside List.not_mem_nil⟩, rfl,
    tautology_observable_static⟩
  rw [show mentionsY.knowledge = [(y, y)] from rfl, List.mem_singleton] at inside
  subst inside
  rfl

#print axioms bounded_of_finite
#print axioms present_of_static
#print axioms not_static_of_mentions
#print axioms mentions_iff_of_supports
#print axioms static_iff_clauses
#print axioms tautology_observable_static
#print axioms support_separates_static
#print axioms rows_count_clause
#print axioms count_separates_static
#print axioms tell_separates_static
#print axioms renamed_modulo_example
#print axioms unsolvable_example
#print axioms solutions_clause
#print axioms rows_label_clause
#print axioms support_clause

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
