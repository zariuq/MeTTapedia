/-
# Standard Combinatorial Characterization of R(k,l)

The definition `ramseyNumber k l` (from RamseyDef.lean) uses `sInf`.
This file formalizes the *classical textbook characterization* as found in:

  Radziszowski, S. P. "Small Ramsey Numbers."
  Electronic Journal of Combinatorics, Dynamic Survey DS1, 1994 (updated regularly).

  Definition: R(k,l) is the **least positive integer n** such that
  for every graph G of order n, G contains K_k as a subgraph or
  the complement of G contains K_l as a subgraph.

In graph-theoretic terms: every n-vertex graph has a k-clique or l-independent set.

We prove `IsRamseyNumber k l n ↔ n = ramseyNumber k l`, establishing that the
`sInf` definition is exactly the classical least-element characterization.

## Notes (LLM)
- `Nat.sInf_def` : `sInf s = Nat.find h` (when `s.Nonempty`)
- `Nat.sInf_mem` : `s.Nonempty → sInf s ∈ s`
- `Nat.sInf_le`  : `m ∈ s → sInf s ≤ m`
- For `ramseyNumber_upper`, we avoid `rw [ramseyNumber_eq_sInf]` in the goal
  because `G : SimpleGraph (Fin (ramseyNumber k l))` depends on `ramseyNumber k l`.
  Instead we rewrite in the hypothesis `hmem`.
- `HasRamseyProperty k l G` does not use the `DecidableRel G.Adj` instance
  in its body, so instance choice does not affect the truth of the proposition
  (proved as `hasRamseyProperty_instIndep`).
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Ramsey36.RamseyDef
import Ramsey36.Basic
import Ramsey36.MainTheorem

open SimpleGraph

/-! ## Instance Independence of HasRamseyProperty -/

/-- `HasRamseyProperty k l G` is independent of the `DecidableRel G.Adj` instance.
    The definition body `(∃ s, G.IsNClique k s) ∨ (∃ s, G.IsNIndepSet l s)`
    is purely propositional and does not refer to the instance. -/
lemma hasRamseyProperty_instIndep {V : Type*}
    (k l : ℕ) (G : SimpleGraph V)
    (inst1 inst2 : DecidableRel G.Adj) :
    @HasRamseyProperty V k l G inst1 ↔ @HasRamseyProperty V k l G inst2 :=
  Iff.rfl

/-! ## The Ramsey Set -/

/-- The Ramsey set: all positive `n` for which every `n`-vertex graph has the
    Ramsey property.  This is exactly the set whose infimum is `ramseyNumber k l`. -/
private def ramseySet (k l : ℕ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    HasRamseyProperty k l G}

private lemma ramseyNumber_eq_sInf (k l : ℕ) :
    ramseyNumber k l = sInf (ramseySet k l) := rfl

/-! ## The Textbook Definition (Radziszowski 1994) -/

/-- **Classical combinatorial characterization** of Ramsey numbers.

    `IsRamseyNumber k l n` holds iff `n` is the *least positive integer* such that
    every graph on `n` vertices contains either a `k`-clique or an `l`-independent set.

    This matches Radziszowski's *Small Ramsey Numbers* survey definition exactly:
    - Condition (i):   `n > 0`
    - Condition (ii):  every `n`-vertex graph has the Ramsey property (upper bound)
    - Condition (iii): for each `0 < m < n`, some `m`-vertex graph lacks it (lower/witness bound)

    Condition (iii) is critical: it certifies that `n` is truly *minimal*,
    ruling out any smaller Ramsey number. -/
def IsRamseyNumber (k l n : ℕ) : Prop :=
  0 < n ∧
  (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty k l G) ∧
  (∀ m : ℕ, 0 < m → m < n →
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj), ¬ HasRamseyProperty k l G)

/-! ## Key Properties of `ramseyNumber` Derived from `Nat.sInf` -/

/-- When the Ramsey set is nonempty, `ramseyNumber k l` is positive. -/
lemma ramseyNumber_pos {k l : ℕ} (h_ne : (ramseySet k l).Nonempty) :
    0 < ramseyNumber k l := by
  have hmem : sInf (ramseySet k l) ∈ ramseySet k l := Nat.sInf_mem h_ne
  rw [← ramseyNumber_eq_sInf] at hmem
  exact hmem.1

-- Sanity: ramseyNumber_pos doesn't need h_ne once we have ramseySet_3_6_nonempty'.
-- The warning about `h_ne` in ramseyNumber_pos came from the `rw ... at hmem`
-- leaving h_ne unused *in the old body*; current body uses it via Nat.sInf_mem h_ne.

/-- When the Ramsey set is nonempty, every graph on `ramseyNumber k l` vertices
    has the Ramsey property. -/
lemma ramseyNumber_upper {k l : ℕ} (h_ne : (ramseySet k l).Nonempty)
    (G : SimpleGraph (Fin (ramseyNumber k l))) [DecidableRel G.Adj] :
    HasRamseyProperty k l G := by
  -- Avoid rewriting in goal (G depends on ramseyNumber k l); rewrite in hmem instead.
  have hmem : sInf (ramseySet k l) ∈ ramseySet k l := Nat.sInf_mem h_ne
  rw [← ramseyNumber_eq_sInf] at hmem
  exact hmem.2 G

/-- For any `0 < m < ramseyNumber k l`, some `m`-vertex graph lacks the Ramsey property. -/
lemma ramseyNumber_lower {k l : ℕ}
    {m : ℕ} (h_pos : 0 < m) (h_lt : m < ramseyNumber k l) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj), ¬ HasRamseyProperty k l G := by
  rw [ramseyNumber_eq_sInf] at h_lt
  -- m < sInf (ramseySet k l), so m ∉ ramseySet k l
  have hm_not_mem : m ∉ ramseySet k l :=
    fun hm => Nat.not_lt.mpr (Nat.sInf_le hm) h_lt
  -- Since m ∉ ramseySet and m > 0, ∃ G without the Ramsey property
  simp only [ramseySet, Set.mem_setOf_eq, not_and] at hm_not_mem
  push_neg at hm_not_mem
  obtain ⟨G, inst, hG⟩ := hm_not_mem h_pos
  exact ⟨G, inst, hG⟩

/-! ## Main Equivalence Theorem -/

/-- **Equivalence of the `sInf` and textbook definitions.**

    When the Ramsey set is nonempty, `n = ramseyNumber k l` if and only if
    `n` satisfies the classical Radziszowski characterization:
    `n > 0`, every `n`-vertex graph has the Ramsey property, and
    for each `0 < m < n`, some `m`-vertex graph witnesses failure. -/
theorem isRamseyNumber_iff_eq_ramseyNumber {k l : ℕ}
    (h_ne : (ramseySet k l).Nonempty) {n : ℕ} :
    IsRamseyNumber k l n ↔ n = ramseyNumber k l := by
  constructor
  · -- Forward: classical characterization → n = ramseyNumber k l
    intro ⟨h_pos, h_upper, h_lower⟩
    -- n ∈ ramseySet k l (since h_upper holds)
    have hn_mem : n ∈ ramseySet k l := ⟨h_pos, fun G _inst => h_upper G⟩
    -- sInf ≤ n, i.e. ramseyNumber k l ≤ n
    have h_inf_le_n : ramseyNumber k l ≤ n := by
      rw [ramseyNumber_eq_sInf]; exact Nat.sInf_le hn_mem
    -- n ≤ ramseyNumber k l: if ramseyNumber k l < n, by h_lower there is
    -- a witness G on ramseyNumber k l vertices lacking the Ramsey property,
    -- contradicting ramseyNumber_upper.
    apply Nat.le_antisymm _ h_inf_le_n
    by_contra h_lt
    push_neg at h_lt
    obtain ⟨G, _inst, hG⟩ := h_lower _ (ramseyNumber_pos h_ne) h_lt
    exact hG (ramseyNumber_upper h_ne G)
  · -- Backward: n = ramseyNumber k l → classical characterization
    intro h_eq; subst h_eq
    exact ⟨ramseyNumber_pos h_ne,
           fun G _inst => ramseyNumber_upper h_ne G,
           fun m h_pos h_lt => ramseyNumber_lower h_pos h_lt⟩

/-! ## Nonemptiness of the Ramsey Set for (3,6) -/

/-- 18 belongs to the Ramsey set for (3,6): the upper bound proof. -/
private lemma ramseySet_3_6_mem_18 : 18 ∈ ramseySet 3 6 :=
  ⟨by norm_num, fun G _inst => hasRamseyProperty_3_6_18.2 G⟩

/-- The Ramsey set for (3,6) is nonempty (witnessed by 18). -/
lemma ramseySet_3_6_nonempty' : (ramseySet 3 6).Nonempty :=
  ⟨18, ramseySet_3_6_mem_18⟩

/-! ## Final Instantiation: R(3,6) = 18 in Textbook Form -/

/-- **Main result in classical form.**

    18 is the Ramsey number R(3,6) in the classical combinatorial sense:
    it is the *least positive integer* n such that every n-vertex graph
    contains a triangle or a 6-independent set.

    This is the formulation in Radziszowski's survey and Cariolaro's proof. -/
theorem isRamseyNumber_3_6_18 : IsRamseyNumber 3 6 18 :=
  (isRamseyNumber_iff_eq_ramseyNumber ramseySet_3_6_nonempty').mpr
    ramsey_three_six.symm
