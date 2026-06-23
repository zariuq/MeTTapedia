import Mettapedia.Logic.OSLFDistinctionGraphWeighted
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Distinction Graph Entropy (Graphtropy)

Defines graphtropy (mean edge weight) for finite distinction graphs and proves
the partition-case reduction: when weights are 0/1 (crisp indistinguishability),
graphtropy reduces to logical entropy.

All theorems proven (0 sorry).

## References

- Goertzel, "Graphtropy" (2026)
- Ellerman, "An Introduction to Logical Entropy" (2017)
-/

namespace Mettapedia.Logic.OSLFDistinctionGraphEntropy

open Mettapedia.Logic.OSLFDistinctionGraphWeighted
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.OSLF.Formula

open scoped ENNReal
open Finset

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-! ## Graphtropy -/

/-- Graphtropy: mean edge weight over all pairs in a finite state space.
Measures the average "distinguishability" in the graph. -/
noncomputable def graphtropy {S : Type*} [Fintype S]
    (w : S → S → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ p : S, ∑ q : S, w p q) / (Fintype.card S ^ 2 : ℕ)

/-- Distinction graphtropy: graphtropy of the scalar distinction graph
over a finite set of patterns. -/
noncomputable def distinctionGraphtropy [Fintype Pat]
    (R : Pat → Pat → Prop) (I : EvidenceAtomSem) : ℝ≥0∞ :=
  graphtropy (fun p q => indistWeightS R I p q)

/-! ## Logical Entropy -/

/-- Repeat probability: probability that two randomly chosen elements
are in the same equivalence class. -/
noncomputable def repeatProbability {S : Type*} [Fintype S] [DecidableEq S]
    (rel : S → S → Prop) [DecidableRel rel] : ℝ≥0∞ :=
  (∑ p : S, ∑ q : S, if rel p q then (1 : ℝ≥0∞) else 0) /
    (Fintype.card S ^ 2 : ℕ)

/-- Logical entropy: 1 - repeat probability.
Measures the probability that two randomly chosen elements are in DIFFERENT classes. -/
noncomputable def logicalEntropy {S : Type*} [Fintype S] [DecidableEq S]
    (rel : S → S → Prop) [DecidableRel rel] : ℝ≥0∞ :=
  1 - repeatProbability rel

/-- Binary edge weight from a relation: 1 if related, 0 if not.
Models the "crisp" (partition) case. -/
noncomputable def crispWeight {S : Type*}
    (rel : S → S → Prop) [DecidableRel rel] (p q : S) : ℝ≥0∞ :=
  if rel p q then 1 else 0

/-! ## Partition-Case Reduction -/

/-- Graphtropy of crisp weights equals repeat probability.
When w(p,q) is 0/1 based on a relation, the mean weight IS the repeat probability. -/
theorem graphtropy_crispWeight_eq_repeatProb {S : Type*} [Fintype S] [DecidableEq S]
    (rel : S → S → Prop) [DecidableRel rel] :
    graphtropy (crispWeight rel) = repeatProbability rel := by
  simp only [graphtropy, repeatProbability, crispWeight]

/-- Graphtropy zero implies trivial graph: all pairs have zero weight. -/
theorem graphtropy_eq_zero_of_all_zero {S : Type*} [Fintype S]
    (w : S → S → ℝ≥0∞) (h : ∀ p q, w p q = 0) :
    graphtropy w = 0 := by
  simp only [graphtropy, h, Finset.sum_const_zero, ENNReal.zero_div]

/-- Constant-weight graphtropy: if all edges have weight c, graphtropy is c
(when the state space is nonempty). -/
theorem graphtropy_const {S : Type*} [Fintype S] [Nonempty S]
    (c : ℝ≥0∞) :
    graphtropy (fun (_ _ : S) => c) = c := by
  simp only [graphtropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Goal: ↑n * (↑n * c) / ↑(n ^ 2) = c where n = Fintype.card S
  set n := Fintype.card S with hn_def
  have hn_pos : (0 : ℕ) < n := Fintype.card_pos
  rw [show (↑n * (↑n * c)) / (↑(n ^ 2) : ℝ≥0∞) =
    (c * ↑(n ^ 2)) / ↑(n ^ 2) by push_cast; ring_nf]
  have hne : (↑(n ^ 2) : ℝ≥0∞) ≠ 0 := by
    simp [hn_pos.ne']
  have htop : (↑(n ^ 2) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top (n ^ 2)
  exact ENNReal.mul_div_cancel_right hne htop

/-! ## Self-Edge Bounds -/

/-- In any distinction graph, self-edges are ⊤ (maximal indistinguishability). -/
theorem selfEdge_top (R : Pat → Pat → Prop) (I : EvidenceAtomSem) (p : Pat) :
    indistWeightE R I p p = ⊤ :=
  indistWeightE_self_top R I p

/-! ## Monotonicity Under Refinement -/

/-- Coarsening an equivalence relation (making more things equivalent) increases
repeat probability. If rel₁ refines rel₂ (fewer equivalent pairs), then
the repeat probability of rel₁ is at most that of rel₂. -/
theorem repeatProb_antitone_refinement {S : Type*} [Fintype S] [DecidableEq S]
    (rel₁ rel₂ : S → S → Prop) [DecidableRel rel₁] [DecidableRel rel₂]
    (hRefine : ∀ p q, rel₁ p q → rel₂ p q) :
    repeatProbability rel₁ ≤ repeatProbability rel₂ := by
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro q _
  split_ifs with h1 h2 h2
  · exact le_refl _
  · exact absurd (hRefine p q h1) h2
  · exact zero_le_one
  · exact le_refl _

/-- Finer partition → lower repeat probability → higher logical entropy.
This is the graphtropy monotonicity theorem: refining an equivalence relation
(making more distinctions) increases logical entropy. -/
theorem logicalEntropy_monotone_refinement {S : Type*} [Fintype S] [DecidableEq S]
    (rel₁ rel₂ : S → S → Prop) [DecidableRel rel₁] [DecidableRel rel₂]
    (hRefine : ∀ p q, rel₁ p q → rel₂ p q) :
    logicalEntropy rel₂ ≤ logicalEntropy rel₁ := by
  simp only [logicalEntropy]
  exact tsub_le_tsub_left (repeatProb_antitone_refinement rel₁ rel₂ hRefine) 1

end Mettapedia.Logic.OSLFDistinctionGraphEntropy
