import Mettapedia.InformationTheory.KnowledgeQuantification.Basic
import Mettapedia.Logic.ProofSharingBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Theoretical knowledge of shared and unshared proofs

D. Fanelli, *A theory and methodology to quantify knowledge*, R. Soc. open sci. 6: 181055
(2019), §3.1, values a proved theorem as lossless knowledge, `K = η`, whose theory is the
proof: the value of a theory falls with its length and rises with its uses.

`Logic.ProofSharingBounds` proves that in its doubling calculus every accepted tree proof of
level `n` has at least `2^n` nodes (`tree_lower_bound`), while one shared certificate cites
each lemma twice and stays within `4 (n + 1)^2` symbols (`dag_input_bound`).  With the
certificate as the theory and an explanandum of `E` units of certificate size:

* `tree_knowledge_le`: every accepted tree proof yields at most `E / (E + 2^n)`;
* `dag_knowledge_ge`: the shared certificate yields at least `E / (E + 4 (n + 1)^2)`;
* `dag_knowledge_gt_tree`: from level 9 on, the shared certificate yields strictly more
  knowledge than every accepted tree proof, whatever the explanandum;
* `tendsto_tree_knowledge` and `tendsto_dag_knowledge`: settling `(n + 1)^3` uses, tree proofs
  tend to no knowledge and the shared certificate to full knowledge.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

open Filter Topology
open Mettapedia.Logic.ProofSharingBounds
open Mettapedia.OSLF.NativeTypes.Certificates

namespace Budget

/-- Lossless, input-free knowledge with a theory of a given length is antitone in the length. -/
theorem lossless_knowledge_le_of_le {E L L' : ℝ} (hE : 0 < E) (hL : 0 ≤ L) (hLL' : L ≤ L') :
    (⟨E, 0, 0, L'⟩ : Budget).knowledge ≤ E / (E + L) := by
  unfold knowledge explained total
  dsimp only
  rw [sub_zero, add_zero]
  exact div_le_div_of_nonneg_left hE.le (by linarith) (by linarith)

/-- Every accepted tree proof of level `n` yields at most `E / (E + 2^n)`. -/
theorem tree_knowledge_le (level : ℕ) (tree : Tree presentation)
    (accepted : treeSystem.check level tree = true) {E : ℝ} (hE : 0 < E) :
    (⟨E, 0, 0, (treeSystem.certificateSize tree : ℝ)⟩ : Budget).knowledge ≤
      E / (E + 2 ^ level) := by
  have hlow : ((2 ^ level : ℕ) : ℝ) ≤ (treeSystem.certificateSize tree : ℝ) := by
    exact_mod_cast tree_lower_bound level tree accepted
  have hcast : ((2 ^ level : ℕ) : ℝ) = (2 : ℝ) ^ level := by push_cast; ring
  rw [hcast] at hlow
  exact lossless_knowledge_le_of_le hE (by positivity) hlow

theorem dag_certificateSize_le (level : ℕ) :
    dagSystem.certificateSize (certificate level) ≤ 4 * (level + 1) ^ 2 := by
  have h := dag_input_bound level
  change level + 1 + certificateSize (certificate level) ≤ 4 * (level + 1) ^ 2 at h
  change certificateSize (certificate level) ≤ 4 * (level + 1) ^ 2
  omega

/-- The shared certificate of level `n` yields at least `E / (E + 4 (n + 1)^2)`. -/
theorem dag_knowledge_ge (level : ℕ) {E : ℝ} (hE : 0 < E) :
    E / (E + 4 * ((level : ℝ) + 1) ^ 2) ≤
      (⟨E, 0, 0, (dagSystem.certificateSize (certificate level) : ℝ)⟩ : Budget).knowledge := by
  have hsize : (dagSystem.certificateSize (certificate level) : ℝ) ≤
      4 * ((level : ℝ) + 1) ^ 2 := by
    exact_mod_cast dag_certificateSize_le level
  unfold knowledge explained total
  dsimp only
  rw [sub_zero, add_zero]
  exact div_le_div_of_nonneg_left hE.le
    (by have := Nat.cast_nonneg (α := ℝ) (dagSystem.certificateSize (certificate level))
        linarith) (by linarith)

theorem four_mul_sq_lt_two_pow {n : ℕ} (hn : 9 ≤ n) : 4 * (n + 1) ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ 2 n]
      nlinarith [ih]

/-- **Sharing beats trees.**  From level 9 on, the shared certificate yields strictly more
knowledge than every accepted tree proof. -/
theorem dag_knowledge_gt_tree {level : ℕ} (hlevel : 9 ≤ level)
    (tree : Tree presentation) (accepted : treeSystem.check level tree = true)
    {E : ℝ} (hE : 0 < E) :
    (⟨E, 0, 0, (treeSystem.certificateSize tree : ℝ)⟩ : Budget).knowledge <
      (⟨E, 0, 0, (dagSystem.certificateSize (certificate level) : ℝ)⟩ : Budget).knowledge := by
  have hgap : 4 * ((level : ℝ) + 1) ^ 2 < (2 : ℝ) ^ level := by
    exact_mod_cast four_mul_sq_lt_two_pow hlevel
  calc (⟨E, 0, 0, (treeSystem.certificateSize tree : ℝ)⟩ : Budget).knowledge
      ≤ E / (E + 2 ^ level) := tree_knowledge_le level tree accepted hE
    _ < E / (E + 4 * ((level : ℝ) + 1) ^ 2) :=
        div_lt_div_of_pos_left hE (by positivity) (by linarith)
    _ ≤ _ := dag_knowledge_ge level hE

/-- Settling `(n + 1)^3` uses, any accepted tree proofs yield knowledge tending to zero. -/
theorem tendsto_tree_knowledge (trees : ℕ → Tree presentation)
    (accepted : ∀ level, treeSystem.check level (trees level) = true) :
    Tendsto (fun level : ℕ =>
        (⟨((level : ℝ) + 1) ^ 3, 0, 0, (treeSystem.certificateSize (trees level) : ℝ)⟩ :
          Budget).knowledge) atTop (𝓝 0) := by
  have hratio : Tendsto (fun level : ℕ => ((level : ℝ) + 1) ^ 3 / (2 : ℝ) ^ level) atTop
      (𝓝 0) := by
    have hpoly := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 2)
    have hshift := hpoly.comp (tendsto_add_atTop_nat 1)
    have hscaled := hshift.const_mul 2
    rw [mul_zero] at hscaled
    refine hscaled.congr fun level => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio ?_ ?_
  · intro level
    unfold knowledge explained total
    dsimp only
    rw [sub_zero, add_zero]
    positivity
  · intro level
    refine (tree_knowledge_le level (trees level) (accepted level) (by positivity)).trans ?_
    have hcube : (0 : ℝ) ≤ ((level : ℝ) + 1) ^ 3 := by positivity
    exact div_le_div_of_nonneg_left hcube (by positivity) (by linarith)

/-- Settling `(n + 1)^3` uses, the shared certificates yield knowledge tending to one. -/
theorem tendsto_dag_knowledge :
    Tendsto (fun level : ℕ =>
        (⟨((level : ℝ) + 1) ^ 3, 0, 0, (dagSystem.certificateSize (certificate level) : ℝ)⟩ :
          Budget).knowledge) atTop (𝓝 1) := by
  have hlower : Tendsto (fun level : ℕ => ((level : ℝ) + 1) / ((level : ℝ) + 1 + 4)) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun level : ℕ => 4 / ((level : ℝ) + 1 + 4)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    rw [sub_zero] at h2
    refine h2.congr fun level => ?_
    have hpos : (0 : ℝ) < (level : ℝ) + 1 + 4 := by positivity
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds ?_ ?_
  · intro level
    have hpos : (0 : ℝ) < ((level : ℝ) + 1) ^ 3 := by positivity
    refine le_trans (le_of_eq ?_) (dag_knowledge_ge level hpos)
    have h1 : (level : ℝ) + 1 + 4 ≠ 0 := by positivity
    have h2 : ((level : ℝ) + 1) ^ 3 + 4 * ((level : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    rw [div_eq_div_iff h1 h2]
    ring
  · intro level
    unfold knowledge explained total
    dsimp only
    rw [sub_zero, add_zero]
    exact div_le_one_of_le₀ (by
      have := Nat.cast_nonneg (α := ℝ) (dagSystem.certificateSize (certificate level))
      linarith) (by positivity)

end Budget

end Mettapedia.InformationTheory.KnowledgeQuantification
