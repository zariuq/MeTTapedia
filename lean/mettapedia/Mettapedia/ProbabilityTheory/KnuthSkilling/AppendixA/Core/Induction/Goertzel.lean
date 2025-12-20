import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.Induction.ThetaPrime

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
Goertzel (Foundations-of-inference-new-proofs_v1, Lemma 7) reframes the B-empty difficulty as an
*order-invariance inside an admissible gap* statement:

If a B-empty extension step admits multiple admissible choices for the new “slope”/parameter, then
the relative order between any two newly-formed expressions should be independent of which
admissible choice is used; otherwise some “critical value” would force an equality, contradicting
the B-empty assumption.

This file records that idea in the current refactored codebase vocabulary, and links it to the
existing explicit blocker `BEmptyStrictGapSpec` in `ThetaPrime.lean`.

Status: This file currently provides *interfaces* (no placeholder proofs) that make the Goertzel
dependency explicit. Proving these interfaces from the existing K&S `Core/` development is the
next step.

Important: Goertzel’s Lemma 7 proof sketch contains the inference
“`X ⊕ d^n = Y` (old `X,Y`) ⇒ an old-grid value equals `d^n`”, i.e. a B-witness for `n`.
This is not valid in general for an associative ordered monoid: it would require additional
structure (e.g. a cancellative group/inverses, or a special unique-decomposition property).
See the concrete counterexample `lean-projects/mettapedia/Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/GoertzelLemma7.lean`.
-/

section
variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d) [KSSeparation α]

noncomputable def ThetaRaw (δ : ℝ) (r_old : Multi k) (t : ℕ) : ℝ :=
  R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ

/-!
`AdmissibleDelta` is a deliberately *local* notion: it says δ lies strictly between A- and C-side
statistics at *every* witness level u.

This matches the informal “δ is in the open gap” reading needed for Goertzel’s “invariance inside
the gap” proof outline.

Note: the current `chooseδ` definition in the B-empty branch uses `sSup` of A-statistics, which
does not automatically provide strict inequalities on the C-side. As a result, proving
`AdmissibleDelta (chooseδ …)` from the current Core library is a nontrivial task (and may require
strengthening hypotheses).
-/
def AdmissibleDelta (δ : ℝ) : Prop :=
  (∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetA F d u → separationStatistic R r u hu < δ) ∧
  (∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetC F d u → δ < separationStatistic R r u hu)

/-!
Goertzel Lemma 7 (invariance inside the admissible gap), specialized to the current
`ThetaRaw` expression family: if two admissible δ choices are both valid, then the sign of the
difference between two “new expressions” is invariant.

This is *exactly* the qualitative ingredient needed to rule out boundary equalities in the B-empty
strict-gap lemmas: if a boundary equality held for δ, then small admissible perturbations of δ
would flip the inequality, contradicting invariance.
-/
class GoertzelInvarianceSpec : Prop where
  invariant :
    ∀ {δ₁ δ₂ : ℝ},
      AdmissibleDelta (R := R) (F := F) (d := d) δ₁ →
      AdmissibleDelta (R := R) (F := F) (d := d) δ₂ →
      ∀ (r_old_x r_old_y : Multi k) (t_x t_y : ℕ),
        (ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x < ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y) ↔
        (ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x < ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y)

end

/-!
## Algebraic core of Goertzel Lemma 7 (affine “flip ⇒ equality”)

In the refactored codebase, the would-be extended evaluator on join-multiplicity witnesses is

`ThetaRaw δ r_old t = Θ(old) + t·δ`.

For fixed `(r_old_x,t_x)` and `(r_old_y,t_y)`, the difference is affine in `δ`.  Therefore, if
the strict inequality flips between two parameters `δ₁ < δ₂`, then there is an explicit “critical
value” `δ₀` where equality holds.  This step is *pure algebra* (no topology, no IVT).

Turning that equality into a contradiction in the B-empty case requires an *additional* link
between “numeric equality” and “algebraic equality” (injectivity of the extension map), which is
exactly where circularity can enter.
-/

section
variable {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)

lemma ThetaRaw_sub
    (δ : ℝ) (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) :
    ThetaRaw (R := R) (F := F) δ r_old_x t_x - ThetaRaw (R := R) (F := F) δ r_old_y t_y =
      (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) +
        ((t_x : ℝ) - (t_y : ℝ)) * δ := by
  simp [ThetaRaw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, mul_comm]

theorem ThetaRaw_flip_implies_eq_between
    {δ₁ δ₂ : ℝ} (_hδ : δ₁ < δ₂)
    (r_old_x r_old_y : Multi k) (t_x t_y : ℕ)
    (ht : t_y < t_x)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x <
          ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y <
          ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x) :
    ∃ δ₀ : ℝ, δ₁ < δ₀ ∧ δ₀ < δ₂ ∧
      ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x =
        ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y := by
  classical
  set a : ℝ :=
    (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) with ha
  set b : ℝ := (t_x : ℝ) - (t_y : ℝ) with hb
  have hb_pos : 0 < b := by
    have : (t_y : ℝ) < (t_x : ℝ) := by exact_mod_cast ht
    simpa [b] using sub_pos.mpr this
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  set δ₀ : ℝ := (-a) / b with hδ₀
  refine ⟨δ₀, ?_, ?_, ?_⟩
  · -- δ₁ < δ₀ from `a + b*δ₁ < 0`
    have hdiff₁ : a + b * δ₁ < 0 := by
      have : ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x -
            ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y < 0 := sub_neg.mpr h1
      simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm] using this
    have hmul : δ₁ * b < -a := by
      have : b * δ₁ < -a := by linarith [hdiff₁]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : δ₁ < (-a) / b := (lt_div_iff₀ hb_pos).2 hmul
    simpa [hδ₀] using this
  · -- δ₀ < δ₂ from `0 < a + b*δ₂`
    have hdiff₂ : 0 < a + b * δ₂ := by
      have : 0 < ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x -
            ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y := sub_pos.mpr h2
      simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm] using this
    have hmul : -a < δ₂ * b := by
      have : -a < b * δ₂ := by linarith [hdiff₂]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : (-a) / b < δ₂ := (div_lt_iff₀ hb_pos).2 hmul
    simpa [hδ₀] using this
  · -- equality at δ₀
    have hdiff0 : ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x -
          ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y = 0 := by
      have hab : a + b * δ₀ = 0 := by
        have hb_mul : b * ((-a) / b) = -a := by
          field_simp [hb_ne]
        have : a + b * ((-a) / b) = 0 := by linarith [hb_mul]
        simpa [δ₀, hδ₀] using this
      have hdiff :
          ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x -
              ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y = a + b * δ₀ := by
        simp [ThetaRaw_sub (R := R) (F := F), a, b]
      simp [hdiff, hab]
    exact sub_eq_zero.mp hdiff0

end

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
