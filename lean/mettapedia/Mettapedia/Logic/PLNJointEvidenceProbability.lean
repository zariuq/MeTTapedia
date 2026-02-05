import Mettapedia.Logic.PLNJointEvidence

/-!
# Joint Evidence → Probability Views (Posterior Means)

`PLNJointEvidence.lean` defines the *theoretically correct* “complete” evidence object for a
finite set of PLN propositions: a Dirichlet posterior over complete worlds.

This file adds the minimal bridge to *probability*:
from a `JointEvidence n`, we can read off posterior-mean probabilities for
- events/propositions `P(A)`
- links/conditionals `P(B | A)`

These are *views* (projections) of the joint evidence, and are exactly the strengths obtained from
the extracted `Evidence` objects (`propEvidence`, `linkEvidence`).
-/

namespace Mettapedia.Logic.PLNJointEvidenceProbability

open scoped ENNReal

open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.PLNJointEvidence.JointEvidence

variable {n : ℕ}

/-! ## Basic “posterior mean” probability views -/

/-- Posterior-mean probability for proposition `A`, read from joint evidence. -/
noncomputable def probProp (E : JointEvidence n) (A : Fin n) : ℝ≥0∞ :=
  Evidence.toStrength (propEvidence (n := n) (E := E) A)

/-- Posterior-mean conditional probability for a link `A ⟹ B`, read from joint evidence. -/
noncomputable def probLink (E : JointEvidence n) (A B : Fin n) : ℝ≥0∞ :=
  Evidence.toStrength (linkEvidence (n := n) (E := E) A B)

/-! ## Structural identities (totals) -/

theorem propEvidence_total (E : JointEvidence n) (A : Fin n) :
    (propEvidence (n := n) (E := E) A).total = total (n := n) (E := E) := by
  classical
  -- We prove that splitting `E` into the parts where `A` is true vs false preserves the total.
  let f : Fin (2 ^ n) → ℝ≥0∞ := fun w => if worldToAssignment n w A then E w else 0
  let g : Fin (2 ^ n) → ℝ≥0∞ := fun w => if !(worldToAssignment n w A) then E w else 0
  have hfg : (fun w => f w + g w) = E := by
    funext w
    by_cases hA : worldToAssignment n w A <;> simp [f, g, hA]
  unfold propEvidence Evidence.total total countWorld
  -- Rewrite `(∑ f) + (∑ g)` as `∑ (f+g)` and use `hfg`.
  calc
    (Finset.univ.sum f + Finset.univ.sum g)
        = Finset.univ.sum (fun w => f w + g w) := by
          simp [Finset.sum_add_distrib]
    _ = Finset.univ.sum E := by
          simp [hfg]

theorem linkEvidence_total (E : JointEvidence n) (A B : Fin n) :
    (linkEvidence (n := n) (E := E) A B).total =
      countWorld (n := n) (E := E) (fun w => worldToAssignment n w A) := by
  classical
  let f : Fin (2 ^ n) → ℝ≥0∞ :=
    fun w => if worldToAssignment n w A && worldToAssignment n w B then E w else 0
  let g : Fin (2 ^ n) → ℝ≥0∞ :=
    fun w => if worldToAssignment n w A && !(worldToAssignment n w B) then E w else 0
  let h : Fin (2 ^ n) → ℝ≥0∞ := fun w => if worldToAssignment n w A then E w else 0
  have hfg : (fun w => f w + g w) = h := by
    funext w
    by_cases hA : worldToAssignment n w A <;> by_cases hB : worldToAssignment n w B <;>
      simp [f, g, h, hA, hB]
  unfold linkEvidence Evidence.total countWorld
  calc
    (Finset.univ.sum f + Finset.univ.sum g)
        = Finset.univ.sum (fun w => f w + g w) := by
          simp [Finset.sum_add_distrib]
    _ = Finset.univ.sum h := by
          simp [hfg]

/-! ## Rewriting the probability views in terms of joint counts -/

theorem probProp_eq (E : JointEvidence n) (A : Fin n) :
    probProp (n := n) E A =
      if total (n := n) (E := E) = 0 then
        0
      else
        countWorld (n := n) (E := E) (fun w => worldToAssignment n w A) /
          total (n := n) (E := E) := by
  classical
  unfold probProp
  have ht : (propEvidence (n := n) (E := E) A).total = total (n := n) (E := E) :=
    propEvidence_total (n := n) (E := E) A
  -- Avoid unfolding `Evidence.total`, so the `if` condition stays as `e.total = 0`
  -- (rather than becoming `e.pos = 0 ∧ e.neg = 0`).
  calc
    Evidence.toStrength (propEvidence (n := n) (E := E) A) =
        if total (n := n) (E := E) = 0 then
          0
        else
          (propEvidence (n := n) (E := E) A).pos / total (n := n) (E := E) := by
      simp [Evidence.toStrength, ht]
    _ = _ := by
      simp [propEvidence]

theorem probLink_eq (E : JointEvidence n) (A B : Fin n) :
    probLink (n := n) E A B =
      if countWorld (n := n) (E := E) (fun w => worldToAssignment n w A) = 0 then
        0
      else
        countWorld (n := n) (E := E)
            (fun w => worldToAssignment n w A && worldToAssignment n w B) /
          countWorld (n := n) (E := E) (fun w => worldToAssignment n w A) := by
  classical
  unfold probLink
  have ht :
      (linkEvidence (n := n) (E := E) A B).total =
        countWorld (n := n) (E := E) (fun w => worldToAssignment n w A) :=
    linkEvidence_total (n := n) (E := E) A B
  -- Avoid unfolding `Evidence.total` for the same reason as in `probProp_eq`.
  calc
    Evidence.toStrength (linkEvidence (n := n) (E := E) A B) =
        if countWorld (n := n) (E := E) (fun w => worldToAssignment n w A) = 0 then
          0
        else
          (linkEvidence (n := n) (E := E) A B).pos /
            countWorld (n := n) (E := E) (fun w => worldToAssignment n w A) := by
      simp [Evidence.toStrength, ht]
    _ = _ := by
      simp [linkEvidence]

end Mettapedia.Logic.PLNJointEvidenceProbability
