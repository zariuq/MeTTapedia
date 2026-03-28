import Mettapedia.GSLT.Logic.ContextHML

/-!
# Depth-Bounded Logical Metric Kernel

This file adds the smallest honest kernel for Meredith's logical metric layer
(Part I, §5.3):

* modal depth for context-decorated HML formulae,
* depth-bounded logical equivalence,
* a binary-valued pseudoultrametric approximation at each depth.

It does **not** claim the full paper's ultrametric on the bisimulation quotient.
Instead, it packages the finite-depth fragments that such a metric is meant to
measure.
-/

namespace Mettapedia.GSLT

namespace HMLFormula

variable {S : GSLT} [HasMinimalContexts S]

/-- Modal depth of a context-decorated HML formula. -/
def modalDepth : HMLFormula S → Nat
  | .top => 0
  | .bot => 0
  | .conj ϕ ψ => max ϕ.modalDepth ψ.modalDepth
  | .neg ϕ => ϕ.modalDepth
  | .diamond _ ϕ => ϕ.modalDepth + 1

/-- The depth-`n` HML fragment: formulae whose modal depth is at most `n`. -/
def DepthFragment (n : Nat) := { ϕ : HMLFormula S // ϕ.modalDepth ≤ n }

/-- Two terms are depth-`n` logically equivalent if no formula of modal depth at
most `n` distinguishes them. -/
def hmlEquivUpTo (n : Nat) (t u : S.Term) : Prop :=
  ∀ ϕ : HMLFormula S, ϕ.modalDepth ≤ n → (satisfies S t ϕ ↔ satisfies S u ϕ)

theorem hmlEquivUpTo_refl (n : Nat) (t : S.Term) : hmlEquivUpTo (S := S) n t t :=
  by
    intro ϕ hϕ
    exact Iff.rfl

theorem hmlEquivUpTo_symm {n : Nat} {t u : S.Term}
    (h : hmlEquivUpTo (S := S) n t u) : hmlEquivUpTo (S := S) n u t :=
  by
    intro ϕ hϕ
    exact (h ϕ hϕ).symm

theorem hmlEquivUpTo_trans {n : Nat} {t u v : S.Term}
    (h₁ : hmlEquivUpTo (S := S) n t u) (h₂ : hmlEquivUpTo (S := S) n u v) :
    hmlEquivUpTo (S := S) n t v :=
  by
    intro ϕ hϕ
    exact (h₁ ϕ hϕ).trans (h₂ ϕ hϕ)

/-- Agreement at a larger depth implies agreement at every smaller depth. -/
theorem hmlEquivUpTo_mono {m n : Nat} {t u : S.Term}
    (hmn : m ≤ n) (h : hmlEquivUpTo (S := S) n t u) :
    hmlEquivUpTo (S := S) m t u :=
  by
    intro ϕ hϕ
    exact h ϕ (Nat.le_trans hϕ hmn)

/-- Full HML equivalence implies agreement at every finite modal depth. -/
theorem hmlEquiv_implies_hmlEquivUpTo {t u : S.Term}
    (h : hmlEquiv S t u) (n : Nat) : hmlEquivUpTo (S := S) n t u :=
  by
    intro ϕ hϕ
    exact h ϕ

/-- A depth-`n` distinguishing witness is a formula in the depth fragment whose
satisfaction differs on the two terms. -/
def DistinguishingWitness (n : Nat) (t u : S.Term) : Prop :=
  ∃ ϕ : HMLFormula S, ϕ.modalDepth ≤ n ∧ ¬ (satisfies S t ϕ ↔ satisfies S u ϕ)

theorem not_hmlEquivUpTo_iff (n : Nat) (t u : S.Term) :
    ¬ hmlEquivUpTo (S := S) n t u ↔ DistinguishingWitness (S := S) n t u := by
  classical
  constructor
  · intro h
    have hex : ∃ ϕ : HMLFormula S, ¬ (ϕ.modalDepth ≤ n → (satisfies S t ϕ ↔ satisfies S u ϕ)) := by
      simpa [hmlEquivUpTo] using h
    rcases hex with ⟨ϕ, hϕ⟩
    have hdepth : ϕ.modalDepth ≤ n := by
      by_contra hdepth
      exact hϕ (fun hd => False.elim (hdepth hd))
    refine ⟨ϕ, hdepth, ?_⟩
    intro hs
    exact hϕ (fun _ => hs)
  · rintro ⟨ϕ, hdepth, hdist⟩ heq
    exact hdist (heq ϕ hdepth)

/-- A depth-`n` logical distance approximation: `0` when the terms agree on the
entire depth-`n` fragment, `1` otherwise.

This is not yet the paper's full `d_HML`, but it is already a pseudoultrametric
kernel on the depth-bounded quotient.
-/
noncomputable def logicalDistanceApprox (n : Nat) (t u : S.Term) : Nat := by
  classical
  exact if hmlEquivUpTo (S := S) n t u then 0 else 1

@[simp] theorem logicalDistanceApprox_self (n : Nat) (t : S.Term) :
    logicalDistanceApprox (S := S) n t t = 0 := by
  classical
  have h : hmlEquivUpTo (S := S) n t t := hmlEquivUpTo_refl (S := S) n t
  simp [logicalDistanceApprox, h]

theorem logicalDistanceApprox_comm (n : Nat) (t u : S.Term) :
    logicalDistanceApprox (S := S) n t u = logicalDistanceApprox (S := S) n u t := by
  classical
  by_cases h : hmlEquivUpTo (S := S) n t u
  · have h' : hmlEquivUpTo (S := S) n u t := hmlEquivUpTo_symm h
    simp [logicalDistanceApprox, h, h']
  · have h' : ¬ hmlEquivUpTo (S := S) n u t := fun hu =>
      h (hmlEquivUpTo_symm hu)
    simp [logicalDistanceApprox, h, h']

theorem logicalDistanceApprox_eq_zero_iff (n : Nat) (t u : S.Term) :
    logicalDistanceApprox (S := S) n t u = 0 ↔ hmlEquivUpTo (S := S) n t u := by
  classical
  by_cases h : hmlEquivUpTo (S := S) n t u <;> simp [logicalDistanceApprox, h]

theorem logicalDistanceApprox_eq_one_iff (n : Nat) (t u : S.Term) :
    logicalDistanceApprox (S := S) n t u = 1 ↔ DistinguishingWitness (S := S) n t u := by
  classical
  rw [← not_hmlEquivUpTo_iff (S := S) n t u]
  by_cases h : hmlEquivUpTo (S := S) n t u <;> simp [logicalDistanceApprox, h]

/-- Each depth-bounded approximation is a pseudoultrametric with values in
`{0, 1}`. -/
theorem logicalDistanceApprox_ultrametric (n : Nat) (t u v : S.Term) :
    logicalDistanceApprox (S := S) n t v ≤
      max (logicalDistanceApprox (S := S) n t u) (logicalDistanceApprox (S := S) n u v) := by
  classical
  by_cases htv : hmlEquivUpTo (S := S) n t v
  · simp [logicalDistanceApprox, htv]
  · by_cases htu : hmlEquivUpTo (S := S) n t u
    · by_cases huv : hmlEquivUpTo (S := S) n u v
      · exact (htv (hmlEquivUpTo_trans htu huv)).elim
      · simp [logicalDistanceApprox, htv, htu, huv]
    · by_cases huv : hmlEquivUpTo (S := S) n u v
      · simp [logicalDistanceApprox, htv, htu, huv]
      · simp [logicalDistanceApprox, htv, htu, huv]

end HMLFormula

end Mettapedia.GSLT
