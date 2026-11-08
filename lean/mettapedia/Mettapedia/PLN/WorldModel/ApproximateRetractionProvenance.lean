import Mettapedia.PLN.WorldModel.ApproximateRetraction
import Mettapedia.PLN.WorldModel.ProvenanceRetraction

/-!
# Approximate retraction on compressed provenance: lineage and truncation

The exact reference is deletion on how-provenance (`ProvenanceRetraction.deletion`).  The evidence
of a claim is its provenance evaluated under a valuation `ν` of the source tokens in `ℝ≥0`
(`mass`): each derivation contributes its multiplicity times the values of its sources.  Evaluation
is a semiring homomorphism, a sub-polynomial has less mass (`mass_le_of_coeff_le`), deletion never
adds mass (`mass_deletion_le`), and what survives deletion is the mass of the derivations that
avoid the withdrawn tokens (`mass_deletion`).

Both compressed representations below hold an estimate and a width, and a faithfulness invariant
ties them to the exact polynomial: the polynomial splits into a part whose mass the estimate
accounts for and a remainder whose mass the width covers.  Each invariant holds of the
compression, survives every forgetting, and is closed under revision and deduction.  It gives the
certified bound `estimate ≤ exact ≤ estimate + width` (`Encloses`).

## Lineage deletion (`LineageClaim`)

A claim is compressed to its evidence, its lineage (the tokens its derivations use) and a width.
Withdrawing tokens drops every claim whose lineage meets them; the evidence it held joins its width
(`LineageClaim.forget`).

* `LineageClaim.Faithful.forget`, `LineageClaim.Faithful.encloses`: the bound holds after any
  number of forgettings; the estimate never exceeds the exact evidence.
* **The gap is the evidence of the derivations that had alternatives** (`lineage_gap`): a dropped
  claim's exact evidence after deletion is the mass of its derivations that avoid the withdrawn
  tokens.  In `x + y`, withdrawing `x` drops the claim while `y` survives
  (`Controls.alternatives_gap`); in `x · y` nothing survives (`Controls.joint_gap`).
* **No accumulation**: forgetting twice is forgetting the union (`LineageClaim.forget_forget`).
* Relevance and support closure hold exactly (`LineageClaim.forget_of_disjoint`,
  `LineageClaim.forget_lineage`).
* **It keeps information about the withdrawn tokens** (`Controls.lineage_leaks`): it is exact on
  clean claims (`lineage_vacuous`) and inexact on `x + y`, so by
  `ApproximateRetraction.leaks_of_inexact` two polynomials that agree once `x` is withdrawn are told
  apart after forgetting.

## Truncated provenance (`TruncatedClaim`)

A claim is compressed to the monomials a selection keeps, with the dropped mass as width
(`TruncatedClaim.ofSelection`).  Deletion after truncation deletes from the kept monomials and
keeps the width (`TruncatedClaim.forget`).

* `TruncatedClaim.Faithful.forget`, `TruncatedClaim.Faithful.encloses`: the error after deletion is
  at most the dropped mass, however many deletions follow (`TruncatedClaim.forget_forget`).
* A fixed selection, degree truncation among them, commutes with deletion (`deletion_select`).
  Top-k selects by the polynomial itself: in `100 x + y` it keeps `x`, and once `x` is withdrawn the
  only support is the dropped `y` (`Controls.heavy_after_deletion`).  The certified guard at
  threshold `1` is then undecided, while a guard on the point estimate commits `below` against the
  exact value `1` (`Controls.heavy_guard`).
* The width is retained data about the dropped monomials: `x + z` and `x` agree once `z` is
  withdrawn and their truncations differ in width (`Controls.truncation_width_remembers`).

## Through derivations

Revision adds faithful claims and deduction multiplies them (`LineageClaim.Faithful.revise`,
`LineageClaim.Faithful.deduce`, `TruncatedClaim.Faithful.revise`, `TruncatedClaim.Faithful.deduce`).
On numbers, the estimate and the width of a derived claim are computed from those of its base claims
(`boundDerived`): revision adds widths, deduction scales each premise's width by the other premise's
estimate.  For every derivation over truncated base claims, after deleting any tokens, the exact
derived evidence is enclosed by that estimate and width (`truncated_derived_encloses`).

## As approximation maps

Both representations give the certified bound as an `ApproximationMap` from exact token deletion
(`truncationCertificate`, `lineageCertificate`), and every Lipschitz readout inherits it: confidence
after deletion from truncated provenance is within `k⁻¹` times the dropped mass
(`truncation_confidence`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance

open MvPolynomial
open scoped NNReal
open Mettapedia.Logic.WorldModel (ApproximationMap)
open Mettapedia.PLN.WorldModel.ProvenanceRetraction
  (deletion deletion_X deletion_C coeff_deletion coeff_deletion_le deletion_eq_self_of_disjoint
    deletion_idempotent deletion_deletion vars_deletion_disjoint vars_deletion_subset Derived
    deletion_prov ProvState forgetTokens)
open Mettapedia.PLN.WorldModel.ApproximateRetraction

/-! ## Mass -/

section Mass

variable {σ : Type}

/-- The evidence of a provenance polynomial under a valuation of its source tokens. -/
noncomputable def mass (ν : σ → ℝ≥0) (p : MvPolynomial σ ℕ) : ℝ≥0 :=
  eval₂ (Nat.castRingHom ℝ≥0) ν p

theorem mass_zero (ν : σ → ℝ≥0) : mass ν 0 = 0 := eval₂_zero _ _

theorem mass_X (ν : σ → ℝ≥0) (x : σ) : mass ν (X x) = ν x := eval₂_X _ _ x

theorem mass_add (ν : σ → ℝ≥0) (p q : MvPolynomial σ ℕ) : mass ν (p + q) = mass ν p + mass ν q :=
  eval₂_add _ _

theorem mass_mul (ν : σ → ℝ≥0) (p q : MvPolynomial σ ℕ) : mass ν (p * q) = mass ν p * mass ν q :=
  eval₂_mul _ _

/-- The weight of a monomial: the product of the values of its tokens. -/
noncomputable def weight (ν : σ → ℝ≥0) (d : σ →₀ ℕ) : ℝ≥0 := ∏ i ∈ d.support, ν i ^ d i

theorem mass_eq_sum (ν : σ → ℝ≥0) (p : MvPolynomial σ ℕ) :
    mass ν p = ∑ d ∈ p.support, ((p.coeff d : ℕ) : ℝ≥0) * weight ν d := by
  rw [mass, eval₂_eq]
  rfl

/-- **A sub-polynomial has less mass**: evaluation manufactures no evidence. -/
theorem mass_le_of_coeff_le (ν : σ → ℝ≥0) {p q : MvPolynomial σ ℕ}
    (le : ∀ d, p.coeff d ≤ q.coeff d) : mass ν p ≤ mass ν q := by
  have sub : p.support ⊆ q.support := fun d hd => by
    rw [mem_support_iff] at hd ⊢
    exact fun hq => hd (Nat.eq_zero_of_le_zero ((le d).trans hq.le))
  rw [mass_eq_sum, mass_eq_sum]
  calc ∑ d ∈ p.support, ((p.coeff d : ℕ) : ℝ≥0) * weight ν d
      ≤ ∑ d ∈ q.support, ((p.coeff d : ℕ) : ℝ≥0) * weight ν d := Finset.sum_le_sum_of_subset sub
    _ ≤ ∑ d ∈ q.support, ((q.coeff d : ℕ) : ℝ≥0) * weight ν d :=
        Finset.sum_le_sum fun d _ => mul_le_mul' (Nat.cast_le.mpr (le d)) le_rfl

/-- The monomials of `p` that `keep` selects. -/
noncomputable def select (keep : (σ →₀ ℕ) → Prop) [DecidablePred keep] (p : MvPolynomial σ ℕ) :
    MvPolynomial σ ℕ :=
  AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter keep)

theorem coeff_select (keep : (σ →₀ ℕ) → Prop) [DecidablePred keep] (p : MvPolynomial σ ℕ)
    (d : σ →₀ ℕ) : (select keep p).coeff d = if keep d then p.coeff d else 0 := rfl

/-- A selection and its complement split the polynomial. -/
theorem select_add_select_not (keep : (σ →₀ ℕ) → Prop) [DecidablePred keep]
    (p : MvPolynomial σ ℕ) : select keep p + select (fun d => ¬ keep d) p = p := by
  ext d
  rw [coeff_add, coeff_select, coeff_select]
  by_cases h : keep d <;> simp [h]

end Mass

section Deletion

variable {σ : Type} [DecidableEq σ]

/-- **Deletion never adds mass.** -/
theorem mass_deletion_le (ν : σ → ℝ≥0) (S : Finset σ) (p : MvPolynomial σ ℕ) :
    mass ν (deletion S p) ≤ mass ν p :=
  mass_le_of_coeff_le ν (coeff_deletion_le S p)

theorem support_deletion (S : Finset σ) (p : MvPolynomial σ ℕ) :
    (deletion S p).support = p.support.filter fun d => Disjoint d.support S := by
  ext d
  rw [Finset.mem_filter, mem_support_iff, mem_support_iff, coeff_deletion]
  split_ifs with h
  · exact ⟨fun hp => ⟨hp, h⟩, fun hp => hp.1⟩
  · exact ⟨fun hp => absurd rfl hp, fun hp => absurd hp.2 h⟩

/-- **What survives deletion is the mass of the derivations that avoid the withdrawn tokens.** -/
theorem mass_deletion (ν : σ → ℝ≥0) (S : Finset σ) (p : MvPolynomial σ ℕ) :
    mass ν (deletion S p) =
      ∑ d ∈ p.support.filter (fun d => Disjoint d.support S),
        ((p.coeff d : ℕ) : ℝ≥0) * weight ν d := by
  rw [mass_eq_sum, support_deletion]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coeff_deletion, if_pos (Finset.mem_filter.mp hd).2]

/-- A polynomial whose deletion changes its mass uses a withdrawn token. -/
theorem meets_of_mass_ne {ν : σ → ℝ≥0} {S : Finset σ} {p : MvPolynomial σ ℕ}
    (h : mass ν (deletion S p) ≠ mass ν p) : ¬ Disjoint p.vars S :=
  fun hd => h (by rw [deletion_eq_self_of_disjoint hd])

/-- **A fixed selection commutes with deletion.**  Degree truncation is one: whether a monomial is
kept does not depend on the polynomial. -/
theorem deletion_select (S : Finset σ) (keep : (σ →₀ ℕ) → Prop) [DecidablePred keep]
    (p : MvPolynomial σ ℕ) : deletion S (select keep p) = select keep (deletion S p) := by
  ext d
  rw [coeff_deletion, coeff_select, coeff_select, coeff_deletion]
  by_cases h₁ : Disjoint d.support S <;> by_cases h₂ : keep d <;> simp [h₁, h₂]

end Deletion

/-! ## Lineage deletion -/

/-- A claim compressed to its evidence, its lineage and a width. -/
structure LineageClaim (σ : Type) where
  /-- The evidence held. -/
  evidence : ℝ≥0
  /-- The tokens the held evidence may use. -/
  lineage : Finset σ
  /-- A bound on the evidence not held. -/
  width : ℝ≥0

namespace LineageClaim

section Plain

variable {σ : Type}

/-- Compress a provenance polynomial to its mass, its tokens and width zero. -/
noncomputable def ofProvenance (ν : σ → ℝ≥0) (p : MvPolynomial σ ℕ) : LineageClaim σ :=
  ⟨mass ν p, p.vars, 0⟩

/-- A lineage claim is faithful to a provenance polynomial when the polynomial splits into a part
whose mass is the held evidence and whose tokens lie in the lineage, and a remainder whose mass the
width covers. -/
def Faithful (ν : σ → ℝ≥0) (c : LineageClaim σ) (p : MvPolynomial σ ℕ) : Prop :=
  ∃ k r : MvPolynomial σ ℕ, p = k + r ∧ c.evidence = mass ν k ∧ k.vars ⊆ c.lineage ∧
    mass ν r ≤ c.width

theorem faithful_ofProvenance (ν : σ → ℝ≥0) (p : MvPolynomial σ ℕ) :
    (ofProvenance ν p).Faithful ν p :=
  ⟨p, 0, (add_zero p).symm, rfl, Finset.Subset.refl _, (mass_zero ν).trans_le zero_le⟩

/-- **The certified bound**: the held evidence never exceeds the exact evidence, and misses at most
the width. -/
theorem Faithful.encloses {ν : σ → ℝ≥0} {c : LineageClaim σ} {p : MvPolynomial σ ℕ}
    (h : c.Faithful ν p) : Encloses c.evidence c.width (mass ν p) := by
  obtain ⟨k, r, rfl, he, _, hr⟩ := h
  rw [mass_add, he]
  exact ⟨le_self_add, add_le_add le_rfl hr⟩

end Plain

section Tracked

variable {σ : Type} [DecidableEq σ]

/-- **Lineage deletion**: a claim whose lineage meets the withdrawn tokens is dropped, and the
evidence it held joins its width. -/
noncomputable def forget (S : Finset σ) (c : LineageClaim σ) : LineageClaim σ :=
  if Disjoint c.lineage S then c else ⟨0, ∅, c.evidence + c.width⟩

/-- Revision adds evidence and widths and joins lineages. -/
noncomputable def revise (c d : LineageClaim σ) : LineageClaim σ :=
  ⟨c.evidence + d.evidence, c.lineage ∪ d.lineage, c.width + d.width⟩

/-- Deduction multiplies evidence and joins lineages; its width scales each premise's width by the
other premise's evidence. -/
noncomputable def deduce (c d : LineageClaim σ) : LineageClaim σ :=
  ⟨c.evidence * d.evidence, c.lineage ∪ d.lineage, mulWidth c.evidence c.width d.evidence d.width⟩

noncomputable instance : Add (LineageClaim σ) := ⟨revise⟩

noncomputable instance : Zero (LineageClaim σ) := ⟨⟨0, ∅, 0⟩⟩

/-- **Faithfulness survives every forgetting.** -/
theorem Faithful.forget {ν : σ → ℝ≥0} {c : LineageClaim σ} {p : MvPolynomial σ ℕ}
    (h : c.Faithful ν p) (S : Finset σ) : (c.forget S).Faithful ν (deletion S p) := by
  obtain ⟨k, r, rfl, he, hk, hr⟩ := h
  unfold LineageClaim.forget
  by_cases hd : Disjoint c.lineage S
  · rw [if_pos hd]
    refine ⟨k, deletion S r, ?_, he, hk, (mass_deletion_le ν S r).trans hr⟩
    rw [map_add, deletion_eq_self_of_disjoint (Finset.disjoint_of_subset_left hk hd)]
  · rw [if_neg hd]
    refine ⟨0, deletion S k + deletion S r, by rw [map_add, zero_add], (mass_zero ν).symm,
      by simp, ?_⟩
    rw [mass_add, he]
    exact add_le_add (mass_deletion_le ν S k) ((mass_deletion_le ν S r).trans hr)

/-- **Revision keeps faithfulness.** -/
theorem Faithful.revise {ν : σ → ℝ≥0} {c d : LineageClaim σ} {p q : MvPolynomial σ ℕ}
    (hc : c.Faithful ν p) (hd : d.Faithful ν q) : (c.revise d).Faithful ν (p + q) := by
  obtain ⟨k₁, r₁, rfl, e₁, l₁, w₁⟩ := hc
  obtain ⟨k₂, r₂, rfl, e₂, l₂, w₂⟩ := hd
  refine ⟨k₁ + k₂, r₁ + r₂, add_add_add_comm _ _ _ _, ?_, ?_, ?_⟩
  · show c.evidence + d.evidence = mass ν (k₁ + k₂)
    rw [mass_add, e₁, e₂]
  · exact (vars_add_subset k₁ k₂).trans (Finset.union_subset_union l₁ l₂)
  · show mass ν (r₁ + r₂) ≤ c.width + d.width
    rw [mass_add]
    exact add_le_add w₁ w₂

/-- **Deduction keeps faithfulness**, with the width of `mulWidth`. -/
theorem Faithful.deduce {ν : σ → ℝ≥0} {c d : LineageClaim σ} {p q : MvPolynomial σ ℕ}
    (hc : c.Faithful ν p) (hd : d.Faithful ν q) : (c.deduce d).Faithful ν (p * q) := by
  obtain ⟨k₁, r₁, rfl, e₁, l₁, w₁⟩ := hc
  obtain ⟨k₂, r₂, rfl, e₂, l₂, w₂⟩ := hd
  refine ⟨k₁ * k₂, k₁ * r₂ + r₁ * k₂ + r₁ * r₂, by ring, ?_, ?_, ?_⟩
  · show c.evidence * d.evidence = mass ν (k₁ * k₂)
    rw [mass_mul, e₁, e₂]
  · exact (vars_mul k₁ k₂).trans (Finset.union_subset_union l₁ l₂)
  · show mass ν (k₁ * r₂ + r₁ * k₂ + r₁ * r₂) ≤ mulWidth c.evidence c.width d.evidence d.width
    rw [mass_add, mass_add, mass_mul, mass_mul, mass_mul, e₁, e₂]
    unfold mulWidth
    exact add_le_add (add_le_add (mul_le_mul' le_rfl w₂) (mul_le_mul' w₁ le_rfl))
      (mul_le_mul' w₁ w₂)

/-- **Forgetting twice is forgetting the union**: lineage deletion accumulates no error. -/
theorem forget_forget (S T : Finset σ) (c : LineageClaim σ) :
    (c.forget S).forget T = c.forget (S ∪ T) := by
  by_cases hS : Disjoint c.lineage S <;> by_cases hT : Disjoint c.lineage T <;>
    simp [LineageClaim.forget, hS, hT, Finset.disjoint_union_right]

/-- **Relevance**: a claim whose lineage avoids the withdrawn tokens is kept unchanged. -/
theorem forget_of_disjoint {S : Finset σ} {c : LineageClaim σ} (h : Disjoint c.lineage S) :
    c.forget S = c :=
  if_pos h

/-- **Support closure**: the lineage held after forgetting avoids the withdrawn tokens and lies in
the lineage held before. -/
theorem forget_lineage (S : Finset σ) (c : LineageClaim σ) :
    Disjoint (c.forget S).lineage S ∧ (c.forget S).lineage ⊆ c.lineage := by
  unfold LineageClaim.forget
  by_cases h : Disjoint c.lineage S
  · rw [if_pos h]
    exact ⟨h, Finset.Subset.refl _⟩
  · rw [if_neg h]
    exact ⟨Finset.disjoint_empty_left S, Finset.empty_subset _⟩

end Tracked

end LineageClaim

section LineageGap

variable {σ : Type} [DecidableEq σ]

open LineageClaim

/-- **The gap of lineage deletion is the evidence of the derivations that had alternatives.**  A
compressed claim whose lineage meets the withdrawn tokens is dropped, while the exact evidence after
deletion is the mass of its derivations that avoid them. -/
theorem lineage_gap (ν : σ → ℝ≥0) (S : Finset σ) (p : MvPolynomial σ ℕ)
    (meets : ¬ Disjoint p.vars S) :
    ((ofProvenance ν p).forget S).evidence = 0 ∧
      mass ν (deletion S p) =
        ∑ d ∈ p.support.filter (fun d => Disjoint d.support S),
          ((p.coeff d : ℕ) : ℝ≥0) * weight ν d := by
  refine ⟨?_, mass_deletion ν S p⟩
  show (if Disjoint p.vars S then ofProvenance ν p else ⟨0, ∅, mass ν p + 0⟩).evidence = 0
  simp only [if_neg meets]

/-- **Exact on clean claims**: when deletion fixes a polynomial, lineage deletion keeps its
compression. -/
theorem lineage_vacuous (ν : σ → ℝ≥0) (S : Finset σ) (p : MvPolynomial σ ℕ)
    (clean : deletion S p = p) : ((ofProvenance ν p).forget S).evidence = mass ν p := by
  have hd : Disjoint p.vars S := by
    have h := vars_deletion_disjoint S p
    rwa [clean] at h
  show (if Disjoint p.vars S then ofProvenance ν p else ⟨0, ∅, mass ν p + 0⟩).evidence = mass ν p
  rw [if_pos hd]
  rfl

end LineageGap

/-! ## Truncated provenance -/

/-- A claim compressed to the monomials it keeps and a width covering the mass it dropped. -/
structure TruncatedClaim (σ : Type) where
  /-- The kept monomials. -/
  kept : MvPolynomial σ ℕ
  /-- A bound on the mass of the dropped monomials. -/
  width : ℝ≥0

namespace TruncatedClaim

section Plain

variable {σ : Type}

/-- Compress by a selection: keep the selected monomials and hold the dropped mass as width. -/
noncomputable def ofSelection (ν : σ → ℝ≥0) (keep : (σ →₀ ℕ) → Prop) [DecidablePred keep]
    (p : MvPolynomial σ ℕ) : TruncatedClaim σ :=
  ⟨select keep p, mass ν (select (fun d => ¬ keep d) p)⟩

/-- The evidence a truncated claim holds. -/
noncomputable def estimate (ν : σ → ℝ≥0) (c : TruncatedClaim σ) : ℝ≥0 := mass ν c.kept

/-- Revision adds kept monomials and widths. -/
noncomputable def revise (c d : TruncatedClaim σ) : TruncatedClaim σ :=
  ⟨c.kept + d.kept, c.width + d.width⟩

/-- Deduction multiplies kept monomials; its width scales each premise's width by the other
premise's estimate. -/
noncomputable def deduce (ν : σ → ℝ≥0) (c d : TruncatedClaim σ) : TruncatedClaim σ :=
  ⟨c.kept * d.kept, mulWidth (c.estimate ν) c.width (d.estimate ν) d.width⟩

noncomputable instance : Add (TruncatedClaim σ) := ⟨revise⟩

noncomputable instance : Zero (TruncatedClaim σ) := ⟨⟨0, 0⟩⟩

/-- A truncated claim is faithful to a provenance polynomial when the polynomial is the kept part
plus a remainder whose mass the width covers. -/
def Faithful (ν : σ → ℝ≥0) (c : TruncatedClaim σ) (p : MvPolynomial σ ℕ) : Prop :=
  ∃ rest : MvPolynomial σ ℕ, p = c.kept + rest ∧ mass ν rest ≤ c.width

theorem faithful_ofSelection (ν : σ → ℝ≥0) (keep : (σ →₀ ℕ) → Prop) [DecidablePred keep]
    (p : MvPolynomial σ ℕ) : (ofSelection ν keep p).Faithful ν p :=
  ⟨select (fun d => ¬ keep d) p, (select_add_select_not keep p).symm, le_rfl⟩

/-- **The certified bound**: the error is at most the dropped mass. -/
theorem Faithful.encloses {ν : σ → ℝ≥0} {c : TruncatedClaim σ} {p : MvPolynomial σ ℕ}
    (h : c.Faithful ν p) : Encloses (c.estimate ν) c.width (mass ν p) := by
  obtain ⟨rest, rfl, hw⟩ := h
  rw [mass_add]
  exact ⟨le_self_add, add_le_add le_rfl hw⟩

/-- **Revision keeps faithfulness**, and the widths add. -/
theorem Faithful.revise {ν : σ → ℝ≥0} {c d : TruncatedClaim σ} {p q : MvPolynomial σ ℕ}
    (hc : c.Faithful ν p) (hd : d.Faithful ν q) : (c.revise d).Faithful ν (p + q) := by
  obtain ⟨r₁, rfl, w₁⟩ := hc
  obtain ⟨r₂, rfl, w₂⟩ := hd
  refine ⟨r₁ + r₂, add_add_add_comm _ _ _ _, ?_⟩
  show mass ν (r₁ + r₂) ≤ c.width + d.width
  rw [mass_add]
  exact add_le_add w₁ w₂

/-- **Deduction keeps faithfulness**, with the width of `mulWidth`. -/
theorem Faithful.deduce {ν : σ → ℝ≥0} {c d : TruncatedClaim σ} {p q : MvPolynomial σ ℕ}
    (hc : c.Faithful ν p) (hd : d.Faithful ν q) : (deduce ν c d).Faithful ν (p * q) := by
  obtain ⟨r₁, rfl, w₁⟩ := hc
  obtain ⟨r₂, rfl, w₂⟩ := hd
  refine ⟨c.kept * r₂ + r₁ * d.kept + r₁ * r₂, ?_, ?_⟩
  · show (c.kept + r₁) * (d.kept + r₂) = c.kept * d.kept + (c.kept * r₂ + r₁ * d.kept + r₁ * r₂)
    ring
  · show mass ν (c.kept * r₂ + r₁ * d.kept + r₁ * r₂) ≤
      mulWidth (mass ν c.kept) c.width (mass ν d.kept) d.width
    rw [mass_add, mass_add, mass_mul, mass_mul, mass_mul]
    unfold mulWidth
    exact add_le_add (add_le_add (mul_le_mul' le_rfl w₂) (mul_le_mul' w₁ le_rfl))
      (mul_le_mul' w₁ w₂)

end Plain

section Tracked

variable {σ : Type} [DecidableEq σ]

/-- **Deletion after truncation**: delete from the kept monomials; the width stays. -/
noncomputable def forget (S : Finset σ) (c : TruncatedClaim σ) : TruncatedClaim σ :=
  ⟨deletion S c.kept, c.width⟩

/-- **Faithfulness survives every forgetting**: deletion only lowers the dropped mass. -/
theorem Faithful.forget {ν : σ → ℝ≥0} {c : TruncatedClaim σ} {p : MvPolynomial σ ℕ}
    (h : c.Faithful ν p) (S : Finset σ) : (c.forget S).Faithful ν (deletion S p) := by
  obtain ⟨rest, rfl, hw⟩ := h
  exact ⟨deletion S rest, map_add (deletion S) c.kept rest, (mass_deletion_le ν S rest).trans hw⟩

/-- **Forgetting twice is forgetting the union**: the width does not grow. -/
theorem forget_forget (S T : Finset σ) (c : TruncatedClaim σ) :
    (c.forget S).forget T = c.forget (T ∪ S) := by
  show (⟨deletion T (deletion S c.kept), c.width⟩ : TruncatedClaim σ) =
    ⟨deletion (T ∪ S) c.kept, c.width⟩
  rw [deletion_deletion]

/-- **Relevance**: the estimate of a claim whose kept tokens avoid the withdrawn ones is
unchanged. -/
theorem estimate_forget_of_disjoint (ν : σ → ℝ≥0) {S : Finset σ} {c : TruncatedClaim σ}
    (h : Disjoint c.kept.vars S) : (c.forget S).estimate ν = c.estimate ν := by
  show mass ν (deletion S c.kept) = mass ν c.kept
  rw [deletion_eq_self_of_disjoint h]

/-- **Support closure**: the kept tokens after forgetting avoid the withdrawn ones and lie among the
kept tokens before. -/
theorem forget_kept_vars (S : Finset σ) (c : TruncatedClaim σ) :
    Disjoint (c.forget S).kept.vars S ∧ (c.forget S).kept.vars ⊆ c.kept.vars :=
  ⟨vars_deletion_disjoint S c.kept, vars_deletion_subset S c.kept⟩

end Tracked

end TruncatedClaim

/-! ## Through derivations -/

section Derivations

/-- A derivation evaluated on numbers: revision adds and deduction multiplies. -/
noncomputable def evalDerived {B : Type} (v : B → ℝ≥0) : Derived B → ℝ≥0
  | .base b => v b
  | .revise d e => evalDerived v d + evalDerived v e
  | .deduce d e => evalDerived v d * evalDerived v e

/-- The estimate and the width of a derived claim from those of its base claims: revision adds
widths, deduction scales each premise's width by the other premise's estimate. -/
noncomputable def boundDerived {B : Type} (est w : B → ℝ≥0) : Derived B → ℝ≥0 × ℝ≥0
  | .base b => (est b, w b)
  | .revise d e => ((boundDerived est w d).1 + (boundDerived est w e).1,
      (boundDerived est w d).2 + (boundDerived est w e).2)
  | .deduce d e => ((boundDerived est w d).1 * (boundDerived est w e).1,
      mulWidth (boundDerived est w d).1 (boundDerived est w d).2 (boundDerived est w e).1
        (boundDerived est w e).2)

/-- **The certified bound holds through every derivation.** -/
theorem encloses_derived {B : Type} {est w x : B → ℝ≥0}
    (base : ∀ b, Encloses (est b) (w b) (x b)) :
    ∀ d : Derived B, Encloses (boundDerived est w d).1 (boundDerived est w d).2 (evalDerived x d)
  | .base b => base b
  | .revise d e => (encloses_derived base d).add (encloses_derived base e)
  | .deduce d e => (encloses_derived base d).mul (encloses_derived base e)

/-- The derived estimate is the derivation evaluated on the base estimates. -/
theorem boundDerived_fst {B : Type} (est w : B → ℝ≥0) :
    ∀ d : Derived B, (boundDerived est w d).1 = evalDerived est d
  | .base _ => rfl
  | .revise d e => by
      show (boundDerived est w d).1 + (boundDerived est w e).1 =
        evalDerived est d + evalDerived est e
      rw [boundDerived_fst est w d, boundDerived_fst est w e]
  | .deduce d e => by
      show (boundDerived est w d).1 * (boundDerived est w e).1 =
        evalDerived est d * evalDerived est e
      rw [boundDerived_fst est w d, boundDerived_fst est w e]

variable {σ : Type} [DecidableEq σ]

omit [DecidableEq σ] in
/-- The mass of a derived claim is the derivation evaluated on the masses of its base claims. -/
theorem mass_derived (ν : σ → ℝ≥0) {B : Type} (ann : B → MvPolynomial σ ℕ) :
    ∀ d : Derived B, mass ν (d.prov ann) = evalDerived (fun b => mass ν (ann b)) d
  | .base _ => rfl
  | .revise d e => by
      rw [Derived.prov, mass_add, mass_derived ν ann d, mass_derived ν ann e]
      rfl
  | .deduce d e => by
      rw [Derived.prov, mass_mul, mass_derived ν ann d, mass_derived ν ann e]
      rfl

/-- **Truncated base claims, deleted and derived from.**  For any derivation from base claims whose
truncations are faithful, after deleting `S` the exact derived evidence is enclosed by the derived
estimate and width, computed only from what the truncations hold. -/
theorem truncated_derived_encloses (ν : σ → ℝ≥0) (S : Finset σ) {B : Type}
    (ann : B → MvPolynomial σ ℕ) (c : B → TruncatedClaim σ)
    (faithful : ∀ b, (c b).Faithful ν (ann b)) (d : Derived B) :
    Encloses (boundDerived (fun b => ((c b).forget S).estimate ν) (fun b => (c b).width) d).1
      (boundDerived (fun b => ((c b).forget S).estimate ν) (fun b => (c b).width) d).2
      (mass ν (deletion S (d.prov ann))) := by
  rw [deletion_prov, mass_derived]
  exact encloses_derived (fun b => ((faithful b).forget S).encloses) d

end Derivations

/-! ## As approximation maps -/

section Certificates

variable {σ : Type} [DecidableEq σ] (Claim : Type)

/-- **Truncated provenance as an approximation map** from exact token deletion to deletion after
truncation, read under `ν`; its error at a claim is the dropped mass that claim holds. -/
noncomputable def truncationCertificate (ν : σ → ℝ≥0) (keep : (σ →₀ ℕ) → Prop)
    [DecidablePred keep] :
    ApproximationMap
      (AfterRetraction (forgetTokens (Claim := Claim)) fun W q => mass ν (W q))
      (Finset σ × Claim) ℝ≥0
      (AfterRetraction (fun S (c : Claim → TruncatedClaim σ) q => (c q).forget S)
        fun c q => (c q).estimate ν)
      (Finset σ × Claim) ℝ≥0 :=
  certified (forgetTokens (Claim := Claim)) (fun W q => mass ν (W q))
    (fun S (c : Claim → TruncatedClaim σ) q => (c q).forget S) (fun c q => (c q).estimate ν)
    (fun W q => TruncatedClaim.ofSelection ν keep (W q))
    (fun W _ q => (TruncatedClaim.ofSelection ν keep (W q)).width)
    (fun W S q => ((TruncatedClaim.faithful_ofSelection ν keep (W q)).forget S).encloses.dist_le)

/-- **Lineage deletion as an approximation map**; its error at a claim is the width it holds after
forgetting. -/
noncomputable def lineageCertificate (ν : σ → ℝ≥0) :
    ApproximationMap
      (AfterRetraction (forgetTokens (Claim := Claim)) fun W q => mass ν (W q))
      (Finset σ × Claim) ℝ≥0
      (AfterRetraction (fun S (c : Claim → LineageClaim σ) q => (c q).forget S)
        fun c q => (c q).evidence)
      (Finset σ × Claim) ℝ≥0 :=
  certified (forgetTokens (Claim := Claim)) (fun W q => mass ν (W q))
    (fun S (c : Claim → LineageClaim σ) q => (c q).forget S) (fun c q => (c q).evidence)
    (fun W q => LineageClaim.ofProvenance ν (W q))
    (fun W S q => ((LineageClaim.ofProvenance ν (W q)).forget S).width)
    (fun W S q => ((LineageClaim.faithful_ofProvenance ν (W q)).forget S).encloses.dist_le)

/-- **Confidence after deletion from truncated provenance** is within `k⁻¹` times the dropped
mass, by the approximation map and the Lipschitz readout. -/
theorem truncation_confidence (ν : σ → ℝ≥0) (keep : (σ →₀ ℕ) → Prop) [DecidablePred keep]
    {k : ℝ≥0} (hk : 0 < k) (W : ProvState Claim σ) (S : Finset σ) (q : Claim) :
    dist (confidence k (((TruncatedClaim.ofSelection ν keep (W q)).forget S).estimate ν))
        (confidence k (mass ν (deletion S (W q)))) ≤
      ((k⁻¹ : ℝ≥0) : ℝ) * (TruncatedClaim.ofSelection ν keep (W q)).width :=
  certified_measured (forgetTokens (Claim := Claim)) (fun W q => mass ν (W q))
    (fun S (c : Claim → TruncatedClaim σ) q => (c q).forget S) (fun c q => (c q).estimate ν)
    (fun W q => TruncatedClaim.ofSelection ν keep (W q))
    (fun W _ q => (TruncatedClaim.ofSelection ν keep (W q)).width)
    (fun W S q => ((TruncatedClaim.faithful_ofSelection ν keep (W q)).forget S).encloses.dist_le)
    (confidence k) k⁻¹ (confidence_lipschitz hk) W S q

end Certificates

/-! ## Controls -/

namespace Controls

open LineageClaim

/-- Every token is worth one: mass counts derivations. -/
def unit : ℕ → ℝ≥0 := fun _ => 1

/-- `100 x + y`, with `x` the token `0` and `y` the token `1`. -/
noncomputable def heavy : MvPolynomial ℕ ℕ := C 100 * X 0 + X 1

/-- The top-1 truncation of `heavy` keeps `100 x`; the width holds the dropped `y`. -/
noncomputable def heavyTop : TruncatedClaim ℕ := ⟨C 100 * X 0, 1⟩

theorem heavyTop_faithful : heavyTop.Faithful unit heavy :=
  ⟨X 1, rfl, by rw [mass_X]; exact le_rfl⟩

/-- **The truncation dropped the monomial that became the only support.**  After `x` is withdrawn
the held evidence is `0`, the exact evidence is `1`, and the width is `1`. -/
theorem heavy_after_deletion :
    (heavyTop.forget {0}).estimate unit = 0 ∧ mass unit (deletion {0} heavy) = 1 ∧
      (heavyTop.forget {0}).width = 1 := by
  refine ⟨?_, ?_, rfl⟩
  · show mass unit (deletion {0} (C 100 * X 0)) = 0
    rw [map_mul, deletion_C, deletion_X {0} 0, if_pos (Finset.mem_singleton_self 0), mul_zero,
      mass_zero]
  · rw [heavy, map_add, map_mul, deletion_C, deletion_X {0} 0, deletion_X {0} 1,
      if_pos (Finset.mem_singleton_self 0), if_neg (show (1 : ℕ) ∉ ({0} : Finset ℕ) by decide),
      mul_zero, zero_add, mass_X]
    rfl

/-- **The guard at the threshold.**  The certified interval `[0, 1]` makes the guard at threshold
`1` undecided; the guard on the point estimate commits `below`, and the exact evidence is `1`. -/
theorem heavy_guard :
    thresholdGuard (1 : ℝ≥0) 0 (0 + 1) = .undecided ∧ thresholdGuard (1 : ℝ≥0) 0 0 = .below ∧
      ¬ mass unit (deletion {0} heavy) < 1 := by
  refine ⟨thresholdGuard_undecided_iff.mpr ⟨zero_lt_one, (zero_add 1).ge⟩, ?_, ?_⟩
  · unfold thresholdGuard
    rw [if_neg (not_le.mpr (zero_lt_one : (0 : ℝ≥0) < 1)), if_pos (zero_lt_one : (0 : ℝ≥0) < 1)]
  · rw [heavy_after_deletion.2.1]
    exact lt_irrefl 1

/-- **Alternatives**: in `x + y`, withdrawing `x` drops the claim, while the derivation `y`
survives: the gap is one derivation. -/
theorem alternatives_gap :
    ((ofProvenance unit (X 0 + X 1)).forget {0}).evidence = 0 ∧
      mass unit (deletion {0} (X 0 + X 1 : MvPolynomial ℕ ℕ)) = 1 := by
  have del : deletion {0} (X 0 + X 1 : MvPolynomial ℕ ℕ) = X 1 := by
    rw [map_add, deletion_X {0} 0, deletion_X {0} 1, if_pos (Finset.mem_singleton_self 0),
      if_neg (show (1 : ℕ) ∉ ({0} : Finset ℕ) by decide), zero_add]
  have m₁ : mass unit (deletion {0} (X 0 + X 1 : MvPolynomial ℕ ℕ)) = 1 := by
    rw [del, mass_X]
    rfl
  have m₂ : mass unit (X 0 + X 1 : MvPolynomial ℕ ℕ) = 2 := by
    rw [mass_add, mass_X, mass_X]
    exact one_add_one_eq_two
  have meets : ¬ Disjoint (X 0 + X 1 : MvPolynomial ℕ ℕ).vars {0} :=
    meets_of_mass_ne (by rw [m₁, m₂]; exact ne_of_lt one_lt_two)
  exact ⟨(lineage_gap unit {0} (X 0 + X 1) meets).1, m₁⟩

/-- **Joint use**: in `x · y`, the claim is dropped and nothing survives: the gap is zero. -/
theorem joint_gap :
    ((ofProvenance unit (X 0 * X 1)).forget {0}).evidence = 0 ∧
      mass unit (deletion {0} (X 0 * X 1 : MvPolynomial ℕ ℕ)) = 0 := by
  have del : deletion {0} (X 0 * X 1 : MvPolynomial ℕ ℕ) = 0 := by
    rw [map_mul, deletion_X {0} 0, if_pos (Finset.mem_singleton_self 0), zero_mul]
  have m₀ : mass unit (deletion {0} (X 0 * X 1 : MvPolynomial ℕ ℕ)) = 0 := by
    rw [del, mass_zero]
  have m₁ : mass unit (X 0 * X 1 : MvPolynomial ℕ ℕ) = 1 := by
    rw [mass_mul, mass_X, mass_X]
    exact one_mul 1
  have meets : ¬ Disjoint (X 0 * X 1 : MvPolynomial ℕ ℕ).vars {0} :=
    meets_of_mass_ne (by rw [m₀, m₁]; exact zero_ne_one)
  exact ⟨(lineage_gap unit {0} (X 0 * X 1) meets).1, m₀⟩

/-- **Lineage deletion keeps information about the withdrawn tokens**: it is exact on clean claims
and inexact on `x + y`, so two polynomials that agree once `x` is withdrawn are told apart after
forgetting. -/
theorem lineage_leaks :
    ¬ ErasesUpToRecomputation
      (fun S (p : MvPolynomial ℕ ℕ) => (ofProvenance unit p).forget S) (fun S p => deletion S p) :=
  leaks_of_inexact (Q := Unit) (fun S p => deletion S p) LineageClaim.forget (ofProvenance unit)
    (fun p _ => mass unit p) (fun c _ => c.evidence) (fun S p => deletion_idempotent S p)
    (fun S p clean _ => lineage_vacuous unit S p clean) (S := {0}) (W := X 0 + X 1) (q := ())
    (by
      show ((ofProvenance unit (X 0 + X 1)).forget {0}).evidence ≠
        mass unit (deletion {0} (X 0 + X 1))
      rw [alternatives_gap.1, alternatives_gap.2]
      exact zero_ne_one)

/-- **The width remembers the withdrawn monomial.**  `x + z` and `x` agree once `z` is withdrawn;
their faithful truncations keep `x`, and still differ in width after forgetting `z`. -/
theorem truncation_width_remembers :
    deletion {2} (X 0 + X 2 : MvPolynomial ℕ ℕ) = deletion {2} (X 0) ∧
      (⟨X 0, 1⟩ : TruncatedClaim ℕ).Faithful unit (X 0 + X 2) ∧
      (⟨X 0, 0⟩ : TruncatedClaim ℕ).Faithful unit (X 0) ∧
      (⟨X 0, 1⟩ : TruncatedClaim ℕ).forget {2} ≠ (⟨X 0, 0⟩ : TruncatedClaim ℕ).forget {2} := by
  refine ⟨?_, ⟨X 2, rfl, by rw [mass_X]; exact le_rfl⟩, ⟨0, (add_zero _).symm, (mass_zero unit).le⟩,
    fun h => one_ne_zero (congrArg TruncatedClaim.width h)⟩
  rw [map_add, deletion_X {2} 0, deletion_X {2} 2,
    if_neg (show (0 : ℕ) ∉ ({2} : Finset ℕ) by decide),
    if_pos (Finset.mem_singleton_self 2), add_zero]

end Controls

end Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance

open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms mass_le_of_coeff_le
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms mass_deletion_le
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms mass_deletion
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms deletion_select
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms LineageClaim.Faithful.forget
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms LineageClaim.Faithful.encloses
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms LineageClaim.Faithful.revise
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms LineageClaim.Faithful.deduce
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms LineageClaim.forget_forget
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms LineageClaim.forget_of_disjoint
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms LineageClaim.forget_lineage
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms lineage_gap
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms lineage_vacuous
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms TruncatedClaim.Faithful.forget
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms TruncatedClaim.Faithful.encloses
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms TruncatedClaim.Faithful.revise
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms TruncatedClaim.Faithful.deduce
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms TruncatedClaim.forget_forget
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms TruncatedClaim.estimate_forget_of_disjoint
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms TruncatedClaim.forget_kept_vars
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms encloses_derived
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms mass_derived
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms truncated_derived_encloses
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms truncationCertificate
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms lineageCertificate
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms truncation_confidence
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms Controls.heavy_after_deletion
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms Controls.heavy_guard
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms Controls.alternatives_gap
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms Controls.joint_gap
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms Controls.lineage_leaks
open Mettapedia.PLN.WorldModel.ApproximateRetractionProvenance in
#print axioms Controls.truncation_width_remembers
