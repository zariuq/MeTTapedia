import Mettapedia.Logic.EvidenceQuantale
import Mathlib.Data.ENNReal.Operations

open scoped ENNReal

/-!
EvidenceHplusQuantale

This file packages the **parallel aggregation** operation `hplus` as a quantale.

Key point:
`hplus` does *not* distribute over the usual Evidence join (coordinatewise max),
because addition does not preserve `sSup` with `⊥ = 0`. To make hplus a quantale,
we use the **order-dual lattice**: `≤` is reversed, so `sSup` becomes coordinatewise `sInf`.

This keeps the tensor-quantale on `Evidence` unchanged, while giving a clean, sound
quantale instance for the additive (parallel) combination on a separate type.
-/

namespace Mettapedia.Logic.EvidenceQuantale

/-- Evidence with the **order-dual** lattice. -/
abbrev EvidenceHplus := OrderDual Evidence

namespace EvidenceHplus

@[simp] lemma ofDual_toEvidence (x : EvidenceHplus) : OrderDual.ofDual x = (x : Evidence) := rfl

@[simp] lemma toDual_ofEvidence (e : Evidence) : (OrderDual.toDual e : EvidenceHplus) = e := rfl

@[simp] lemma pos_image_toDual_preimage (S : Set EvidenceHplus) :
    Evidence.pos '' (OrderDual.toDual ⁻¹' S)
      = (fun b : EvidenceHplus => (OrderDual.ofDual b).pos) '' S := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨OrderDual.toDual e, ?_, rfl⟩
    simpa using he
  · rintro ⟨b, hb, rfl⟩
    refine ⟨OrderDual.ofDual b, ?_, rfl⟩
    simpa using hb

@[simp] lemma neg_image_toDual_preimage (S : Set EvidenceHplus) :
    Evidence.neg '' (OrderDual.toDual ⁻¹' S)
      = (fun b : EvidenceHplus => (OrderDual.ofDual b).neg) '' S := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨OrderDual.toDual e, ?_, rfl⟩
    simpa using he
  · rintro ⟨b, hb, rfl⟩
    refine ⟨OrderDual.ofDual b, ?_, rfl⟩
    simpa using hb

@[simp] lemma image_toDual_preimage {β} (f : Evidence → β) (S : Set EvidenceHplus) :
    f '' (OrderDual.toDual ⁻¹' S) = (fun b : EvidenceHplus => f (OrderDual.ofDual b)) '' S := by
  ext y
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨OrderDual.toDual e, ?_, rfl⟩
    simpa using he
  · rintro ⟨b, hb, rfl⟩
    refine ⟨OrderDual.ofDual b, ?_, rfl⟩
    simpa using hb

@[simp] lemma pos_sInf_toDual_preimage (S : Set EvidenceHplus) :
    (sInf (OrderDual.toDual ⁻¹' S)).pos =
      sInf ((fun b : EvidenceHplus => (OrderDual.ofDual b).pos) '' S) := by
  -- unfold the sInf on Evidence and rewrite the image
  change (Evidence.evidenceSInf (OrderDual.toDual ⁻¹' S)).pos =
    sInf ((fun b : EvidenceHplus => (OrderDual.ofDual b).pos) '' S)
  simp [Evidence.evidenceSInf, image_toDual_preimage]

@[simp] lemma neg_sInf_toDual_preimage (S : Set EvidenceHplus) :
    (sInf (OrderDual.toDual ⁻¹' S)).neg =
      sInf ((fun b : EvidenceHplus => (OrderDual.ofDual b).neg) '' S) := by
  change (Evidence.evidenceSInf (OrderDual.toDual ⁻¹' S)).neg =
    sInf ((fun b : EvidenceHplus => (OrderDual.ofDual b).neg) '' S)
  simp [Evidence.evidenceSInf, image_toDual_preimage]

/-- Parallel aggregation as multiplication on the dual lattice. -/
noncomputable def hplus (x y : EvidenceHplus) : EvidenceHplus :=
  OrderDual.toDual ((OrderDual.ofDual x) + (OrderDual.ofDual y))

noncomputable instance : Mul EvidenceHplus := ⟨hplus⟩

@[simp] lemma mul_def (x y : EvidenceHplus) :
    OrderDual.ofDual (x * y) = (OrderDual.ofDual x) + (OrderDual.ofDual y) := rfl

@[simp] lemma pos_mul (x y : EvidenceHplus) : (x * y).pos = x.pos + y.pos := by
  rfl

@[simp] lemma neg_mul (x y : EvidenceHplus) : (x * y).neg = x.neg + y.neg := by
  rfl

lemma hplus_assoc (x y z : EvidenceHplus) : (x * y) * z = x * (y * z) := by
  -- reduce to Evidence.hplus_assoc on the underlying type
  change OrderDual.ofDual ((x * y) * z) = OrderDual.ofDual (x * (y * z))
  calc
    OrderDual.ofDual ((x * y) * z)
        = OrderDual.ofDual (x * y) + OrderDual.ofDual z := rfl
    _   = (OrderDual.ofDual x + OrderDual.ofDual y) + OrderDual.ofDual z := rfl
    _   = OrderDual.ofDual x + (OrderDual.ofDual y + OrderDual.ofDual z) := by
            simpa [Evidence.hplus_def] using
              (Evidence.hplus_assoc (x := OrderDual.ofDual x)
                                    (y := OrderDual.ofDual y)
                                    (z := OrderDual.ofDual z))
    _   = OrderDual.ofDual x + OrderDual.ofDual (y * z) := rfl
    _   = OrderDual.ofDual (x * (y * z)) := rfl

lemma hplus_comm (x y : EvidenceHplus) : x * y = y * x := by
  change OrderDual.ofDual (x * y) = OrderDual.ofDual (y * x)
  calc
    OrderDual.ofDual (x * y) = OrderDual.ofDual x + OrderDual.ofDual y := rfl
    _ = OrderDual.ofDual y + OrderDual.ofDual x := by
          simpa [Evidence.hplus_def] using
            (Evidence.hplus_comm (x := OrderDual.ofDual x) (y := OrderDual.ofDual y))
    _ = OrderDual.ofDual (y * x) := rfl

noncomputable instance : Semigroup EvidenceHplus where
  mul := (· * ·)
  mul_assoc := hplus_assoc

noncomputable instance : CommSemigroup EvidenceHplus where
  mul_comm := hplus_comm

/-- hplus distributes over sSup in the **dual** lattice. -/
lemma hplus_sSup_right (a : EvidenceHplus) (S : Set EvidenceHplus) :
    a * sSup S = ⨆ b ∈ S, a * b := by
  classical
  -- work in Evidence via OrderDual.ofDual
  change OrderDual.ofDual (a * sSup S) = OrderDual.ofDual (⨆ b ∈ S, a * b)
  -- reduce to coordinatewise ENNReal facts
  apply Evidence.ext'
  · -- pos coordinate
    let s : Set ℝ≥0∞ := Evidence.pos '' (OrderDual.toDual ⁻¹' S)
    have hleft :
        (OrderDual.ofDual (a * sSup S)).pos = (OrderDual.ofDual a).pos + sInf s := by
      -- expand hplus and the dual sSup into Evidence-level operations
      change ((OrderDual.ofDual a) + (OrderDual.ofDual (sSup S))).pos =
        (OrderDual.ofDual a).pos + sInf s
      simp [Evidence.hplus_def, s, image_toDual_preimage]
    have hright :
        (OrderDual.ofDual (⨆ b ∈ S, a * b)).pos =
          sInf ((fun b : EvidenceHplus => (OrderDual.ofDual a).pos + (OrderDual.ofDual b).pos) '' S) := by
      -- rewrite the indexed sup as a set sup, then use ofDual_sSup
      have hs : (⨆ b ∈ S, a * b) = sSup ((fun b : EvidenceHplus => a * b) '' S) := by
        exact (sSup_image (f := fun b : EvidenceHplus => a * b) (s := S)).symm
      calc
        (OrderDual.ofDual (⨆ b ∈ S, a * b)).pos
            = (OrderDual.ofDual (sSup ((fun b : EvidenceHplus => a * b) '' S))).pos := by
                simp [hs]
        _ = (sInf (OrderDual.toDual ⁻¹' ((fun b : EvidenceHplus => a * b) '' S))).pos := by
              simp
        _ = sInf ((fun b : EvidenceHplus => (OrderDual.ofDual b).pos) '' ((fun b : EvidenceHplus => a * b) '' S)) := by
              exact (pos_sInf_toDual_preimage (S := (fun b : EvidenceHplus => a * b) '' S))
        _ = sInf ((fun b : EvidenceHplus => (OrderDual.ofDual a).pos + (OrderDual.ofDual b).pos) '' S) := by
              -- compute pos of hplus
              simp [Set.image_image]
    calc
      (OrderDual.ofDual (a * sSup S)).pos
          = (OrderDual.ofDual a).pos + sInf s := hleft
      _ = sInf ((fun b : ℝ≥0∞ => (OrderDual.ofDual a).pos + b) '' s) := by
            calc
              (OrderDual.ofDual a).pos + sInf s
                  = ⨅ b ∈ s, (OrderDual.ofDual a).pos + b := by
                      simpa using (ENNReal.add_sInf (a := (OrderDual.ofDual a).pos) (s := s))
              _ = sInf ((fun b : ℝ≥0∞ => (OrderDual.ofDual a).pos + b) '' s) := by
                    simp [sInf_image]
      _ = sInf ((fun b : EvidenceHplus => (OrderDual.ofDual a).pos + (OrderDual.ofDual b).pos) '' S) := by
            simp [s, image_toDual_preimage, Set.image_image]
      _ = (OrderDual.ofDual (⨆ b ∈ S, a * b)).pos := by
            symm; exact hright
  · -- neg coordinate
    let s : Set ℝ≥0∞ := Evidence.neg '' (OrderDual.toDual ⁻¹' S)
    have hleft :
        (OrderDual.ofDual (a * sSup S)).neg = (OrderDual.ofDual a).neg + sInf s := by
      change ((OrderDual.ofDual a) + (OrderDual.ofDual (sSup S))).neg =
        (OrderDual.ofDual a).neg + sInf s
      simp [Evidence.hplus_def, s, image_toDual_preimage]
    have hright :
        (OrderDual.ofDual (⨆ b ∈ S, a * b)).neg =
          sInf ((fun b : EvidenceHplus => (OrderDual.ofDual a).neg + (OrderDual.ofDual b).neg) '' S) := by
      have hs : (⨆ b ∈ S, a * b) = sSup ((fun b : EvidenceHplus => a * b) '' S) := by
        exact (sSup_image (f := fun b : EvidenceHplus => a * b) (s := S)).symm
      calc
        (OrderDual.ofDual (⨆ b ∈ S, a * b)).neg
            = (OrderDual.ofDual (sSup ((fun b : EvidenceHplus => a * b) '' S))).neg := by
                simp [hs]
        _ = (sInf (OrderDual.toDual ⁻¹' ((fun b : EvidenceHplus => a * b) '' S))).neg := by
              simp
        _ = sInf ((fun b : EvidenceHplus => (OrderDual.ofDual b).neg) '' ((fun b : EvidenceHplus => a * b) '' S)) := by
              exact (neg_sInf_toDual_preimage (S := (fun b : EvidenceHplus => a * b) '' S))
        _ = sInf ((fun b : EvidenceHplus => (OrderDual.ofDual a).neg + (OrderDual.ofDual b).neg) '' S) := by
              simp [Set.image_image]
    calc
      (OrderDual.ofDual (a * sSup S)).neg
          = (OrderDual.ofDual a).neg + sInf s := hleft
      _ = sInf ((fun b : ℝ≥0∞ => (OrderDual.ofDual a).neg + b) '' s) := by
            calc
              (OrderDual.ofDual a).neg + sInf s
                  = ⨅ b ∈ s, (OrderDual.ofDual a).neg + b := by
                      simpa using (ENNReal.add_sInf (a := (OrderDual.ofDual a).neg) (s := s))
              _ = sInf ((fun b : ℝ≥0∞ => (OrderDual.ofDual a).neg + b) '' s) := by
                    simp [sInf_image]
      _ = sInf ((fun b : EvidenceHplus => (OrderDual.ofDual a).neg + (OrderDual.ofDual b).neg) '' S) := by
            simp [s, image_toDual_preimage, Set.image_image]
      _ = (OrderDual.ofDual (⨆ b ∈ S, a * b)).neg := by
            symm; exact hright

/-- hplus distributes over sSup on the left (dual lattice). -/
lemma hplus_sSup_left (S : Set EvidenceHplus) (a : EvidenceHplus) :
    sSup S * a = ⨆ b ∈ S, b * a := by
  -- commutativity reduces to right distributivity
  simpa [hplus_comm] using hplus_sSup_right a S

instance : Mettapedia.Algebra.QuantaleWeakness.IsCommQuantale EvidenceHplus :=
  Mettapedia.Algebra.QuantaleWeakness.IsCommQuantale.ofCommSemigroup hplus_sSup_right

end EvidenceHplus
end Mettapedia.Logic.EvidenceQuantale
