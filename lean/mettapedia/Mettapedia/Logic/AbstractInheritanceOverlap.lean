import Mettapedia.Logic.AbstractInheritanceStampedWitness
import Mettapedia.Logic.WorldModelOverlap

/-!
# Overlap Bridge for Stamped Abstract Inheritance

This module connects the stamped witness packets from `AbstractInheritance` to the
generic overlap-correction surface:

- stamped packets form an additive state by evidence-addition + stamp union
- shared witness stamps induce a concrete overlap evidence
- overlap-corrected merge recovers additive revision exactly when stamps are disjoint

This is the missing theorem-level bridge between inheritance provenance and the
generic WM overlap layer.
-/

namespace Mettapedia.Logic.EvidenceQuantale.BinaryEvidence

open scoped ENNReal

/-- Coordinatewise truncated subtraction on binary evidence. -/
noncomputable instance : Sub BinaryEvidence where
  sub x y := ⟨x.pos - y.pos, x.neg - y.neg⟩

@[simp] theorem sub_def (x y : BinaryEvidence) :
    x - y = ⟨x.pos - y.pos, x.neg - y.neg⟩ := rfl

@[simp] theorem zero_pos : (0 : BinaryEvidence).pos = 0 := rfl

@[simp] theorem zero_neg : (0 : BinaryEvidence).neg = 0 := rfl

@[simp] theorem sub_zero (x : BinaryEvidence) : x - 0 = x := by
  apply BinaryEvidence.ext'
  · simp [sub_def]
  · simp [sub_def]

end Mettapedia.Logic.EvidenceQuantale.BinaryEvidence

namespace Mettapedia.Logic.AbstractInheritance

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelGeneric
open scoped ENNReal

universe u v w

namespace StampedBinaryEvidence

variable {Stamp : Type u} [DecidableEq Stamp]

noncomputable instance : Add (StampedBinaryEvidence Stamp) := ⟨revise⟩

noncomputable instance : Zero (StampedBinaryEvidence Stamp) := ⟨empty⟩

@[simp] theorem add_evidence (x y : StampedBinaryEvidence Stamp) :
    (x + y).evidence = x.evidence + y.evidence := rfl

@[simp] theorem add_stamp (x y : StampedBinaryEvidence Stamp) :
    (x + y).stamp = x.stamp ∪ y.stamp := rfl

noncomputable instance : AddCommMonoid (StampedBinaryEvidence Stamp) where
  add := (· + ·)
  add_assoc x y z := by
    apply StampedBinaryEvidence.ext
    · apply BinaryEvidence.ext'
      · change (x.evidence.pos + y.evidence.pos) + z.evidence.pos =
          x.evidence.pos + (y.evidence.pos + z.evidence.pos)
        simp [add_assoc]
      · change (x.evidence.neg + y.evidence.neg) + z.evidence.neg =
          x.evidence.neg + (y.evidence.neg + z.evidence.neg)
        simp [add_assoc]
    · ext a
      change (a ∈ (x.stamp ∪ y.stamp) ∪ z.stamp) ↔ a ∈ x.stamp ∪ (y.stamp ∪ z.stamp)
      simp
  zero := 0
  zero_add x := by
    apply StampedBinaryEvidence.ext
    · apply BinaryEvidence.ext'
      · change (0 : ℝ≥0∞) + x.evidence.pos = x.evidence.pos
        simp
      · change (0 : ℝ≥0∞) + x.evidence.neg = x.evidence.neg
        simp
    · ext a
      change (a ∈ (∅ : Finset Stamp) ∪ x.stamp) ↔ a ∈ x.stamp
      simp
  add_zero x := by
    apply StampedBinaryEvidence.ext
    · apply BinaryEvidence.ext'
      · change x.evidence.pos + (0 : ℝ≥0∞) = x.evidence.pos
        simp
      · change x.evidence.neg + (0 : ℝ≥0∞) = x.evidence.neg
        simp
    · ext a
      change (a ∈ x.stamp ∪ (∅ : Finset Stamp)) ↔ a ∈ x.stamp
      simp
  nsmul := nsmulRec
  nsmul_zero := by
    intro x
    rfl
  nsmul_succ := by
    intro n x
    rfl
  add_comm x y := by
    apply StampedBinaryEvidence.ext
    · apply BinaryEvidence.ext'
      · change x.evidence.pos + y.evidence.pos = y.evidence.pos + x.evidence.pos
        simp [add_comm]
      · change x.evidence.neg + y.evidence.neg = y.evidence.neg + x.evidence.neg
        simp [add_comm]
    · ext a
      simp [Finset.mem_union, or_comm]

noncomputable instance : EvidenceType (StampedBinaryEvidence Stamp) where
  toAddCommMonoid := inferInstance

noncomputable instance instAdditiveWorldModel :
    AdditiveWorldModel (StampedBinaryEvidence Stamp) Unit BinaryEvidence where
  extract W _ := W.evidence
  extract_add _ _ _ := rfl

end StampedBinaryEvidence

namespace DualConcept

section Finite

variable {Obj : Type u} {Attr : Type v}
variable [Fintype Obj] [DecidableEq Obj] [Fintype Attr] [DecidableEq Attr]

/-- The binary-evidence contribution of one witness stamp. -/
noncomputable def stampContribution : WitnessStamp Obj Attr → BinaryEvidence
  | .posExt _ => ⟨1, 0⟩
  | .posInt _ => ⟨1, 0⟩
  | .negExt _ => ⟨0, 1⟩
  | .negInt _ => ⟨0, 1⟩

/-- Shared-stamp overlap viewed as binary evidence. -/
noncomputable def overlapEvidence
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr)) :
    BinaryEvidence :=
  (x.stamp ∩ y.stamp).sum stampContribution

omit [Fintype Obj] [Fintype Attr] in
theorem overlapEvidence_comm
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr)) :
    overlapEvidence x y = overlapEvidence y x := by
  simp [overlapEvidence, Finset.inter_comm]

omit [Fintype Obj] [Fintype Attr] in
theorem inter_stamp_eq_empty_of_stampDisjoint
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (h : StampedBinaryEvidence.StampDisjoint x y) :
    x.stamp ∩ y.stamp = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hmem : a ∈ x.stamp ∧ a ∈ y.stamp := by
    simpa [Finset.mem_inter] using ha
  exact (Finset.disjoint_left.mp h hmem.1) hmem.2

omit [Fintype Obj] [Fintype Attr] in
theorem overlapEvidence_eq_zero_of_stampDisjoint
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (h : StampedBinaryEvidence.StampDisjoint x y) :
    overlapEvidence x y = 0 := by
  have hinter : x.stamp ∩ y.stamp = ∅ := inter_stamp_eq_empty_of_stampDisjoint x y h
  simp [overlapEvidence, hinter]

/-- Overlap-corrected merge: union provenance, subtract shared witness mass once. -/
noncomputable def correctedMerge
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr)) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) where
  evidence := x.evidence + y.evidence - overlapEvidence x y
  stamp := x.stamp ∪ y.stamp

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem correctedMerge_evidence
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr)) :
    (correctedMerge x y).evidence = x.evidence + y.evidence - overlapEvidence x y := rfl

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem correctedMerge_stamp
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr)) :
    (correctedMerge x y).stamp = x.stamp ∪ y.stamp := rfl

omit [Fintype Obj] [Fintype Attr] in
theorem correctedMerge_eq_revise_of_stampDisjoint
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (h : StampedBinaryEvidence.StampDisjoint x y) :
    correctedMerge x y = StampedBinaryEvidence.revise x y := by
  apply StampedBinaryEvidence.ext
  · apply BinaryEvidence.ext' <;>
      simp [correctedMerge, StampedBinaryEvidence.revise,
        overlapEvidence_eq_zero_of_stampDisjoint, h]
  · rfl

/-- Concrete stamped-overlap layer for inheritance witness packets. -/
noncomputable def witnessStampOverlapLayer :
    OverlapLayer
      (StampedBinaryEvidence (WitnessStamp Obj Attr))
      Unit
      BinaryEvidence
      BinaryEvidence where
  merge := correctedMerge
  overlap := fun x y _ => overlapEvidence x y
  combine := fun e₁ e₂ ov => e₁ + e₂ - ov
  independent := fun x y _ => StampedBinaryEvidence.StampDisjoint x y
  evidence_merge := by
    intro x y q
    cases q
    rfl
  additive_of_independent := by
    intro x y q h
    cases q
    change (correctedMerge x y).evidence = x.evidence + y.evidence
    apply BinaryEvidence.ext' <;>
      simp [correctedMerge, overlapEvidence_eq_zero_of_stampDisjoint, h]

omit [Fintype Obj] [Fintype Attr] in
theorem witnessStampOverlapLayer_additive_of_stampDisjoint
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (h : StampedBinaryEvidence.StampDisjoint x y) :
    AdditiveWorldModel.extract
      (State := StampedBinaryEvidence (WitnessStamp Obj Attr))
      (Query := Unit) (Ev := BinaryEvidence)
      ((witnessStampOverlapLayer (Obj := Obj) (Attr := Attr)).merge x y) () =
    AdditiveWorldModel.extract
      (State := StampedBinaryEvidence (WitnessStamp Obj Attr))
      (Query := Unit) (Ev := BinaryEvidence) x () +
    AdditiveWorldModel.extract
      (State := StampedBinaryEvidence (WitnessStamp Obj Attr))
      (Query := Unit) (Ev := BinaryEvidence) y () := by
  exact OverlapLayer.additive_of_independent'
    (L := witnessStampOverlapLayer (Obj := Obj) (Attr := Attr))
    x y () h

theorem correctedMerge_positive_negative_eq_finiteInheritanceStampedEvidence
    (A B : DualConcept Obj Attr) :
    correctedMerge (positiveStampedEvidence A B) (negativeStampedEvidence A B) =
      finiteInheritanceStampedEvidence A B := by
  simpa [finiteInheritanceStampedEvidence] using
    correctedMerge_eq_revise_of_stampDisjoint
      (positiveStampedEvidence A B)
      (negativeStampedEvidence A B)
      (positive_negative_stampDisjoint A B)

theorem correctedMerge_positive_negative_evidence_eq_finiteInheritanceEvidence
    (A B : DualConcept Obj Attr) :
    (correctedMerge (positiveStampedEvidence A B) (negativeStampedEvidence A B)).evidence =
      finiteInheritanceEvidence A B := by
  rw [correctedMerge_positive_negative_eq_finiteInheritanceStampedEvidence]
  exact finiteInheritanceStampedEvidence_evidence_eq A B

end Finite

end DualConcept

end Mettapedia.Logic.AbstractInheritance
