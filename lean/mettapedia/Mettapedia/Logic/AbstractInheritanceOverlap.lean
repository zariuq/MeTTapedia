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

/-- Raw stamped-packet addition: additive evidence plus union provenance.
This helper is intentionally explicit rather than a global typeclass instance,
because overlap-aware code should not discover it accidentally via `+`. -/
noncomputable def rawAdd : StampedBinaryEvidence Stamp → StampedBinaryEvidence Stamp → StampedBinaryEvidence Stamp :=
  revise

/-- Raw stamped-packet zero for the explicit additive helper surface. -/
noncomputable def rawZero : StampedBinaryEvidence Stamp := empty

@[simp] theorem rawAdd_evidence (x y : StampedBinaryEvidence Stamp) :
    (rawAdd x y).evidence = x.evidence + y.evidence := rfl

@[simp] theorem rawAdd_stamp (x y : StampedBinaryEvidence Stamp) :
    (rawAdd x y).stamp = x.stamp ∪ y.stamp := rfl

/-- Explicit additive structure for raw stamped packets.
This is kept available for bridge proofs, but is not exported as a global
instance because raw stamped addition can double-count overlapping provenance. -/
noncomputable def rawAddCommMonoid : AddCommMonoid (StampedBinaryEvidence Stamp) where
  add := rawAdd
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
  zero := rawZero
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
  nsmul n x := Nat.rec rawZero (fun _ acc => rawAdd acc x) n
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
      change (a ∈ x.stamp ∪ y.stamp) ↔ a ∈ y.stamp ∪ x.stamp
      simp [or_comm]

/-- Explicit `EvidenceType` wrapper for the raw stamped additive packet algebra. -/
noncomputable def rawEvidenceType : EvidenceType (StampedBinaryEvidence Stamp) where
  toAddCommMonoid := rawAddCommMonoid

/-- Explicit additive-world-model view of raw stamped packets. -/
noncomputable def rawAdditiveWorldModel :
    letI : EvidenceType (StampedBinaryEvidence Stamp) := rawEvidenceType
    AdditiveWorldModel (StampedBinaryEvidence Stamp) Unit BinaryEvidence := by
  letI : EvidenceType (StampedBinaryEvidence Stamp) := rawEvidenceType
  exact
    { extract := fun W _ => W.evidence
      extract_add := by
        intro _ _ _
        rfl }

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
@[simp] theorem sum_stampContribution_pos
    (S : Finset (WitnessStamp Obj Attr)) :
    (S.sum stampContribution).pos =
      ∑ x ∈ S, (stampContribution x).pos := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp [ha, ih, BinaryEvidence.hplus_def]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem sum_stampContribution_neg
    (S : Finset (WitnessStamp Obj Attr)) :
    (S.sum stampContribution).neg =
      ∑ x ∈ S, (stampContribution x).neg := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp [ha, ih, BinaryEvidence.hplus_def]

omit [Fintype Obj] [Fintype Attr] [DecidableEq Obj] [DecidableEq Attr] in
theorem sum_stampContribution_pos_coord_ne_top
    (S : Finset (WitnessStamp Obj Attr)) :
    (∑ x ∈ S, (stampContribution x).pos) ≠ ∞ := by
  rw [ENNReal.sum_ne_top]
  intro x _hx
  cases x <;> simp [stampContribution]

omit [Fintype Obj] [Fintype Attr] [DecidableEq Obj] [DecidableEq Attr] in
theorem sum_stampContribution_neg_coord_ne_top
    (S : Finset (WitnessStamp Obj Attr)) :
    (∑ x ∈ S, (stampContribution x).neg) ≠ ∞ := by
  rw [ENNReal.sum_ne_top]
  intro x _hx
  cases x <;> simp [stampContribution]

/-- Evidence generated exactly by a finite set of witness stamps. -/
noncomputable def stampSetEvidence
    (S : Finset (WitnessStamp Obj Attr)) :
    BinaryEvidence :=
  S.sum stampContribution

/-- A source-level stamped packet whose evidence is exactly the contribution of
its finite provenance set. -/
noncomputable def stampSetPacket
    (S : Finset (WitnessStamp Obj Attr)) :
    StampedBinaryEvidence (WitnessStamp Obj Attr) where
  evidence := stampSetEvidence S
  stamp := S

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
theorem correctedMerge_stampSetPacket_evidence_eq_union
    (S T : Finset (WitnessStamp Obj Attr)) :
    (correctedMerge (stampSetPacket S) (stampSetPacket T)).evidence =
      stampSetEvidence (S ∪ T) := by
  apply BinaryEvidence.ext'
  · have h := congrArg BinaryEvidence.pos
      (Finset.sum_union_inter (s₁ := S) (s₂ := T)
        (f := stampContribution))
    simp [stampSetEvidence, stampSetPacket, correctedMerge, overlapEvidence,
      BinaryEvidence.hplus_def, EvidenceQuantale.BinaryEvidence.sub_def] at h ⊢
    rw [← h]
    exact ENNReal.add_sub_cancel_right
      (sum_stampContribution_pos_coord_ne_top (S ∩ T))
  · have h := congrArg BinaryEvidence.neg
      (Finset.sum_union_inter (s₁ := S) (s₂ := T)
        (f := stampContribution))
    simp [stampSetEvidence, stampSetPacket, correctedMerge, overlapEvidence,
      BinaryEvidence.hplus_def, EvidenceQuantale.BinaryEvidence.sub_def] at h ⊢
    rw [← h]
    exact ENNReal.add_sub_cancel_right
      (sum_stampContribution_neg_coord_ne_top (S ∩ T))

omit [Fintype Obj] [Fintype Attr] in
theorem correctedMerge_stampSetPacket_eq_union
    (S T : Finset (WitnessStamp Obj Attr)) :
    correctedMerge (stampSetPacket S) (stampSetPacket T) =
      stampSetPacket (S ∪ T) := by
  apply StampedBinaryEvidence.ext
  · exact correctedMerge_stampSetPacket_evidence_eq_union S T
  · simp [stampSetPacket, correctedMerge]

/-- N-ary source-level joint merge for exact stamp-set packets.

This is the provenance/factor version of overlap-corrected Revision: merge the
sources, not merely their already-flattened truth values. -/
noncomputable def stampSetPacketJointMerge :
    List (Finset (WitnessStamp Obj Attr)) →
      StampedBinaryEvidence (WitnessStamp Obj Attr)
  | [] => stampSetPacket ∅
  | S :: Ss => correctedMerge (stampSetPacket S) (stampSetPacketJointMerge Ss)

/-- The finite source union represented by an n-ary stamp-set packet merge. -/
def stampSetListUnion
    (Ss : List (Finset (WitnessStamp Obj Attr))) :
    Finset (WitnessStamp Obj Attr) :=
  Ss.foldr (fun S acc => S ∪ acc) ∅

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetListUnion_nil :
    stampSetListUnion
      ([] : List (Finset (WitnessStamp Obj Attr))) = ∅ := rfl

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetListUnion_cons
    (S : Finset (WitnessStamp Obj Attr))
    (Ss : List (Finset (WitnessStamp Obj Attr))) :
    stampSetListUnion (S :: Ss) = S ∪ stampSetListUnion Ss := rfl

omit [Fintype Obj] [Fintype Attr] in
/-- N-ary overlap-corrected Revision of exact source packets is exactly one
packet over the union of all source stamps.  In particular, repeated provenance
is counted once at the source level rather than becoming extra confidence. -/
theorem stampSetPacketJointMerge_eq_union
    (Ss : List (Finset (WitnessStamp Obj Attr))) :
    stampSetPacketJointMerge Ss = stampSetPacket (stampSetListUnion Ss) := by
  induction Ss with
  | nil =>
      rfl
  | cons S Ss ih =>
      simp [stampSetPacketJointMerge, ih, correctedMerge_stampSetPacket_eq_union]

omit [Fintype Obj] [Fintype Attr] in
/-- Duplicate exact source packets collapse to one packet; this is the n-ary
joint-factor boundary case that raw additive Revision would get wrong. -/
theorem stampSetPacketJointMerge_duplicate_eq_single
    (S : Finset (WitnessStamp Obj Attr)) :
    stampSetPacketJointMerge [S, S] = stampSetPacket S := by
  simp [stampSetPacketJointMerge, correctedMerge_stampSetPacket_eq_union]

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
    letI : EvidenceType (StampedBinaryEvidence (WitnessStamp Obj Attr)) :=
      StampedBinaryEvidence.rawEvidenceType
    letI : AdditiveWorldModel (StampedBinaryEvidence (WitnessStamp Obj Attr)) Unit BinaryEvidence :=
      StampedBinaryEvidence.rawAdditiveWorldModel
    OverlapLayer
      (StampedBinaryEvidence (WitnessStamp Obj Attr))
      Unit
      BinaryEvidence
      BinaryEvidence := by
  letI : EvidenceType (StampedBinaryEvidence (WitnessStamp Obj Attr)) :=
    StampedBinaryEvidence.rawEvidenceType
  letI : AdditiveWorldModel (StampedBinaryEvidence (WitnessStamp Obj Attr)) Unit BinaryEvidence :=
    StampedBinaryEvidence.rawAdditiveWorldModel
  exact
    { merge := correctedMerge
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
          simp [correctedMerge, overlapEvidence_eq_zero_of_stampDisjoint, h] }

omit [Fintype Obj] [Fintype Attr] in
theorem witnessStampOverlapLayer_additive_of_stampDisjoint
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (h : StampedBinaryEvidence.StampDisjoint x y) :
    letI : EvidenceType (StampedBinaryEvidence (WitnessStamp Obj Attr)) :=
      StampedBinaryEvidence.rawEvidenceType
    letI : AdditiveWorldModel (StampedBinaryEvidence (WitnessStamp Obj Attr)) Unit BinaryEvidence :=
      StampedBinaryEvidence.rawAdditiveWorldModel
    ((witnessStampOverlapLayer (Obj := Obj) (Attr := Attr)).merge x y).evidence =
      x.evidence + y.evidence := by
  letI : EvidenceType (StampedBinaryEvidence (WitnessStamp Obj Attr)) :=
    StampedBinaryEvidence.rawEvidenceType
  letI : AdditiveWorldModel (StampedBinaryEvidence (WitnessStamp Obj Attr)) Unit BinaryEvidence :=
    StampedBinaryEvidence.rawAdditiveWorldModel
  change (correctedMerge x y).evidence = x.evidence + y.evidence
  apply BinaryEvidence.ext' <;>
    simp [correctedMerge, overlapEvidence_eq_zero_of_stampDisjoint, h]

/-! ### Revision-overlap boundary canaries

These small concrete theorems pin the Revision provenance boundary used by the
WM-PLN executable witnesses: disjoint stamps reduce to raw additive revision,
while repeated provenance does not double-count the same witness packet. -/

inductive RevisionOverlapCanaryObj where
  | left
  | right
  deriving DecidableEq, Fintype

inductive RevisionOverlapCanaryAttr where
  | only
  deriving DecidableEq, Fintype

/-- One positive extensional witness packet at the left canary object. -/
noncomputable def revisionOverlapCanaryLeftPacket :
    StampedBinaryEvidence
      (WitnessStamp RevisionOverlapCanaryObj RevisionOverlapCanaryAttr) where
  evidence := ⟨1, 0⟩
  stamp := {WitnessStamp.posExt RevisionOverlapCanaryObj.left}

/-- One positive extensional witness packet at the right canary object. -/
noncomputable def revisionOverlapCanaryRightPacket :
    StampedBinaryEvidence
      (WitnessStamp RevisionOverlapCanaryObj RevisionOverlapCanaryAttr) where
  evidence := ⟨1, 0⟩
  stamp := {WitnessStamp.posExt RevisionOverlapCanaryObj.right}

/-- Positive canary: when provenance is disjoint, overlap correction is just raw
additive revision. -/
theorem correctedMerge_disjointCanary_eq_rawAdd :
    correctedMerge revisionOverlapCanaryLeftPacket revisionOverlapCanaryRightPacket =
      StampedBinaryEvidence.rawAdd
        revisionOverlapCanaryLeftPacket
        revisionOverlapCanaryRightPacket := by
  rw [correctedMerge_eq_revise_of_stampDisjoint]
  · rfl
  · simp [StampedBinaryEvidence.StampDisjoint, revisionOverlapCanaryLeftPacket,
      revisionOverlapCanaryRightPacket]

/-- Negative canary: merging the same provenance packet with itself keeps one
copy of the evidence rather than inflating to two. -/
theorem correctedMerge_selfCanary_evidence_eq_single :
    (correctedMerge
        revisionOverlapCanaryLeftPacket
        revisionOverlapCanaryLeftPacket).evidence = ⟨1, 0⟩ := by
  apply BinaryEvidence.ext' <;>
    simp [correctedMerge, overlapEvidence, revisionOverlapCanaryLeftPacket,
      stampContribution, BinaryEvidence.hplus_def,
      EvidenceQuantale.BinaryEvidence.sub_def]

/-- Raw additive revision is deliberately exposed as unsafe at overlapping
provenance: the same one-witness packet would count as two positive witnesses. -/
theorem rawAdd_selfCanary_evidence_eq_double :
    (StampedBinaryEvidence.rawAdd
        revisionOverlapCanaryLeftPacket
        revisionOverlapCanaryLeftPacket).evidence = ⟨2, 0⟩ := by
  apply BinaryEvidence.ext'
  · simp [StampedBinaryEvidence.rawAdd, StampedBinaryEvidence.revise,
      revisionOverlapCanaryLeftPacket, BinaryEvidence.hplus_def]
    norm_num
  · simp [StampedBinaryEvidence.rawAdd, StampedBinaryEvidence.revise,
      revisionOverlapCanaryLeftPacket, BinaryEvidence.hplus_def]

/-- The corrected and raw overlapping revisions are observationally different
on the canary packet, so overlap correction is not cosmetic. -/
theorem correctedMerge_selfCanary_evidence_ne_rawAdd :
    (correctedMerge
        revisionOverlapCanaryLeftPacket
        revisionOverlapCanaryLeftPacket).evidence ≠
      (StampedBinaryEvidence.rawAdd
          revisionOverlapCanaryLeftPacket
          revisionOverlapCanaryLeftPacket).evidence := by
  intro h
  have hpos := congrArg BinaryEvidence.pos h
  simp [correctedMerge, overlapEvidence, revisionOverlapCanaryLeftPacket,
    stampContribution, StampedBinaryEvidence.rawAdd,
    StampedBinaryEvidence.revise, BinaryEvidence.hplus_def,
    EvidenceQuantale.BinaryEvidence.sub_def] at hpos
  norm_num at hpos

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
