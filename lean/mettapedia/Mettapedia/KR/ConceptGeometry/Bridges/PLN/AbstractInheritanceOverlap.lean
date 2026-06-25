import Mettapedia.KR.ConceptGeometry.AbstractInheritanceStampedWitness
import Mettapedia.PLN.WorldModel.WorldModelOverlap

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

namespace Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence

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

end Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence

namespace Mettapedia.KR.ConceptGeometry.AbstractInheritance

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WorldModelOverlap
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
@[reducible] noncomputable def rawAddCommMonoid :
    AddCommMonoid (StampedBinaryEvidence Stamp) where
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
@[reducible] noncomputable def rawEvidenceType :
    EvidenceType (StampedBinaryEvidence Stamp) where
  toAddCommMonoid := rawAddCommMonoid

/-- Explicit additive-world-model view of raw stamped packets. -/
@[reducible] noncomputable def rawAdditiveWorldModel :
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

/-- A rule-family packet is exact when its evidence is precisely the sum of the
finite witness contributions named by its provenance stamp set.  This is the
interface later consumers should discharge before using source-union Revision
theorems. -/
def ExactStampPacket
    (x : StampedBinaryEvidence (WitnessStamp Obj Attr)) : Prop :=
  x.evidence = stampSetEvidence x.stamp

omit [Fintype Obj] [Fintype Attr] [DecidableEq Obj] [DecidableEq Attr] in
@[simp] theorem stampSetPacket_exact
    (S : Finset (WitnessStamp Obj Attr)) :
    ExactStampPacket (stampSetPacket S) := rfl

omit [Fintype Obj] [Fintype Attr] [DecidableEq Obj] [DecidableEq Attr] in
theorem eq_stampSetPacket_of_exact
    (x : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (hx : ExactStampPacket x) :
    x = stampSetPacket x.stamp := by
  apply StampedBinaryEvidence.ext
  · exact hx
  · simp [stampSetPacket]

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
      BinaryEvidence.hplus_def, Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.sub_def] at h ⊢
    rw [← h]
    exact ENNReal.add_sub_cancel_right
      (sum_stampContribution_pos_coord_ne_top (S ∩ T))
  · have h := congrArg BinaryEvidence.neg
      (Finset.sum_union_inter (s₁ := S) (s₂ := T)
        (f := stampContribution))
    simp [stampSetEvidence, stampSetPacket, correctedMerge, overlapEvidence,
      BinaryEvidence.hplus_def, Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.sub_def] at h ⊢
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

omit [Fintype Obj] [Fintype Attr] in
theorem correctedMerge_eq_stampSetPacket_union_of_exact
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (hx : ExactStampPacket x) (hy : ExactStampPacket y) :
    correctedMerge x y = stampSetPacket (x.stamp ∪ y.stamp) := by
  rw [eq_stampSetPacket_of_exact x hx, eq_stampSetPacket_of_exact y hy]
  exact correctedMerge_stampSetPacket_eq_union x.stamp y.stamp

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

/-- The finite source union represented by a list of already-built stamped
packets. -/
def packetListUnion
    (xs : List (StampedBinaryEvidence (WitnessStamp Obj Attr))) :
    Finset (WitnessStamp Obj Attr) :=
  xs.foldr (fun x acc => x.stamp ∪ acc) ∅

/-- N-ary source-level joint merge for already-built stamped packets.

Unlike `StampedBinaryEvidence.listRevise`, this operation is overlap-aware:
repeated provenance contributes once through `correctedMerge`.  The main theorem
below says exact packets collapse to the packet over the source-union. -/
noncomputable def packetJointMerge :
    List (StampedBinaryEvidence (WitnessStamp Obj Attr)) →
      StampedBinaryEvidence (WitnessStamp Obj Attr)
  | [] => stampSetPacket ∅
  | x :: xs => correctedMerge x (packetJointMerge xs)

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
@[simp] theorem packetListUnion_nil :
    packetListUnion
      ([] : List (StampedBinaryEvidence (WitnessStamp Obj Attr))) = ∅ := rfl

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem packetListUnion_cons
    (x : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (xs : List (StampedBinaryEvidence (WitnessStamp Obj Attr))) :
    packetListUnion (x :: xs) = x.stamp ∪ packetListUnion xs := rfl

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem packetJointMerge_nil :
    packetJointMerge
      ([] : List (StampedBinaryEvidence (WitnessStamp Obj Attr))) =
        stampSetPacket ∅ := rfl

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem packetJointMerge_cons
    (x : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (xs : List (StampedBinaryEvidence (WitnessStamp Obj Attr))) :
    packetJointMerge (x :: xs) = correctedMerge x (packetJointMerge xs) := rfl

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
/-- N-ary overlap-corrected Revision of already-built exact packets is exactly
one packet over the union of their source stamps.  This is the consumer-facing
form of `stampSetPacketJointMerge_eq_union`: rule-family packets only need to
prove `ExactStampPacket`, not expose how their stamps were constructed. -/
theorem packetJointMerge_eq_stampSetPacket_packetListUnion_of_exact
    (xs : List (StampedBinaryEvidence (WitnessStamp Obj Attr)))
    (hExact : ∀ x ∈ xs, ExactStampPacket x) :
    packetJointMerge xs = stampSetPacket (packetListUnion xs) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hx : ExactStampPacket x := hExact x (by simp)
      have hExactTail : ∀ y ∈ xs, ExactStampPacket y := by
        intro y hy
        exact hExact y (by simp [hy])
      have hTail :
          packetJointMerge xs = stampSetPacket (packetListUnion xs) :=
        ih hExactTail
      rw [packetJointMerge_cons, hTail, packetListUnion_cons]
      exact correctedMerge_eq_stampSetPacket_union_of_exact
        x (stampSetPacket (packetListUnion xs)) hx (stampSetPacket_exact _)

omit [Fintype Obj] [Fintype Attr] in
/-- Duplicate exact source packets collapse to one source packet even when the
packets were built by a rule family rather than introduced as raw stamp sets. -/
theorem packetJointMerge_duplicate_eq_single_of_exact
    (x : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (hx : ExactStampPacket x) :
    packetJointMerge [x, x] = stampSetPacket x.stamp := by
  rw [packetJointMerge_eq_stampSetPacket_packetListUnion_of_exact]
  · simp
  · intro y hy
    simp at hy
    simpa [hy] using hx

omit [Fintype Obj] [Fintype Attr] in
/-- Exact packet joint-merge depends only on the union of source stamps, not on
the particular list presentation used to produce that union. -/
theorem packetJointMerge_eq_of_packetListUnion_eq_of_exact
    (xs ys : List (StampedBinaryEvidence (WitnessStamp Obj Attr)))
    (hExactXs : ∀ x ∈ xs, ExactStampPacket x)
    (hExactYs : ∀ y ∈ ys, ExactStampPacket y)
    (hUnion : packetListUnion xs = packetListUnion ys) :
    packetJointMerge xs = packetJointMerge ys := by
  rw [packetJointMerge_eq_stampSetPacket_packetListUnion_of_exact xs hExactXs,
    packetJointMerge_eq_stampSetPacket_packetListUnion_of_exact ys hExactYs,
    hUnion]

omit [Fintype Obj] [Fintype Attr] in
/-- Duplicate exact source packets are absorbed inside larger joint merges.
This is the list-level form of the source-union idempotence law. -/
theorem packetJointMerge_cons_duplicate_absorb_of_exact
    (x : StampedBinaryEvidence (WitnessStamp Obj Attr))
    (xs : List (StampedBinaryEvidence (WitnessStamp Obj Attr)))
    (hExact : ∀ y ∈ x :: xs, ExactStampPacket y) :
    packetJointMerge (x :: x :: xs) = packetJointMerge (x :: xs) := by
  have hExactDup : ∀ y ∈ x :: x :: xs, ExactStampPacket y := by
    intro y hy
    rcases List.mem_cons.mp hy with hHead | hyTail
    · rw [hHead]
      exact hExact x (by simp)
    · rcases List.mem_cons.mp hyTail with hSecond | hyXs
      · rw [hSecond]
        exact hExact x (by simp)
      · exact hExact y (List.mem_cons.mpr (Or.inr hyXs))
  rw [packetJointMerge_eq_stampSetPacket_packetListUnion_of_exact _ hExactDup,
    packetJointMerge_eq_stampSetPacket_packetListUnion_of_exact _ hExact]
  simp [packetListUnion]

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

omit [Fintype Obj] [Fintype Attr] in
/-- Overlap correction conservatively extends guarded Revision: whenever the
guarded additive Revision succeeds, the overlap-corrected merge is exactly the
successful guarded result.  Thus guarded Revision is the disjoint special case
of the source-level overlap-aware merge, not a competing semantics. -/
theorem correctedMerge_eq_of_guardedRevise_eq_some
    (x y : StampedBinaryEvidence (WitnessStamp Obj Attr))
    {r : StampedBinaryEvidence (WitnessStamp Obj Attr)}
    (h : StampedBinaryEvidence.guardedRevise x y = some r) :
    correctedMerge x y = r := by
  by_cases hdisj : StampedBinaryEvidence.StampDisjoint x y
  · have hguard :
        StampedBinaryEvidence.guardedRevise x y =
          some (StampedBinaryEvidence.revise x y) :=
      StampedBinaryEvidence.guardedRevise_eq_some_of_stampDisjoint x y hdisj
    have hsome :
        some (StampedBinaryEvidence.revise x y) = some r := by
      rw [← hguard, h]
    have hr : StampedBinaryEvidence.revise x y = r :=
      Option.some.inj hsome
    rw [correctedMerge_eq_revise_of_stampDisjoint x y hdisj, hr]
  · have hnone :
        StampedBinaryEvidence.guardedRevise x y = none :=
      StampedBinaryEvidence.guardedRevise_eq_none_of_not_stampDisjoint x y hdisj
    rw [hnone] at h
    simp at h

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_posExtEmbedding_pos
    (S : Finset Obj) :
    (stampSetEvidence
      (S.map (posExtEmbedding (Obj := Obj) (Attr := Attr)))).pos =
        (S.card : ℝ≥0∞) := by
  rw [stampSetEvidence, sum_stampContribution_pos, Finset.sum_map]
  simp [stampContribution, posExtEmbedding]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_posExtEmbedding_neg
    (S : Finset Obj) :
    (stampSetEvidence
      (S.map (posExtEmbedding (Obj := Obj) (Attr := Attr)))).neg = 0 := by
  rw [stampSetEvidence, sum_stampContribution_neg, Finset.sum_map]
  simp [stampContribution, posExtEmbedding]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_negExtEmbedding_pos
    (S : Finset Obj) :
    (stampSetEvidence
      (S.map (negExtEmbedding (Obj := Obj) (Attr := Attr)))).pos = 0 := by
  rw [stampSetEvidence, sum_stampContribution_pos, Finset.sum_map]
  simp [stampContribution, negExtEmbedding]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_negExtEmbedding_neg
    (S : Finset Obj) :
    (stampSetEvidence
      (S.map (negExtEmbedding (Obj := Obj) (Attr := Attr)))).neg =
        (S.card : ℝ≥0∞) := by
  rw [stampSetEvidence, sum_stampContribution_neg, Finset.sum_map]
  simp [stampContribution, negExtEmbedding]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_posIntEmbedding_pos
    (S : Finset Attr) :
    (stampSetEvidence
      (S.map (posIntEmbedding (Obj := Obj) (Attr := Attr)))).pos =
        (S.card : ℝ≥0∞) := by
  rw [stampSetEvidence, sum_stampContribution_pos, Finset.sum_map]
  simp [stampContribution, posIntEmbedding]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_posIntEmbedding_neg
    (S : Finset Attr) :
    (stampSetEvidence
      (S.map (posIntEmbedding (Obj := Obj) (Attr := Attr)))).neg = 0 := by
  rw [stampSetEvidence, sum_stampContribution_neg, Finset.sum_map]
  simp [stampContribution, posIntEmbedding]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_negIntEmbedding_pos
    (S : Finset Attr) :
    (stampSetEvidence
      (S.map (negIntEmbedding (Obj := Obj) (Attr := Attr)))).pos = 0 := by
  rw [stampSetEvidence, sum_stampContribution_pos, Finset.sum_map]
  simp [stampContribution, negIntEmbedding]

omit [Fintype Obj] [Fintype Attr] in
@[simp] theorem stampSetEvidence_negIntEmbedding_neg
    (S : Finset Attr) :
    (stampSetEvidence
      (S.map (negIntEmbedding (Obj := Obj) (Attr := Attr)))).neg =
        (S.card : ℝ≥0∞) := by
  rw [stampSetEvidence, sum_stampContribution_neg, Finset.sum_map]
  simp [stampContribution, negIntEmbedding]

omit [Fintype Attr] in
theorem positiveExtensionalStampedEvidence_exact
    (A B : DualConcept Obj Attr) :
    ExactStampPacket (positiveExtensionalStampedEvidence A B) := by
  apply BinaryEvidence.ext' <;>
    simp [positiveExtensionalStampedEvidence]

omit [Fintype Attr] in
theorem negativeExtensionalStampedEvidence_exact
    (A B : DualConcept Obj Attr) :
    ExactStampPacket (negativeExtensionalStampedEvidence A B) := by
  apply BinaryEvidence.ext' <;>
    simp [negativeExtensionalStampedEvidence]

omit [Fintype Obj] in
theorem positiveIntensionalStampedEvidence_exact
    (A B : DualConcept Obj Attr) :
    ExactStampPacket (positiveIntensionalStampedEvidence A B) := by
  apply BinaryEvidence.ext' <;>
    simp [positiveIntensionalStampedEvidence]

omit [Fintype Obj] in
theorem negativeIntensionalStampedEvidence_exact
    (A B : DualConcept Obj Attr) :
    ExactStampPacket (negativeIntensionalStampedEvidence A B) := by
  apply BinaryEvidence.ext' <;>
    simp [negativeIntensionalStampedEvidence]

theorem positiveStampedEvidence_exact
    (A B : DualConcept Obj Attr) :
    ExactStampPacket (positiveStampedEvidence A B) := by
  have hpos :
      positiveExtensionalStampedEvidence A B =
        stampSetPacket (positiveExtensionalStampedEvidence A B).stamp :=
    eq_stampSetPacket_of_exact
      (positiveExtensionalStampedEvidence A B)
      (positiveExtensionalStampedEvidence_exact A B)
  have hint :
      positiveIntensionalStampedEvidence A B =
        stampSetPacket (positiveIntensionalStampedEvidence A B).stamp :=
    eq_stampSetPacket_of_exact
      (positiveIntensionalStampedEvidence A B)
      (positiveIntensionalStampedEvidence_exact A B)
  have hguard := positiveStampedEvidence_guardedRevise_eq_some A B
  rw [hpos, hint] at hguard
  have h :=
    correctedMerge_eq_of_guardedRevise_eq_some
      (stampSetPacket ((positiveExtensionalStampedEvidence A B).stamp))
      (stampSetPacket ((positiveIntensionalStampedEvidence A B).stamp))
      hguard
  rw [correctedMerge_stampSetPacket_eq_union] at h
  exact h.symm ▸ stampSetPacket_exact _

theorem negativeStampedEvidence_exact
    (A B : DualConcept Obj Attr) :
    ExactStampPacket (negativeStampedEvidence A B) := by
  have hext :
      negativeExtensionalStampedEvidence A B =
        stampSetPacket (negativeExtensionalStampedEvidence A B).stamp :=
    eq_stampSetPacket_of_exact
      (negativeExtensionalStampedEvidence A B)
      (negativeExtensionalStampedEvidence_exact A B)
  have hint :
      negativeIntensionalStampedEvidence A B =
        stampSetPacket (negativeIntensionalStampedEvidence A B).stamp :=
    eq_stampSetPacket_of_exact
      (negativeIntensionalStampedEvidence A B)
      (negativeIntensionalStampedEvidence_exact A B)
  have hguard := negativeStampedEvidence_guardedRevise_eq_some A B
  rw [hext, hint] at hguard
  have h :=
    correctedMerge_eq_of_guardedRevise_eq_some
      (stampSetPacket ((negativeExtensionalStampedEvidence A B).stamp))
      (stampSetPacket ((negativeIntensionalStampedEvidence A B).stamp))
      hguard
  rw [correctedMerge_stampSetPacket_eq_union] at h
  exact h.symm ▸ stampSetPacket_exact _

theorem finiteInheritanceStampedEvidence_exact
    (A B : DualConcept Obj Attr) :
    ExactStampPacket (finiteInheritanceStampedEvidence A B) := by
  have hpos :
      positiveStampedEvidence A B =
        stampSetPacket (positiveStampedEvidence A B).stamp :=
    eq_stampSetPacket_of_exact
      (positiveStampedEvidence A B)
      (positiveStampedEvidence_exact A B)
  have hneg :
      negativeStampedEvidence A B =
        stampSetPacket (negativeStampedEvidence A B).stamp :=
    eq_stampSetPacket_of_exact
      (negativeStampedEvidence A B)
      (negativeStampedEvidence_exact A B)
  have hguard := finiteInheritanceStampedEvidence_guardedRevise_eq_some A B
  rw [hpos, hneg] at hguard
  have h :=
    correctedMerge_eq_of_guardedRevise_eq_some
      (stampSetPacket ((positiveStampedEvidence A B).stamp))
      (stampSetPacket ((negativeStampedEvidence A B).stamp))
      hguard
  rw [correctedMerge_stampSetPacket_eq_union] at h
  exact h.symm ▸ stampSetPacket_exact _

omit [Fintype Obj] [Fintype Attr] in
theorem listRevise_eq_stampSetPacket_packetListUnion_of_pairwise_of_exact
    (xs : List (StampedBinaryEvidence (WitnessStamp Obj Attr)))
    (hExact : ∀ x ∈ xs, ExactStampPacket x)
    (hPair : xs.Pairwise StampedBinaryEvidence.StampDisjoint) :
    StampedBinaryEvidence.listRevise xs = stampSetPacket (packetListUnion xs) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hx : ExactStampPacket x := hExact x (by simp)
      have hHead :
          ∀ y ∈ xs, StampedBinaryEvidence.StampDisjoint x y :=
        (List.pairwise_cons.mp hPair).1
      have hTail :
          xs.Pairwise StampedBinaryEvidence.StampDisjoint :=
        (List.pairwise_cons.mp hPair).2
      have hExactTail : ∀ y ∈ xs, ExactStampPacket y := by
        intro y hy
        exact hExact y (by simp [hy])
      have hTailEq :
          StampedBinaryEvidence.listRevise xs = stampSetPacket (packetListUnion xs) :=
        ih hExactTail hTail
      have hDisjList :
          StampedBinaryEvidence.StampDisjoint
            x (StampedBinaryEvidence.listRevise xs) := by
        rw [StampedBinaryEvidence.stampDisjoint_listRevise_iff]
        exact hHead
      have hDisjUnion :
          StampedBinaryEvidence.StampDisjoint
            x (stampSetPacket (packetListUnion xs)) := by
        simpa [hTailEq] using hDisjList
      have hCorr :
          correctedMerge x (stampSetPacket (packetListUnion xs)) =
            StampedBinaryEvidence.revise x
              (stampSetPacket (packetListUnion xs)) :=
        correctedMerge_eq_revise_of_stampDisjoint
          x (stampSetPacket (packetListUnion xs)) hDisjUnion
      have hMerge :
          correctedMerge x (stampSetPacket (packetListUnion xs)) =
            stampSetPacket (x.stamp ∪ packetListUnion xs) :=
        correctedMerge_eq_stampSetPacket_union_of_exact
          x (stampSetPacket (packetListUnion xs)) hx (stampSetPacket_exact _)
      simp only [StampedBinaryEvidence.listRevise_cons, packetListUnion_cons]
      rw [hTailEq, ← hCorr, hMerge]

omit [Fintype Obj] [Fintype Attr] in
theorem listRevise_stampSetPacket_eq_union_of_pairwise
    (Ss : List (Finset (WitnessStamp Obj Attr)))
    (hPair :
      (Ss.map stampSetPacket).Pairwise StampedBinaryEvidence.StampDisjoint) :
    StampedBinaryEvidence.listRevise (Ss.map stampSetPacket) =
      stampSetPacket (stampSetListUnion Ss) := by
  induction Ss with
  | nil =>
      rfl
  | cons S Ss ih =>
      have hHead :
          ∀ y ∈ Ss.map stampSetPacket,
            StampedBinaryEvidence.StampDisjoint (stampSetPacket S) y :=
        (List.pairwise_cons.mp hPair).1
      have hTail :
          (Ss.map stampSetPacket).Pairwise
            StampedBinaryEvidence.StampDisjoint :=
        (List.pairwise_cons.mp hPair).2
      have hTailEq :
          StampedBinaryEvidence.listRevise (Ss.map stampSetPacket) =
            stampSetPacket (stampSetListUnion Ss) :=
        ih hTail
      have hDisjList :
          StampedBinaryEvidence.StampDisjoint
            (stampSetPacket S)
            (StampedBinaryEvidence.listRevise (Ss.map stampSetPacket)) := by
        rw [StampedBinaryEvidence.stampDisjoint_listRevise_iff]
        exact hHead
      have hDisjUnion :
          StampedBinaryEvidence.StampDisjoint
            (stampSetPacket S)
            (stampSetPacket (stampSetListUnion Ss)) := by
        simpa [hTailEq] using hDisjList
      have hCorr :
          correctedMerge (stampSetPacket S) (stampSetPacket (stampSetListUnion Ss)) =
            StampedBinaryEvidence.revise
              (stampSetPacket S) (stampSetPacket (stampSetListUnion Ss)) :=
        correctedMerge_eq_revise_of_stampDisjoint
          (stampSetPacket S) (stampSetPacket (stampSetListUnion Ss)) hDisjUnion
      simp only [List.map_cons, StampedBinaryEvidence.listRevise_cons,
        stampSetListUnion_cons]
      rw [hTailEq, ← hCorr, correctedMerge_stampSetPacket_eq_union]

omit [Fintype Obj] [Fintype Attr] in
/-- N-ary conservative-extension theorem for exact source packets: whenever
guarded list Revision succeeds, the overlap-corrected source-union merge is
exactly the same aggregate.  When guarded list Revision rejects, the
source-union merge remains the provenance-aware alternative rather than a
raw additive over-count. -/
theorem stampSetPacketJointMerge_eq_of_guardedListRevise_eq_some
    (Ss : List (Finset (WitnessStamp Obj Attr)))
    {r : StampedBinaryEvidence (WitnessStamp Obj Attr)}
    (h :
      StampedBinaryEvidence.guardedListRevise (Ss.map stampSetPacket) =
        some r) :
    stampSetPacketJointMerge Ss = r := by
  have hSome :
      (StampedBinaryEvidence.guardedListRevise (Ss.map stampSetPacket)).isSome := by
    rw [h]
    simp
  have hPair :
      (Ss.map stampSetPacket).Pairwise StampedBinaryEvidence.StampDisjoint :=
    (StampedBinaryEvidence.guardedListRevise_isSome_iff_pairwise
      (Ss.map stampSetPacket)).mp hSome
  have hList :
      StampedBinaryEvidence.listRevise (Ss.map stampSetPacket) =
        stampSetPacket (stampSetListUnion Ss) :=
    listRevise_stampSetPacket_eq_union_of_pairwise Ss hPair
  have hr :
      r = StampedBinaryEvidence.listRevise (Ss.map stampSetPacket) :=
    StampedBinaryEvidence.guardedListRevise_eq_some_imp_eq_listRevise
      (Ss.map stampSetPacket) h
  rw [stampSetPacketJointMerge_eq_union, ← hList, ← hr]

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
      Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.sub_def]

/-- Raw additive revision is deliberately exposed as over-counting at overlapping
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
    Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.sub_def] at hpos
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

end Mettapedia.KR.ConceptGeometry.AbstractInheritance
