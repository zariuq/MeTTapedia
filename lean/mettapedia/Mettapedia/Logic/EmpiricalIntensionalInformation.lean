import Mettapedia.Logic.IntensionalInheritance
import Mettapedia.Logic.AbstractInheritance
import Mettapedia.Logic.ConceptOntology.Basic
import Mettapedia.Logic.BinaryEvidence
import Mettapedia.InformationTheory.MutualInformation

/-!
# Empirical Intensional Information for Concept-Membership Events

This file gives a concrete finite model for Chapter-12-style reasoning over a
binary membership table:

- feature absent / present
- witness absent / present

It deliberately keeps two different objects side by side:

1. the **pointwise log-ratio score** for the update `P(W | F)` versus `P(W)`
2. the **Shannon mutual information** of the whole 2×2 joint table
-/

namespace Mettapedia.Logic.IntensionalInheritance

open Mettapedia.InformationTheory
open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.ConceptOntology

/-- The two concept positions in the empirical 2×2 table. -/
inductive MembershipConcept
  | feature
  | witness
  deriving DecidableEq, Fintype

/-- Counts for a binary feature/witness contingency table.

We use the convention:
- `neither`: neither `F` nor `W`
- `witnessOnly`: `W` but not `F`
- `featureOnly`: `F` but not `W`
- `both`: both `F` and `W`
-/
structure MembershipCounts where
  neither : ℕ
  witnessOnly : ℕ
  featureOnly : ℕ
  both : ℕ
  total_pos : 0 < neither + witnessOnly + featureOnly + both

namespace MembershipCounts

/-- A finite object domain whose cardinality is exactly the 2×2 table total,
presented as the four contingency-table regions. -/
abbrev EmpiricalObject (c : MembershipCounts) :=
  Sum (Fin c.neither) (Sum (Fin c.witnessOnly) (Sum (Fin c.featureOnly) (Fin c.both)))

/-- Crisp membership evidence contributed by a single empirical object. -/
def empiricalMembershipAtom
    (c : MembershipCounts)
    (x : EmpiricalObject c)
    (k : MembershipConcept) :
    BinaryEvidence :=
  match k, x with
  | .feature, Sum.inl _ => BinaryEvidence.zero
  | .feature, Sum.inr (Sum.inl _) => BinaryEvidence.zero
  | .feature, Sum.inr (Sum.inr (Sum.inl _)) => BinaryEvidence.one
  | .feature, Sum.inr (Sum.inr (Sum.inr _)) => BinaryEvidence.one
  | .witness, Sum.inl _ => BinaryEvidence.zero
  | .witness, Sum.inr (Sum.inl _) => BinaryEvidence.one
  | .witness, Sum.inr (Sum.inr (Sum.inl _)) => BinaryEvidence.zero
  | .witness, Sum.inr (Sum.inr (Sum.inr _)) => BinaryEvidence.one

/-- Empirical posterior states are multisets of empirical objects. -/
abbrev EmpiricalState (c : MembershipCounts) := Multiset (EmpiricalObject c)

/-- Membership evidence is the additive accumulation of single-object evidence
over an empirical multiset state. -/
noncomputable def empiricalMemberEvidence
    (c : MembershipCounts)
    (σ : EmpiricalState c)
    (x : EmpiricalObject c)
    (k : MembershipConcept) :
    BinaryEvidence :=
  σ.count x • empiricalMembershipAtom c x k

/-- The empirical 2×2 table as an evidence-membership context. -/
noncomputable def empiricalMembershipContext
    (c : MembershipCounts) :
    letI : EvidenceType (EmpiricalState c) :=
      PLNWorldModelAdditive.multisetEvidenceType (EmpiricalObject c)
    EvidenceMembershipContext
      (EmpiricalState c) (EmpiricalObject c) MembershipConcept BinaryEvidence := by
  letI : EvidenceType (EmpiricalState c) :=
    PLNWorldModelAdditive.multisetEvidenceType (EmpiricalObject c)
  exact
  { memberEvidence := empiricalMemberEvidence c
    memberEvidence_add := by
      intro σ₁ σ₂ x k
      show Multiset.count x (σ₁ + σ₂) • c.empiricalMembershipAtom x k
        = Multiset.count x σ₁ • c.empiricalMembershipAtom x k
          + Multiset.count x σ₂ • c.empiricalMembershipAtom x k
      rw [Multiset.count_add, add_nsmul] }

/-- The full finite observation state containing each empirical object exactly
once. -/
noncomputable def fullObservationState (c : MembershipCounts) : EmpiricalState c :=
  (Finset.univ : Finset (EmpiricalObject c)).1

/-- In the full empirical observation state, each object contributes exactly its
own single-object membership evidence. -/
theorem empiricalMemberEvidence_fullObservationState
    (c : MembershipCounts) (x : EmpiricalObject c) (k : MembershipConcept) :
    letI : EvidenceType (EmpiricalState c) :=
      PLNWorldModelAdditive.multisetEvidenceType (EmpiricalObject c)
    empiricalMemberEvidence c (fullObservationState c) x k =
      empiricalMembershipAtom c x k := by
  letI : EvidenceType (EmpiricalState c) :=
    PLNWorldModelAdditive.multisetEvidenceType (EmpiricalObject c)
  classical
  simp [empiricalMemberEvidence, fullObservationState]

/-- The crisp semantic interpretation induced by the empirical 2×2 table. -/
noncomputable def semanticInterpretation
    (c : MembershipCounts) :
    AbstractInheritance.Interpretation
      MembershipConcept (EmpiricalObject c) MembershipConcept :=
  AbstractInheritance.crispInterpretation
    EvidenceGate.positiveSupport
    (fun x k =>
      letI : EvidenceType (EmpiricalState c) :=
        PLNWorldModelAdditive.multisetEvidenceType (EmpiricalObject c)
      empiricalMemberEvidence c (fullObservationState c) x k)

theorem mem_semanticInterpretation_witness_extent_iff_pos
    (c : MembershipCounts) (x : EmpiricalObject c) :
    x ∈ ((semanticInterpretation c).meaning MembershipConcept.witness).extent ↔
      0 < (empiricalMembershipAtom c x MembershipConcept.witness).pos := by
  simp [semanticInterpretation,
    Mettapedia.Logic.AbstractInheritance.crispInterpretation,
    Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept,
    Mettapedia.Logic.AbstractInheritance.crispBaseConcept,
    empiricalMemberEvidence_fullObservationState]

theorem mem_semanticInterpretation_feature_extent_iff_pos
    (c : MembershipCounts) (x : EmpiricalObject c) :
    x ∈ ((semanticInterpretation c).meaning MembershipConcept.feature).extent ↔
      0 < (empiricalMembershipAtom c x MembershipConcept.feature).pos := by
  simp [semanticInterpretation,
    Mettapedia.Logic.AbstractInheritance.crispInterpretation,
    Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept,
    Mettapedia.Logic.AbstractInheritance.crispBaseConcept,
    empiricalMemberEvidence_fullObservationState]

noncomputable def witnessExtentEquiv
    (c : MembershipCounts) :
    {x : EmpiricalObject c //
        x ∈ ((semanticInterpretation c).meaning MembershipConcept.witness).extent} ≃
      Fin c.witnessOnly ⊕ Fin c.both where
  toFun x :=
    match x with
    | ⟨Sum.inl n, hx⟩ =>
        False.elim (by
          simp [mem_semanticInterpretation_witness_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | ⟨Sum.inr (Sum.inl w), _⟩ => Sum.inl w
    | ⟨Sum.inr (Sum.inr (Sum.inl f)), hx⟩ =>
        False.elim (by
          simp [mem_semanticInterpretation_witness_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | ⟨Sum.inr (Sum.inr (Sum.inr b)), _⟩ => Sum.inr b
  invFun y :=
    match y with
    | Sum.inl w =>
        ⟨Sum.inr (Sum.inl w), by
          simp [mem_semanticInterpretation_witness_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.one]⟩
    | Sum.inr b =>
        ⟨Sum.inr (Sum.inr (Sum.inr b)), by
          simp [mem_semanticInterpretation_witness_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.one]⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl n =>
        exact False.elim (by
          simp [mem_semanticInterpretation_witness_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | inr rest =>
        cases rest with
        | inl w => rfl
        | inr rest =>
            cases rest with
            | inl f =>
                exact False.elim (by
                  simp [mem_semanticInterpretation_witness_extent_iff_pos,
                    empiricalMembershipAtom, BinaryEvidence.zero] at hx)
            | inr b => rfl
  right_inv y := by
    cases y <;> rfl

noncomputable def featureExtentEquiv
    (c : MembershipCounts) :
    {x : EmpiricalObject c //
        x ∈ ((semanticInterpretation c).meaning MembershipConcept.feature).extent} ≃
      Fin c.featureOnly ⊕ Fin c.both where
  toFun x :=
    match x with
    | ⟨Sum.inl n, hx⟩ =>
        False.elim (by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | ⟨Sum.inr (Sum.inl w), hx⟩ =>
        False.elim (by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | ⟨Sum.inr (Sum.inr (Sum.inl f)), _⟩ => Sum.inl f
    | ⟨Sum.inr (Sum.inr (Sum.inr b)), _⟩ => Sum.inr b
  invFun y :=
    match y with
    | Sum.inl f =>
        ⟨Sum.inr (Sum.inr (Sum.inl f)), by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.one]⟩
    | Sum.inr b =>
        ⟨Sum.inr (Sum.inr (Sum.inr b)), by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.one]⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl n =>
        exact False.elim (by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | inr rest =>
        cases rest with
        | inl w =>
            exact False.elim (by
              simp [mem_semanticInterpretation_feature_extent_iff_pos,
                empiricalMembershipAtom, BinaryEvidence.zero] at hx)
        | inr rest =>
            cases rest with
            | inl f => rfl
            | inr b => rfl
  right_inv y := by
    cases y <;> rfl

noncomputable def jointFeatureWitnessExtentEquiv
    (c : MembershipCounts) :
    {x : EmpiricalObject c //
        x ∈ ((semanticInterpretation c).meaning MembershipConcept.feature).extent ∧
        x ∈ ((semanticInterpretation c).meaning MembershipConcept.witness).extent} ≃
      Fin c.both where
  toFun x :=
    match x with
    | ⟨Sum.inl n, hx⟩ =>
        False.elim (by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | ⟨Sum.inr (Sum.inl w), hx⟩ =>
        False.elim (by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | ⟨Sum.inr (Sum.inr (Sum.inl f)), hx⟩ =>
        False.elim (by
          simp [mem_semanticInterpretation_witness_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | ⟨Sum.inr (Sum.inr (Sum.inr b)), _⟩ => b
  invFun b :=
    ⟨Sum.inr (Sum.inr (Sum.inr b)), by
      constructor
      · simp [mem_semanticInterpretation_feature_extent_iff_pos,
          empiricalMembershipAtom, BinaryEvidence.one]
      · simp [mem_semanticInterpretation_witness_extent_iff_pos,
          empiricalMembershipAtom, BinaryEvidence.one]⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl n =>
        exact False.elim (by
          simp [mem_semanticInterpretation_feature_extent_iff_pos,
            empiricalMembershipAtom, BinaryEvidence.zero] at hx)
    | inr rest =>
        cases rest with
        | inl w =>
            exact False.elim (by
              simp [mem_semanticInterpretation_feature_extent_iff_pos,
                empiricalMembershipAtom, BinaryEvidence.zero] at hx)
        | inr rest =>
            cases rest with
            | inl f =>
                exact False.elim (by
                  simp [mem_semanticInterpretation_witness_extent_iff_pos,
                    empiricalMembershipAtom, BinaryEvidence.zero] at hx)
            | inr b => rfl
  right_inv b := by
    rfl

@[simp] theorem empiricalMemberEvidence_feature_featureOnly
    (c : MembershipCounts) (x : Fin c.featureOnly) :
    empiricalMembershipAtom c
        (Sum.inr (Sum.inr (Sum.inl x))) .feature =
      BinaryEvidence.one := rfl

@[simp] theorem empiricalMemberEvidence_witness_witnessOnly
    (c : MembershipCounts) (x : Fin c.witnessOnly) :
    empiricalMembershipAtom c
        (Sum.inr (Sum.inl x)) .witness =
      BinaryEvidence.one := rfl

/-- Total number of observations. -/
def total (c : MembershipCounts) : ℕ :=
  c.neither + c.witnessOnly + c.featureOnly + c.both

/-- Number of observations where the witness concept holds. -/
def witnessSupport (c : MembershipCounts) : ℕ :=
  c.witnessOnly + c.both

/-- Number of observations where the feature concept holds. -/
def featureSupport (c : MembershipCounts) : ℕ :=
  c.featureOnly + c.both

/-- Prior probability `P(W)`. -/
noncomputable def priorProbWitness (c : MembershipCounts) : ℝ :=
  (c.witnessSupport : ℝ) / c.total

/-- Prior probability `P(F)`. -/
noncomputable def priorProbFeature (c : MembershipCounts) : ℝ :=
  (c.featureSupport : ℝ) / c.total

/-- Extensional inheritance `P(W | F)` extracted from the 2×2 table. -/
noncomputable def extensionalInheritance (c : MembershipCounts) : ℝ :=
  if c.featureSupport = 0 then
    0
  else
    (c.both : ℝ) / c.featureSupport

/-- Chapter-12 pointwise intensional score in bits, read from the empirical table. -/
noncomputable def pointwiseIntensionalScoreBits (c : MembershipCounts) : ℝ :=
  logRatioInformationGainFromEvidence (extensionalInheritance c) (priorProbWitness c)

theorem empiricalObject_card (c : MembershipCounts) :
    Fintype.card (EmpiricalObject c) = total c := by
  simp [EmpiricalObject, total, Fintype.card_sum, add_assoc]

theorem semanticInterpretation_extentCount_witness
    (c : MembershipCounts) :
    Interpretation.extentCount (semanticInterpretation c) MembershipConcept.witness =
      witnessSupport c := by
  classical
  unfold Interpretation.extentCount witnessSupport
  rw [Fintype.card_congr (witnessExtentEquiv c)]
  simp [Fintype.card_sum]

theorem semanticInterpretation_extentCount_feature
    (c : MembershipCounts) :
    Interpretation.extentCount (semanticInterpretation c) MembershipConcept.feature =
      featureSupport c := by
  classical
  unfold Interpretation.extentCount featureSupport
  rw [Fintype.card_congr (featureExtentEquiv c)]
  simp [Fintype.card_sum]

theorem semanticInterpretation_jointExtentCount_feature_witness
    (c : MembershipCounts) :
    Interpretation.jointExtentCount
        (semanticInterpretation c)
        MembershipConcept.feature
        MembershipConcept.witness =
      c.both := by
  classical
  unfold Interpretation.jointExtentCount
  rw [Fintype.card_congr (jointFeatureWitnessExtentEquiv c)]
  simp

theorem finitePriorProb_semanticInterpretation_witness
    (c : MembershipCounts) :
    Interpretation.finitePriorProb
        (semanticInterpretation c)
        MembershipConcept.witness =
      priorProbWitness c := by
  unfold priorProbWitness
  rw [Interpretation.finitePriorProb, semanticInterpretation_extentCount_witness, empiricalObject_card]

theorem finiteExtensionalProb_semanticInterpretation_feature_witness
    (c : MembershipCounts) :
    Interpretation.finiteExtensionalProb
        (semanticInterpretation c)
        MembershipConcept.feature
        MembershipConcept.witness =
      extensionalInheritance c := by
  simp [Interpretation.finiteExtensionalProb, extensionalInheritance,
    semanticInterpretation_extentCount_feature,
    semanticInterpretation_jointExtentCount_feature_witness]

theorem finitePointwiseLogRatioBits_semanticInterpretation_feature_witness
    (c : MembershipCounts) :
    Interpretation.finitePointwiseLogRatioBits
        (semanticInterpretation c)
        MembershipConcept.feature
        MembershipConcept.witness =
      pointwiseIntensionalScoreBits c := by
  simp [Interpretation.finitePointwiseLogRatioBits, pointwiseIntensionalScoreBits,
    finitePriorProb_semanticInterpretation_witness,
    finiteExtensionalProb_semanticInterpretation_feature_witness]

/-- Fin-2 encoding of the empirical joint distribution.

Index convention:
- `0` = false / absent
- `1` = true / present
-/
noncomputable def jointMembershipDist (c : MembershipCounts) : JointProb 2 2 :=
  ⟨fun ij =>
      match ij with
      | (0, 0) => (c.neither : ℝ) / c.total
      | (0, 1) => (c.witnessOnly : ℝ) / c.total
      | (1, 0) => (c.featureOnly : ℝ) / c.total
      | (1, 1) => (c.both : ℝ) / c.total,
    by
      constructor
      · intro ij
        rcases ij with ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> positivity
      ·
        have hTotalNe : (c.total : ℝ) ≠ 0 := by
          exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt c.total_pos)
        have hTotalCast :
            (c.total : ℝ) = (c.neither : ℝ) + c.witnessOnly + c.featureOnly + c.both := by
          norm_num [MembershipCounts.total]
        simp [MembershipCounts.total, Fintype.sum_prod_type]
        calc
          (c.neither : ℝ) / (c.neither + c.witnessOnly + c.featureOnly + c.both) +
                c.witnessOnly / (c.neither + c.witnessOnly + c.featureOnly + c.both) +
              (c.featureOnly / (c.neither + c.witnessOnly + c.featureOnly + c.both) +
                c.both / (c.neither + c.witnessOnly + c.featureOnly + c.both))
              = ((c.neither : ℝ) + c.witnessOnly + c.featureOnly + c.both) /
                  ((c.neither : ℝ) + c.witnessOnly + c.featureOnly + c.both) := by
                  ring_nf
          _ = (c.total : ℝ) / c.total := by simp [hTotalCast]
          _ = 1 := by field_simp [hTotalNe]⟩

/-- The witness prior read from the empirical joint distribution. -/
theorem marginalRight_true_eq_priorProbWitness (c : MembershipCounts) :
    (JointProb.marginalRight (jointMembershipDist c)).1 1 = priorProbWitness c := by
  have hTotalNe : (c.total : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt c.total_pos)
  simp [JointProb.marginalRight, jointMembershipDist, priorProbWitness, witnessSupport]
  field_simp [MembershipCounts.total, hTotalNe]

/-- The feature prior read from the empirical joint distribution. -/
theorem marginalLeft_true_eq_priorProbFeature (c : MembershipCounts) :
    (JointProb.marginalLeft (jointMembershipDist c)).1 1 = priorProbFeature c := by
  have hTotalNe : (c.total : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt c.total_pos)
  simp [JointProb.marginalLeft, jointMembershipDist, priorProbFeature, featureSupport]
  field_simp [MembershipCounts.total, hTotalNe]

/-- Shannon mutual information of the empirical 2×2 table, in nats. -/
noncomputable def shannonMutualInformationNats (c : MembershipCounts) : ℝ :=
  JointProb.shannonMutualInformationNats (jointMembershipDist c)

/-- Shannon mutual information of the empirical 2×2 table, in bits. -/
noncomputable def shannonMutualInformationBits (c : MembershipCounts) : ℝ :=
  JointProb.shannonMutualInformationBits (jointMembershipDist c)

/-- Expected log-ratio information gain of the empirical 2×2 table, in bits. -/
noncomputable def expectedLogRatioToProductBits (c : MembershipCounts) : ℝ :=
  JointProb.expectedLogRatioToProductBits (jointMembershipDist c)

theorem shannonMutualInformationBits_eq_expectedLogRatioToProductBits
    (c : MembershipCounts) :
    shannonMutualInformationBits c = expectedLogRatioToProductBits c := by
  unfold shannonMutualInformationBits expectedLogRatioToProductBits
  exact JointProb.shannonMutualInformationBits_eq_expectedLogRatioToProductBits _

theorem extensionalInheritance_eq_prior_mul_two_rpow_pointwiseIntensionalScoreBits
    (c : MembershipCounts)
    (hExt : 0 < extensionalInheritance c)
    (hPrior : 0 < priorProbWitness c) :
    extensionalInheritance c =
      priorProbWitness c * (2 : ℝ).rpow (pointwiseIntensionalScoreBits c) := by
  have hExt' :
      0 <
        Interpretation.finiteExtensionalProb
          (semanticInterpretation c)
          MembershipConcept.feature
          MembershipConcept.witness := by
    simpa [finiteExtensionalProb_semanticInterpretation_feature_witness] using hExt
  have hPrior' :
      0 <
        Interpretation.finitePriorProb
          (semanticInterpretation c)
          MembershipConcept.witness := by
    simpa [finitePriorProb_semanticInterpretation_witness] using hPrior
  simpa [finitePriorProb_semanticInterpretation_witness,
    finiteExtensionalProb_semanticInterpretation_feature_witness,
    finitePointwiseLogRatioBits_semanticInterpretation_feature_witness] using
      (Interpretation.finite_goertzel_formula
        (I := semanticInterpretation c)
        (f := MembershipConcept.feature)
        (w := MembershipConcept.witness)
        hExt' hPrior')

/-- Concrete Chapter-12 formula for the empirical 2×2 membership table. -/
theorem empirical_goertzel_formula
    (c : MembershipCounts)
    (hExt : 0 < extensionalInheritance c)
    (hPrior : 0 < priorProbWitness c) :
    extensionalInheritance c =
      priorProbWitness c * (2 : ℝ).rpow (pointwiseIntensionalScoreBits c) :=
  extensionalInheritance_eq_prior_mul_two_rpow_pointwiseIntensionalScoreBits c hExt hPrior

/-- Rearranged empirical reduction theorem for the pointwise Chapter-12 score. -/
theorem empirical_pointwise_logRatio_reduction
    (c : MembershipCounts)
    (hExt : 0 < extensionalInheritance c)
    (hPrior : 0 < priorProbWitness c) :
    (2 : ℝ).rpow (pointwiseIntensionalScoreBits c) =
      extensionalInheritance c / priorProbWitness c := by
  have hExt' :
      0 <
        Interpretation.finiteExtensionalProb
          (semanticInterpretation c)
          MembershipConcept.feature
          MembershipConcept.witness := by
    simpa [finiteExtensionalProb_semanticInterpretation_feature_witness] using hExt
  have hPrior' :
      0 <
        Interpretation.finitePriorProb
          (semanticInterpretation c)
          MembershipConcept.witness := by
    simpa [finitePriorProb_semanticInterpretation_witness] using hPrior
  simpa [finitePriorProb_semanticInterpretation_witness,
    finiteExtensionalProb_semanticInterpretation_feature_witness,
    finitePointwiseLogRatioBits_semanticInterpretation_feature_witness] using
      (Interpretation.finite_pointwise_logRatio_reduction
        (I := semanticInterpretation c)
        (f := MembershipConcept.feature)
        (w := MembershipConcept.witness)
        hExt' hPrior')

/-! ## Positive and negative examples -/

def positiveExample : MembershipCounts where
  neither := 2
  witnessOnly := 1
  featureOnly := 1
  both := 6
  total_pos := by decide

def independenceExample : MembershipCounts where
  neither := 1
  witnessOnly := 1
  featureOnly := 1
  both := 1
  total_pos := by decide

def antiCorrelationExample : MembershipCounts where
  neither := 1
  witnessOnly := 4
  featureOnly := 4
  both := 1
  total_pos := by decide

def zeroFeatureSupportExample : MembershipCounts where
  neither := 3
  witnessOnly := 2
  featureOnly := 0
  both := 0
  total_pos := by decide

example : priorProbWitness positiveExample = (7 : ℝ) / 10 := by
  norm_num [priorProbWitness, witnessSupport, total, positiveExample]

example : 0 < extensionalInheritance positiveExample := by
  norm_num [extensionalInheritance, featureSupport, positiveExample]

example : extensionalInheritance independenceExample = priorProbWitness independenceExample := by
  norm_num [extensionalInheritance, priorProbWitness, featureSupport, witnessSupport, total,
    independenceExample]

example : pointwiseIntensionalScoreBits independenceExample = 0 := by
  unfold pointwiseIntensionalScoreBits logRatioInformationGainFromEvidence
    Mettapedia.InformationTheory.logRatioInformationGainBits
    Mettapedia.InformationTheory.logBase2
  norm_num [extensionalInheritance, priorProbWitness, featureSupport, witnessSupport, total,
    independenceExample, Real.log_one]

example : extensionalInheritance antiCorrelationExample < priorProbWitness antiCorrelationExample := by
  norm_num [extensionalInheritance, priorProbWitness, featureSupport, witnessSupport, total,
    antiCorrelationExample]

example : extensionalInheritance zeroFeatureSupportExample = 0 := by
  simp [extensionalInheritance, featureSupport, zeroFeatureSupportExample]

example : pointwiseIntensionalScoreBits zeroFeatureSupportExample = 0 := by
  unfold pointwiseIntensionalScoreBits logRatioInformationGainFromEvidence
    Mettapedia.InformationTheory.logRatioInformationGainBits
  simp [extensionalInheritance, featureSupport,
    zeroFeatureSupportExample]

end MembershipCounts

end Mettapedia.Logic.IntensionalInheritance
