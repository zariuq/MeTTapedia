import Mettapedia.Logic.EmpiricalIntensionalFactorGraphBridge
import Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge

/-!
# Empirical Chapter-12 ASSOC/PAT Source for HO Predicate Vocabulary

This module instantiates the calibrated-intent seam from
`PLNHigherOrderHOLAssocPatBridge` on the empirical 2x2 Chapter-12 membership
table semantics. It does not identify empirical concepts with HOL predicates.
Instead, it records the exact calibration obligation needed to transport an
empirical pair-subset fact into the finite HO predicate-vocabulary ASSOC/PAT
target.
-/

namespace Mettapedia.Logic.PLNHigherOrderHOLEmpiricalAssocPatBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.IntensionalInheritance
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Empirical Chapter-12 pair-subset facts feed the finite HO predicate-pair
ASSOC/PAT target once decoded HO intent is calibrated to the empirical
`semanticInterpretation` intent.

This is the first semantic-source instantiation of the calibrated seam: the
source interpretation is the concrete 2x2 empirical membership-table
interpretation, while the target remains the existing finite-vocabulary HO
predicate interpretation. -/
theorem predicateVocabularyIntensionalPairSubsetRel_of_empiricalPairSubsetRel_viaIntentCalibration
    (counts : MembershipCounts)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : MembershipConcept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈ ((MembershipCounts.semanticInterpretation counts).meaning p).intent)
    {a b c d : MembershipConcept}
    {AssocState : Type} (W : AssocState)
    (hRel : (MembershipCounts.semanticInterpretation counts).PairSubsetRel a b c d) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentCalibration
      (I := MembershipCounts.semanticInterpretation counts)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal W hRel

/-- Finite witness/feature factor-graph tables feed the finite HO predicate-pair
ASSOC/PAT target through the same calibrated-intent seam.

The source interpretation is the `MembershipCounts` interpretation induced by
`FiniteWitnessFeatureTable.toMembershipCounts`; the factor-graph bridge proves
that this table also has exact VE/BP readouts for the same empirical quantities. -/
theorem predicateVocabularyIntensionalPairSubsetRel_of_finiteWitnessFeatureTablePairSubsetRel_viaIntentCalibration
    (table : FiniteWitnessFeatureTable)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : MembershipConcept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts table)).meaning p).intent)
    {a b c d : MembershipConcept}
    {AssocState : Type} (W : AssocState)
    (hRel :
      (MembershipCounts.semanticInterpretation
        (FiniteWitnessFeatureTable.toMembershipCounts table)).PairSubsetRel a b c d) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact
    predicateVocabularyIntensionalPairSubsetRel_of_empiricalPairSubsetRel_viaIntentCalibration
      (counts := FiniteWitnessFeatureTable.toMembershipCounts table)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal W hRel

/-- Formed Chapter-12 concepts feed the finite HO predicate-pair ASSOC/PAT
target through the same calibrated-intent seam.

This is the concept-formation source of the bridge: the source relation is the
formed-concept interpretation already provided by `AbstractInheritance`, while
the target remains the finite HO predicate-vocabulary interpretation. -/
theorem predicateVocabularyIntensionalPairSubsetRel_of_formedConceptPairSubsetRel_viaIntentCalibration
    {Obj Attr Q : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (Memb : Obj → Attr → Q)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Mettapedia.Logic.AbstractInheritance.FormedConcept G Memb → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hCal : ∀ {p : Mettapedia.Logic.AbstractInheritance.FormedConcept G Memb} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G Memb).meaning p).intent)
    {a b c d : Mettapedia.Logic.AbstractInheritance.FormedConcept G Memb}
    {AssocState : Type} (W : AssocState)
    (hRel :
      (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G Memb).PairSubsetRel
        a b c d) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentCalibration
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G Memb)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal W hRel

/-- Formed Chapter-12 concept mutual inheritance feeds the finite HO
predicate-vocabulary same-intent/similarity target under calibrated intent.

This is the predicate-level similarity companion to the pair-subset transport
above: same-intent remains mutual intensional inheritance in the existing HO
vocabulary, not a new similarity semantics. -/
theorem predicateVocabularySameIntent_of_formedConceptMutualInherits_viaIntentCalibration
    {Obj Attr Q : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (Memb : Obj → Attr → Q)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Mettapedia.Logic.AbstractInheritance.FormedConcept G Memb → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hCal : ∀ {p : Mettapedia.Logic.AbstractInheritance.FormedConcept G Memb} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G Memb).meaning p).intent)
    {p q : Mettapedia.Logic.AbstractInheritance.FormedConcept G Memb}
    (hMutual :
      (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G Memb).MutualInherits
        p q) :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode (code p) (code q) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularySameIntent_of_interpretationMutualInherits_viaIntentCalibration
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G Memb)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal hMutual

/-- Generic finite feature/witness count-table criterion behind the tiny
factor-graph canary.

If all support for a witness state is concentrated in one feature state, then
the VE query for the witness marginal equals the VE query for that
feature-and-witness joint event. This is a factor-graph/count-table fact, not
a new HO semantics. -/
theorem finiteFeatureWitnessCountTable_veWeight_witness_eq_feature_witness_of_support_eq_joint
    {Feature Witness : Type} [Fintype Feature] [Fintype Witness]
    (table : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness)
    (hSupport :
      FiniteFeatureWitnessCountTable.witnessSupport table witness =
        table.count feature witness) :
    FiniteFeatureWitnessCountTable.veWeight table
        [⟨MembershipConcept.witness, witness⟩] =
      FiniteFeatureWitnessCountTable.veWeight table
        [⟨MembershipConcept.feature, feature⟩,
          ⟨MembershipConcept.witness, witness⟩] := by
  rw [FiniteFeatureWitnessCountTable.veWeight_witness,
    FiniteFeatureWitnessCountTable.veWeight_feature_witness]
  exact hSupport

/-- A generic finite feature/witness table whose `true` witness is supported
only at the `true` feature state. -/
noncomputable def genericWitnessImpliesFeatureCountTable :
    FiniteFeatureWitnessCountTable Bool Bool where
  count := fun feature witness =>
    match feature, witness with
    | false, false => 1
    | false, true => 0
    | true, false => 1
    | true, true => 1
  total_pos := by
    decide

/-- The generic count-table canary has all true-witness support at the
true-feature state. -/
theorem genericWitnessImpliesFeatureCountTable_trueWitness_support_eq_joint :
    FiniteFeatureWitnessCountTable.witnessSupport
        genericWitnessImpliesFeatureCountTable true =
      genericWitnessImpliesFeatureCountTable.count true true := by
  simp [genericWitnessImpliesFeatureCountTable,
    FiniteFeatureWitnessCountTable.witnessSupport]

/-- The generic finite feature/witness count-table VE canary: true-witness
marginal equals the true-feature/true-witness joint query. -/
theorem genericWitnessImpliesFeatureCountTable_veWeight_trueWitness_eq_trueFeature_trueWitness :
    FiniteFeatureWitnessCountTable.veWeight genericWitnessImpliesFeatureCountTable
        [⟨MembershipConcept.witness, true⟩] =
      FiniteFeatureWitnessCountTable.veWeight genericWitnessImpliesFeatureCountTable
        [⟨MembershipConcept.feature, true⟩,
          ⟨MembershipConcept.witness, true⟩] := by
  exact
    finiteFeatureWitnessCountTable_veWeight_witness_eq_feature_witness_of_support_eq_joint
      genericWitnessImpliesFeatureCountTable true true
      genericWitnessImpliesFeatureCountTable_trueWitness_support_eq_joint

/-- Finite witness/feature table criterion specialized to the Chapter-12
2x2 empirical bridge.

If there are no witness-only cases, the witness marginal is exactly the
feature-and-witness joint mass. This is the table-level source fact behind the
formed-concept and empirical subset canaries; it is not a separate HO
semantics. -/
theorem finiteWitnessFeatureTable_veWeight_witness_eq_feature_witness_of_no_witnessOnly
    (table : FiniteWitnessFeatureTable)
    (hNoWitnessOnly : table.witnessOnly = 0) :
    FiniteWitnessFeatureTable.veWeight table
        [⟨MembershipConcept.witness, true⟩] =
      FiniteWitnessFeatureTable.veWeight table
        [⟨MembershipConcept.feature, true⟩,
          ⟨MembershipConcept.witness, true⟩] := by
  have hWitness :
      FiniteWitnessFeatureTable.veWeight table
          [⟨MembershipConcept.witness, true⟩] =
        (FiniteWitnessFeatureTable.toMembershipCounts table).witnessSupport := by
    simpa [FiniteWitnessFeatureTable.veWeight] using
      MembershipCounts.veWeight_witness_true
        (FiniteWitnessFeatureTable.toMembershipCounts table)
  have hJoint :
      FiniteWitnessFeatureTable.veWeight table
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] =
        (FiniteWitnessFeatureTable.toMembershipCounts table).both := by
    simpa [FiniteWitnessFeatureTable.veWeight] using
      MembershipCounts.veWeight_feature_witness_true
        (FiniteWitnessFeatureTable.toMembershipCounts table)
  rw [hWitness, hJoint]
  simp [FiniteWitnessFeatureTable.toMembershipCounts, MembershipCounts.witnessSupport,
    hNoWitnessOnly]

/-- The formed-concept inheritance table inherits the same no-witness-only VE
criterion. This packages the source-side condition in the vocabulary used by
Chapter-12 concept formation. -/
theorem formedConceptInheritanceTable_veWeight_witness_eq_feature_witness_of_no_witnessOnly
    {Obj Attr Q : Type*} [Preorder Q] [Fintype Obj] [Nonempty Obj] [Fintype Attr]
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (Memb : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G Memb)
    (hNoWitnessOnly :
      (Mettapedia.Logic.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
        G Memb feature witness).witnessOnly = 0) :
    FiniteWitnessFeatureTable.veWeight
        (Mettapedia.Logic.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
          G Memb feature witness)
        [⟨MembershipConcept.witness, true⟩] =
      FiniteWitnessFeatureTable.veWeight
        (Mettapedia.Logic.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
          G Memb feature witness)
        [⟨MembershipConcept.feature, true⟩,
          ⟨MembershipConcept.witness, true⟩] := by
  exact
    finiteWitnessFeatureTable_veWeight_witness_eq_feature_witness_of_no_witnessOnly
      (Mettapedia.Logic.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
        G Memb feature witness)
      hNoWitnessOnly

/-- Tiny nontrivial empirical table: there are no witness-only cases, so every
witness is also a feature. -/
def witnessImpliesFeatureCounts : MembershipCounts where
  neither := 1
  witnessOnly := 0
  featureOnly := 1
  both := 1
  total_pos := by decide

/-- The same canary as a reusable finite witness/feature factor-graph table. -/
def witnessImpliesFeatureTable : FiniteWitnessFeatureTable where
  neither := 1
  witnessOnly := 0
  featureOnly := 1
  both := 1
  total_pos := by decide

/-- Tiny empirical table where witness and feature have exactly the same
positive extent. This supplies a nontrivial formed-concept same-intent canary. -/
def witnessEquivalentFeatureCounts : MembershipCounts where
  neither := 1
  witnessOnly := 0
  featureOnly := 0
  both := 1
  total_pos := by decide

/-- The evidence-valued membership relation behind the tiny empirical canary,
factored out so the same source can be viewed as formed concepts. -/
noncomputable def witnessImpliesFeatureMemberEvidence
    (x : MembershipCounts.EmpiricalObject witnessImpliesFeatureCounts)
    (k : MembershipConcept) :
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence :=
  letI : Mettapedia.Logic.EvidenceClass.EvidenceType
      (MembershipCounts.EmpiricalState witnessImpliesFeatureCounts) :=
    Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType
      (MembershipCounts.EmpiricalObject witnessImpliesFeatureCounts)
  MembershipCounts.empiricalMemberEvidence witnessImpliesFeatureCounts
    (MembershipCounts.fullObservationState witnessImpliesFeatureCounts) x k

/-- The evidence-valued membership relation behind the equivalence canary,
where witness and feature have the same positive extent. -/
noncomputable def witnessEquivalentFeatureMemberEvidence
    (x : MembershipCounts.EmpiricalObject witnessEquivalentFeatureCounts)
    (k : MembershipConcept) :
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence :=
  letI : Mettapedia.Logic.EvidenceClass.EvidenceType
      (MembershipCounts.EmpiricalState witnessEquivalentFeatureCounts) :=
    Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType
      (MembershipCounts.EmpiricalObject witnessEquivalentFeatureCounts)
  MembershipCounts.empiricalMemberEvidence witnessEquivalentFeatureCounts
    (MembershipCounts.fullObservationState witnessEquivalentFeatureCounts) x k

/-- Base attributes in the tiny empirical canary, closed into the finite formed
concept family. This is the smallest actual formed-concept source used by the
HO ASSOC/PAT bridge. -/
noncomputable def witnessImpliesFeatureFormedConcept
    (k : MembershipConcept) :
    Mettapedia.Logic.AbstractInheritance.FormedConcept
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence :=
  ⟨Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence k,
    Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept_mem_finiteConceptFamily
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence k⟩

/-- Base attributes in the equivalence canary, closed into the finite formed
concept family. -/
noncomputable def witnessEquivalentFeatureFormedConcept
    (k : MembershipConcept) :
    Mettapedia.Logic.AbstractInheritance.FormedConcept
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence :=
  ⟨Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence k,
    Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept_mem_finiteConceptFamily
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence k⟩

/-- In the tiny empirical canary table, `witness` inherits from `feature`
because the witness extent is contained in the feature extent. -/
theorem witness_inherits_feature_canary :
    (MembershipCounts.semanticInterpretation witnessImpliesFeatureCounts).Inherits
      MembershipConcept.witness MembershipConcept.feature := by
  change
    (Mettapedia.Logic.AbstractInheritance.crispInterpretation
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        (fun x k =>
          letI : Mettapedia.Logic.EvidenceClass.EvidenceType
              (MembershipCounts.EmpiricalState witnessImpliesFeatureCounts) :=
            Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType
              (MembershipCounts.EmpiricalObject witnessImpliesFeatureCounts)
          MembershipCounts.empiricalMemberEvidence witnessImpliesFeatureCounts
            (MembershipCounts.fullObservationState witnessImpliesFeatureCounts) x k)).Inherits
      MembershipConcept.witness MembershipConcept.feature
  rw [Mettapedia.Logic.AbstractInheritance.crispInterpretation_inherits_iff,
    Mettapedia.Logic.ConceptOntology.crispExtensionalInherits_iff]
  intro x hx
  cases x with
  | inl n =>
      simp [MembershipCounts.empiricalMemberEvidence_fullObservationState,
        MembershipCounts.empiricalMembershipAtom,
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero,
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport] at hx
  | inr rest =>
      cases rest with
      | inl w =>
          exact Fin.elim0 w
      | inr rest =>
          cases rest with
          | inl f =>
              simp [MembershipCounts.empiricalMemberEvidence_fullObservationState,
                MembershipCounts.empiricalMembershipAtom,
                Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero,
                Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport] at hx
          | inr b =>
              simp [MembershipCounts.empiricalMemberEvidence_fullObservationState,
                MembershipCounts.empiricalMembershipAtom,
                Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.one,
                Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport]

/-- The tiny empirical table supplies a concrete pair-subset fact suitable for
ASSOC/PAT monotonicity: `(feature, feature)` is below `(witness, feature)`.

The left half is the empirical `witness -> feature` fact above; the right half
is reflexivity. -/
theorem witnessFeature_pairSubsetRel_canary :
    (MembershipCounts.semanticInterpretation witnessImpliesFeatureCounts).PairSubsetRel
      MembershipConcept.feature MembershipConcept.feature
      MembershipConcept.witness MembershipConcept.feature := by
  exact
    ⟨witness_inherits_feature_canary,
      Mettapedia.Logic.AbstractInheritance.Interpretation.inherits_refl
        (I := MembershipCounts.semanticInterpretation witnessImpliesFeatureCounts)
      MembershipConcept.feature⟩

/-- The same tiny canary lifted from base attributes to actual formed
concepts: the formed `witness` concept inherits from the formed `feature`
concept. -/
theorem witness_formedConcept_inherits_feature_formedConcept_canary :
    (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence).Inherits
      (witnessImpliesFeatureFormedConcept MembershipConcept.witness)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature) := by
  have hBase :
      Mettapedia.Logic.ConceptOntology.crispExtensionalInherits
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence
        MembershipConcept.witness MembershipConcept.feature := by
    exact
      (Mettapedia.Logic.AbstractInheritance.crispInterpretation_inherits_iff
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence
        MembershipConcept.witness MembershipConcept.feature).mp
        witness_inherits_feature_canary
  change
    Mettapedia.Logic.AbstractInheritance.DualConcept.Inherits
      (Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence MembershipConcept.witness)
      (Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence MembershipConcept.feature)
  exact
    (Mettapedia.Logic.AbstractInheritance.inherits_ofCrispBaseConcept_iff
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence
      MembershipConcept.witness MembershipConcept.feature).2 hBase

/-- In the equivalence canary, the witness extent is included in the feature
extent. -/
theorem witnessEquivalentFeature_crispExtensionalInherits_witness_feature :
    Mettapedia.Logic.ConceptOntology.crispExtensionalInherits
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence
      MembershipConcept.witness MembershipConcept.feature := by
  rw [Mettapedia.Logic.ConceptOntology.crispExtensionalInherits_iff]
  intro x hx
  cases x with
  | inl n =>
      simp [witnessEquivalentFeatureMemberEvidence,
        MembershipCounts.empiricalMemberEvidence_fullObservationState,
        MembershipCounts.empiricalMembershipAtom,
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero,
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport] at hx
  | inr rest =>
      cases rest with
      | inl w =>
          exact Fin.elim0 w
      | inr rest =>
          cases rest with
          | inl f =>
              exact Fin.elim0 f
          | inr b =>
              simp [witnessEquivalentFeatureMemberEvidence,
                MembershipCounts.empiricalMemberEvidence_fullObservationState,
                MembershipCounts.empiricalMembershipAtom,
                Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.one,
                Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport]

/-- In the equivalence canary, the feature extent is included in the witness
extent. -/
theorem witnessEquivalentFeature_crispExtensionalInherits_feature_witness :
    Mettapedia.Logic.ConceptOntology.crispExtensionalInherits
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence
      MembershipConcept.feature MembershipConcept.witness := by
  rw [Mettapedia.Logic.ConceptOntology.crispExtensionalInherits_iff]
  intro x hx
  cases x with
  | inl n =>
      simp [witnessEquivalentFeatureMemberEvidence,
        MembershipCounts.empiricalMemberEvidence_fullObservationState,
        MembershipCounts.empiricalMembershipAtom,
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero,
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport] at hx
  | inr rest =>
      cases rest with
      | inl w =>
          exact Fin.elim0 w
      | inr rest =>
          cases rest with
          | inl f =>
              exact Fin.elim0 f
          | inr b =>
              simp [witnessEquivalentFeatureMemberEvidence,
                MembershipCounts.empiricalMemberEvidence_fullObservationState,
                MembershipCounts.empiricalMembershipAtom,
                Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.one,
                Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport]

/-- Equivalent empirical extents close into mutually-inheriting formed
concepts. This is the source-side same-intent canary for predicate-level
similarity. -/
theorem witnessEquivalentFeature_formedConcept_mutualInherits_canary :
    (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence).MutualInherits
      (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)
      (witnessEquivalentFeatureFormedConcept MembershipConcept.feature) := by
  constructor
  · change
      Mettapedia.Logic.AbstractInheritance.DualConcept.Inherits
        (Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.witness)
        (Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.feature)
    exact
      (Mettapedia.Logic.AbstractInheritance.inherits_ofCrispBaseConcept_iff
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence
        MembershipConcept.witness MembershipConcept.feature).2
        witnessEquivalentFeature_crispExtensionalInherits_witness_feature
  · change
      Mettapedia.Logic.AbstractInheritance.DualConcept.Inherits
        (Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.feature)
        (Mettapedia.Logic.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.witness)
    exact
      (Mettapedia.Logic.AbstractInheritance.inherits_ofCrispBaseConcept_iff
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence
        MembershipConcept.feature MembershipConcept.witness).2
        witnessEquivalentFeature_crispExtensionalInherits_feature_witness

/-- The actual formed-concept source supplies the same pair-subset fact as the
raw empirical and finite-table presentations. -/
theorem witnessFeature_formedConcept_pairSubsetRel_canary :
    (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
      Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence).PairSubsetRel
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
      (witnessImpliesFeatureFormedConcept MembershipConcept.witness)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature) := by
  exact
    ⟨witness_formedConcept_inherits_feature_formedConcept_canary,
      Mettapedia.Logic.AbstractInheritance.Interpretation.inherits_refl
        (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
          Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence)
        (witnessImpliesFeatureFormedConcept MembershipConcept.feature)⟩

/-- The finite-table version of the canary has the same empirical inheritance
fact. -/
theorem witness_inherits_feature_table_canary :
    (MembershipCounts.semanticInterpretation
      (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).Inherits
      MembershipConcept.witness MembershipConcept.feature := by
  simpa [witnessImpliesFeatureTable, FiniteWitnessFeatureTable.toMembershipCounts,
    witnessImpliesFeatureCounts] using witness_inherits_feature_canary

/-- The factor-graph table's VE query weights expose the same subset fact:
the witness marginal equals the joint feature-and-witness mass because there
are no witness-only cases. -/
theorem witnessImpliesFeatureTable_veWeight_witness_eq_feature_witness :
    FiniteWitnessFeatureTable.veWeight witnessImpliesFeatureTable
        [⟨MembershipConcept.witness, true⟩] =
      FiniteWitnessFeatureTable.veWeight witnessImpliesFeatureTable
        [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] := by
  exact
    finiteWitnessFeatureTable_veWeight_witness_eq_feature_witness_of_no_witnessOnly
      witnessImpliesFeatureTable (by rfl)

/-- The finite witness/feature table supplies the same pair-subset fact as the
raw empirical-counts presentation. -/
theorem witnessFeature_pairSubsetRel_table_canary :
    (MembershipCounts.semanticInterpretation
      (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).PairSubsetRel
      MembershipConcept.feature MembershipConcept.feature
      MembershipConcept.witness MembershipConcept.feature := by
  exact
    ⟨witness_inherits_feature_table_canary,
      Mettapedia.Logic.AbstractInheritance.Interpretation.inherits_refl
        (I := MembershipCounts.semanticInterpretation
          (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable))
        MembershipConcept.feature⟩

/-- End-to-end empirical canary: the concrete 2x2 table's pair-subset fact
feeds the finite HO predicate-vocabulary ASSOC/PAT target once the decoded
predicate vocabulary is calibrated to empirical intent. -/
theorem witnessFeature_pairSubsetRel_transports_to_predicateVocabulary_viaEmpiricalCalibration
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : MembershipConcept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation witnessImpliesFeatureCounts).meaning p).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code MembershipConcept.feature) (code MembershipConcept.feature)
      (code MembershipConcept.witness) (code MembershipConcept.feature) := by
  exact
    predicateVocabularyIntensionalPairSubsetRel_of_empiricalPairSubsetRel_viaIntentCalibration
      (counts := witnessImpliesFeatureCounts)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal W witnessFeature_pairSubsetRel_canary

/-- End-to-end finite-table canary: the factor-graph table source supplies the
same HO ASSOC/PAT pair-subset target under calibrated intent. -/
theorem witnessFeature_pairSubsetRel_transports_to_predicateVocabulary_viaFiniteTableCalibration
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : MembershipConcept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning p).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code MembershipConcept.feature) (code MembershipConcept.feature)
      (code MembershipConcept.witness) (code MembershipConcept.feature) := by
  exact
    predicateVocabularyIntensionalPairSubsetRel_of_finiteWitnessFeatureTablePairSubsetRel_viaIntentCalibration
      (table := witnessImpliesFeatureTable)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal W witnessFeature_pairSubsetRel_table_canary

/-- End-to-end formed-concept canary: the actual formed concepts generated
from the tiny empirical membership relation feed the same finite HO
predicate-vocabulary ASSOC/PAT target under calibrated intent. -/
theorem witnessFeature_pairSubsetRel_transports_to_predicateVocabulary_viaFormedConceptCalibration
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code :
      Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
            Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
            witnessImpliesFeatureMemberEvidence).meaning p).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) := by
  exact
    predicateVocabularyIntensionalPairSubsetRel_of_formedConceptPairSubsetRel_viaIntentCalibration
      (G := Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport)
      (Memb := witnessImpliesFeatureMemberEvidence)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal W witnessFeature_formedConcept_pairSubsetRel_canary

/-- End-to-end formed-concept same-intent canary: equivalent empirical
witness/feature extents close into mutually-inheriting formed concepts, and
that source-level similarity feeds the finite HO predicate-vocabulary
same-intent target under calibrated intent. -/
theorem witnessEquivalentFeature_sameIntent_transports_to_predicateVocabulary_viaFormedConceptCalibration
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code :
      Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
            Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
            witnessEquivalentFeatureMemberEvidence).meaning p).intent) :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode
      (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
      (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) := by
  exact
    predicateVocabularySameIntent_of_formedConceptMutualInherits_viaIntentCalibration
      (G := Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport)
      (Memb := witnessEquivalentFeatureMemberEvidence)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal witnessEquivalentFeature_formedConcept_mutualInherits_canary

/-- Formed-concept same-intent drives equality of the ASSOC and PAT evidence
channels for weighted finite-vocabulary predicate-pair scores.

This is a rule-facing consumer of the formed-concept similarity canary: the
source is actual concept formation, while the evidence equality is supplied by
the existing ASSOC/PAT score-family bridge. -/
theorem witnessEquivalentFeature_assocPatEvidence_eq_viaFormedConceptCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code :
      Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
            Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
            witnessEquivalentFeatureMemberEvidence).meaning p).intent)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
    (hAssocLeftWeight : 0 ≤ assocLeftWeight)
    (hAssocRightWeight : 0 ≤ assocRightWeight)
    (hPatLeftWeight : 0 ≤ patLeftWeight)
    (hPatRightWeight : 0 ≤ patRightWeight)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
      ∧
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) := by
  have hSame :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) :=
    witnessEquivalentFeature_sameIntent_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.assocPatEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hSame hSame

/-- Mixed evidence preservation for the same formed-concept same-intent source.

The extensional channel is deliberately an explicit hypothesis: formed-concept
same-intent preserves the ASSOC/PAT channels through the existing score-family
bridge, but mixed evidence is preserved only when the extensional channel is
also known to match. -/
theorem witnessEquivalentFeature_mixedEvidence_eq_viaFormedConceptCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code :
      Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.Logic.AbstractInheritance.FormedConcept
        Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation
            Mettapedia.Logic.ConceptOntology.EvidenceGate.positiveSupport
            witnessEquivalentFeatureMemberEvidence).meaning p).intent)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (m : InheritanceQueryBuilder.AssocPatSemanticModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
    (hAssocLeftWeight : 0 ≤ assocLeftWeight)
    (hAssocRightWeight : 0 ≤ assocRightWeight)
    (hPatLeftWeight : 0 ≤ patLeftWeight)
    (hPatRightWeight : 0 ≤ patRightWeight)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.assocScore W a b =
        Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State}
    (hExt :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))) :
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
      InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) := by
  have hSame :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) :=
    witnessEquivalentFeature_sameIntent_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.mixedEvidence_eq_of_assocPatSemanticModel_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc m
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hExt hSame hSame

end Mettapedia.Logic.PLNHigherOrderHOLEmpiricalAssocPatBridge
