import Mettapedia.KR.ConceptGeometry.Bridges.ProbabilityTheory.EmpiricalIntensionalFactorGraphBridge
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNTypedSemanticLayerAssocPatBridge

/-!
# Empirical Chapter-12 ASSOC/PAT Source for HO Predicate Vocabulary

This module instantiates the calibrated-intent seam from
`PLNHigherOrderHOLAssocPatBridge` on the empirical 2x2 Chapter-12 membership
table semantics. It does not identify empirical concepts with HOL predicates.
Instead, it records the exact calibration obligation needed to transport an
empirical pair-subset fact into the finite HO predicate-vocabulary ASSOC/PAT
target.
-/

namespace Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge

open Mettapedia.Logic.HOL
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.KR.ConceptGeometry.IntensionalInheritance
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel

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
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈ ((MembershipCounts.semanticInterpretation counts).meaning p).intent)
    {a b c d : MembershipConcept}
    {AssocState : Type} (W : AssocState)
    (hRel : (MembershipCounts.semanticInterpretation counts).PairSubsetRel a b c d) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentCalibration
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
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts table)).meaning p).intent)
    {a b c d : MembershipConcept}
    {AssocState : Type} (W : AssocState)
    (hRel :
      (MembershipCounts.semanticInterpretation
        (FiniteWitnessFeatureTable.toMembershipCounts table)).PairSubsetRel a b c d) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
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
    (G : Mettapedia.KR.ConceptOntology.EvidenceGate Q)
    (Memb : Obj → Attr → Q)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G Memb → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hCal : ∀ {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G Memb} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G Memb).meaning p).intent)
    {a b c d : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G Memb}
    {AssocState : Type} (W : AssocState)
    (hRel :
      (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G Memb).PairSubsetRel
        a b c d) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentCalibration
      (I := Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G Memb)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal W hRel

/-- Formed Chapter-12 concept mutual inheritance feeds the finite HO
predicate-vocabulary same-intent/similarity target under calibrated intent.

This is the predicate-level similarity companion to the pair-subset transport
above: same-intent remains mutual intensional inheritance in the existing HO
vocabulary, not a new similarity semantics. -/
theorem predicateVocabularySameIntent_of_formedConceptMutualInherits_viaIntentCalibration
    {Obj Attr Q : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
    (G : Mettapedia.KR.ConceptOntology.EvidenceGate Q)
    (Memb : Obj → Attr → Q)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G Memb → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hCal : ∀ {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G Memb} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G Memb).meaning p).intent)
    {p q : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G Memb}
    (hMutual :
      (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G Memb).MutualInherits
        p q) :
    Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode (code p) (code q) := by
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularySameIntent_of_interpretationMutualInherits_viaIntentCalibration
      (I := Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G Memb)
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
    (G : Mettapedia.KR.ConceptOntology.EvidenceGate Q)
    (Memb : Obj → Attr → Q)
    (feature witness : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G Memb)
    (hNoWitnessOnly :
      (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
        G Memb feature witness).witnessOnly = 0) :
    FiniteWitnessFeatureTable.veWeight
        (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
          G Memb feature witness)
        [⟨MembershipConcept.witness, true⟩] =
      FiniteWitnessFeatureTable.veWeight
        (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
          G Memb feature witness)
        [⟨MembershipConcept.feature, true⟩,
          ⟨MembershipConcept.witness, true⟩] := by
  exact
    finiteWitnessFeatureTable_veWeight_witness_eq_feature_witness_of_no_witnessOnly
      (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
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

/-- The witness-feature canary has a concrete positive object in the `both`
cell, so formed-concept finite-table readouts are nonvacuous. -/
instance witnessImpliesFeatureEmpiricalObject_nonempty :
    Nonempty (MembershipCounts.EmpiricalObject witnessImpliesFeatureCounts) :=
  ⟨Sum.inr (Sum.inr (Sum.inr ⟨0, by decide⟩))⟩

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
    Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence :=
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType
      (MembershipCounts.EmpiricalState witnessImpliesFeatureCounts) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType
      (MembershipCounts.EmpiricalObject witnessImpliesFeatureCounts)
  MembershipCounts.empiricalMemberEvidence witnessImpliesFeatureCounts
    (MembershipCounts.fullObservationState witnessImpliesFeatureCounts) x k

/-- The evidence-valued membership relation behind the equivalence canary,
where witness and feature have the same positive extent. -/
noncomputable def witnessEquivalentFeatureMemberEvidence
    (x : MembershipCounts.EmpiricalObject witnessEquivalentFeatureCounts)
    (k : MembershipConcept) :
    Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence :=
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType
      (MembershipCounts.EmpiricalState witnessEquivalentFeatureCounts) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType
      (MembershipCounts.EmpiricalObject witnessEquivalentFeatureCounts)
  MembershipCounts.empiricalMemberEvidence witnessEquivalentFeatureCounts
    (MembershipCounts.fullObservationState witnessEquivalentFeatureCounts) x k

/-- Base attributes in the tiny empirical canary, closed into the finite formed
concept family. This is the smallest actual formed-concept source used by the
HO ASSOC/PAT bridge. -/
noncomputable def witnessImpliesFeatureFormedConcept
    (k : MembershipConcept) :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence :=
  ⟨Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence k,
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept_mem_finiteConceptFamily
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence k⟩

/-- Base attributes in the equivalence canary, closed into the finite formed
concept family. -/
noncomputable def witnessEquivalentFeatureFormedConcept
    (k : MembershipConcept) :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence :=
  ⟨Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence k,
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept_mem_finiteConceptFamily
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence k⟩

/-- In the tiny empirical canary table, `witness` inherits from `feature`
because the witness extent is contained in the feature extent. -/
theorem witness_inherits_feature_canary :
    (MembershipCounts.semanticInterpretation witnessImpliesFeatureCounts).Inherits
      MembershipConcept.witness MembershipConcept.feature := by
  change
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.crispInterpretation
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        (fun x k =>
          letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType
              (MembershipCounts.EmpiricalState witnessImpliesFeatureCounts) :=
            Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType
              (MembershipCounts.EmpiricalObject witnessImpliesFeatureCounts)
          MembershipCounts.empiricalMemberEvidence witnessImpliesFeatureCounts
            (MembershipCounts.fullObservationState witnessImpliesFeatureCounts) x k)).Inherits
      MembershipConcept.witness MembershipConcept.feature
  rw [Mettapedia.KR.ConceptGeometry.AbstractInheritance.crispInterpretation_inherits_iff,
    Mettapedia.KR.ConceptOntology.crispExtensionalInherits_iff]
  intro x hx
  cases x with
  | inl n =>
      simp [MembershipCounts.empiricalMemberEvidence_fullObservationState,
        MembershipCounts.empiricalMembershipAtom,
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.zero,
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport] at hx
  | inr rest =>
      cases rest with
      | inl w =>
          exact Fin.elim0 w
      | inr rest =>
          cases rest with
          | inl f =>
              simp [MembershipCounts.empiricalMemberEvidence_fullObservationState,
                MembershipCounts.empiricalMembershipAtom,
                Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.zero,
                Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport] at hx
          | inr b =>
              simp [MembershipCounts.empiricalMemberEvidence_fullObservationState,
                MembershipCounts.empiricalMembershipAtom,
                Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.one,
                Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport]

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
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.Interpretation.inherits_refl
        (I := MembershipCounts.semanticInterpretation witnessImpliesFeatureCounts)
      MembershipConcept.feature⟩

/-- The same tiny canary lifted from base attributes to actual formed
concepts: the formed `witness` concept inherits from the formed `feature`
concept. -/
theorem witness_formedConcept_inherits_feature_formedConcept_canary :
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence).Inherits
      (witnessImpliesFeatureFormedConcept MembershipConcept.witness)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature) := by
  have hBase :
      Mettapedia.KR.ConceptOntology.crispExtensionalInherits
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence
        MembershipConcept.witness MembershipConcept.feature := by
    exact
      (Mettapedia.KR.ConceptGeometry.AbstractInheritance.crispInterpretation_inherits_iff
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence
        MembershipConcept.witness MembershipConcept.feature).mp
        witness_inherits_feature_canary
  change
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.Inherits
      (Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence MembershipConcept.witness)
      (Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence MembershipConcept.feature)
  exact
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.inherits_ofCrispBaseConcept_iff
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence
      MembershipConcept.witness MembershipConcept.feature).2 hBase

/-- In the equivalence canary, the witness extent is included in the feature
extent. -/
theorem witnessEquivalentFeature_crispExtensionalInherits_witness_feature :
    Mettapedia.KR.ConceptOntology.crispExtensionalInherits
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence
      MembershipConcept.witness MembershipConcept.feature := by
  rw [Mettapedia.KR.ConceptOntology.crispExtensionalInherits_iff]
  intro x hx
  cases x with
  | inl n =>
      simp [witnessEquivalentFeatureMemberEvidence,
        MembershipCounts.empiricalMemberEvidence_fullObservationState,
        MembershipCounts.empiricalMembershipAtom,
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.zero,
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport] at hx
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
                Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.one,
                Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport]

/-- In the equivalence canary, the feature extent is included in the witness
extent. -/
theorem witnessEquivalentFeature_crispExtensionalInherits_feature_witness :
    Mettapedia.KR.ConceptOntology.crispExtensionalInherits
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence
      MembershipConcept.feature MembershipConcept.witness := by
  rw [Mettapedia.KR.ConceptOntology.crispExtensionalInherits_iff]
  intro x hx
  cases x with
  | inl n =>
      simp [witnessEquivalentFeatureMemberEvidence,
        MembershipCounts.empiricalMemberEvidence_fullObservationState,
        MembershipCounts.empiricalMembershipAtom,
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.zero,
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport] at hx
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
                Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.one,
                Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport]

/-- Equivalent empirical extents close into mutually-inheriting formed
concepts. This is the source-side same-intent canary for predicate-level
similarity. -/
theorem witnessEquivalentFeature_formedConcept_mutualInherits_canary :
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence).MutualInherits
      (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)
      (witnessEquivalentFeatureFormedConcept MembershipConcept.feature) := by
  constructor
  · change
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.Inherits
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.witness)
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.feature)
    exact
      (Mettapedia.KR.ConceptGeometry.AbstractInheritance.inherits_ofCrispBaseConcept_iff
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence
        MembershipConcept.witness MembershipConcept.feature).2
        witnessEquivalentFeature_crispExtensionalInherits_witness_feature
  · change
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.Inherits
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.feature)
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.ofCrispBaseConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence MembershipConcept.witness)
    exact
      (Mettapedia.KR.ConceptGeometry.AbstractInheritance.inherits_ofCrispBaseConcept_iff
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence
        MembershipConcept.feature MembershipConcept.witness).2
        witnessEquivalentFeature_crispExtensionalInherits_feature_witness

/-- The actual formed-concept source supplies the same pair-subset fact as the
raw empirical and finite-table presentations. -/
theorem witnessFeature_formedConcept_pairSubsetRel_canary :
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence).PairSubsetRel
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
      (witnessImpliesFeatureFormedConcept MembershipConcept.witness)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature) := by
  exact
    ⟨witness_formedConcept_inherits_feature_formedConcept_canary,
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.Interpretation.inherits_refl
        (I := Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence)
        (witnessImpliesFeatureFormedConcept MembershipConcept.feature)⟩

/-- The finite witness/feature table generated by the same formed-concept
source used by the HO ASSOC/PAT bridge.

This is the concrete Chapter-12 source table for the witness-feature canary:
it keeps the pair-subset source and the information-gain ASSOC readout tied to
one formed-concept interpretation. -/
noncomputable def witnessFeatureFormedInheritanceTable :
    FiniteWitnessFeatureTable :=
  Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable
    Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
    witnessImpliesFeatureMemberEvidence
    (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
    (witnessImpliesFeatureFormedConcept MembershipConcept.witness)

/-- The formed-concept source used for the HO pair-subset bridge also has its
ASSOC/log-ratio score generated by the exact finite-table VE query.

This theorem does not identify PAT with ASSOC.  It only records that the ASSOC
side of this formed source has the standard Chapter-12 information-gain
readout, while PAT remains the separate structural channel handled by the
typed ASSOC/PAT bridge. -/
theorem witnessFeature_formedConcept_assocLogRatio_eq_veQueryScore :
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence)
        (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
        (witnessImpliesFeatureFormedConcept MembershipConcept.witness) =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            witnessFeatureFormedInheritanceTable
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            witnessFeatureFormedInheritanceTable
            [⟨MembershipConcept.feature, true⟩,
              ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              witnessFeatureFormedInheritanceTable
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          witnessFeatureFormedInheritanceTable
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              witnessFeatureFormedInheritanceTable []) := by
  simpa [witnessFeatureFormedInheritanceTable,
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.formedConceptInheritanceTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.finiteInheritanceLogRatioBits_formedConceptInterpretation_eq_veQueryScore
      (G := Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport)
      (M := witnessImpliesFeatureMemberEvidence)
      (subConcept := witnessImpliesFeatureFormedConcept MembershipConcept.feature)
      (superConcept := witnessImpliesFeatureFormedConcept MembershipConcept.witness)

/-- Proof-carrying profile for the concrete formed-concept Chapter-12 source.

The fields keep the semantic source together: actual formed concepts provide a
pair-subset fact, an equivalent-source same-intent canary, and the ASSOC
log-ratio readout through the finite-table VE bridge.  Downstream HO ASSOC/PAT
theorems consume this profile through calibrated intent; this profile itself is
not a separate PAT semantics. -/
structure FormedConceptChapter12SourceProfile where
  witnessInheritsFeature :
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence).Inherits
      (witnessImpliesFeatureFormedConcept MembershipConcept.witness)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
  equivalentWitnessFeatureMutualInherits :
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessEquivalentFeatureMemberEvidence).MutualInherits
      (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)
      (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)
  witnessFeaturePairSubset :
    (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
      Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
      witnessImpliesFeatureMemberEvidence).PairSubsetRel
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
      (witnessImpliesFeatureFormedConcept MembershipConcept.witness)
      (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
  assocLogRatioReadout :
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence)
        (witnessImpliesFeatureFormedConcept MembershipConcept.feature)
        (witnessImpliesFeatureFormedConcept MembershipConcept.witness) =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            witnessFeatureFormedInheritanceTable
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            witnessFeatureFormedInheritanceTable
            [⟨MembershipConcept.feature, true⟩,
              ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              witnessFeatureFormedInheritanceTable
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          witnessFeatureFormedInheritanceTable
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              witnessFeatureFormedInheritanceTable [])

/-- Concrete formed-concept Chapter-12 source package consumed by the public
ASSOC/PAT theorem index. -/
noncomputable def formedConceptChapter12SourceProfile :
    FormedConceptChapter12SourceProfile where
  witnessInheritsFeature :=
    witness_formedConcept_inherits_feature_formedConcept_canary
  equivalentWitnessFeatureMutualInherits :=
    witnessEquivalentFeature_formedConcept_mutualInherits_canary
  witnessFeaturePairSubset :=
    witnessFeature_formedConcept_pairSubsetRel_canary
  assocLogRatioReadout :=
    witnessFeature_formedConcept_assocLogRatio_eq_veQueryScore

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
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.Interpretation.inherits_refl
        (I := MembershipCounts.semanticInterpretation
          (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable))
        MembershipConcept.feature⟩

/-- Tiny finite-table guardrail with a real witness-only case.

Here the witness marginal is strictly larger than the feature/witness joint
mass, so the no-witness-only hypothesis in the positive VE source theorem is
load-bearing. -/
def witnessOnlyCounterexampleTable : FiniteWitnessFeatureTable where
  neither := 0
  witnessOnly := 1
  featureOnly := 0
  both := 1
  total_pos := by decide

/-- Negative finite-table source canary: if a witness-only case exists, the
witness marginal need not equal the feature/witness joint. -/
theorem witnessOnlyCounterexampleTable_veWeight_witness_ne_feature_witness :
    FiniteWitnessFeatureTable.veWeight witnessOnlyCounterexampleTable
        [⟨MembershipConcept.witness, true⟩] ≠
      FiniteWitnessFeatureTable.veWeight witnessOnlyCounterexampleTable
        [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] := by
  change
    MembershipCounts.veWeight (FiniteWitnessFeatureTable.toMembershipCounts witnessOnlyCounterexampleTable)
        [⟨MembershipConcept.witness, true⟩] ≠
      MembershipCounts.veWeight (FiniteWitnessFeatureTable.toMembershipCounts witnessOnlyCounterexampleTable)
        [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩]
  rw [MembershipCounts.veWeight_witness_true,
    MembershipCounts.veWeight_feature_witness_true]
  norm_num [FiniteWitnessFeatureTable.toMembershipCounts,
    MembershipCounts.witnessSupport,
    witnessOnlyCounterexampleTable]

/-- Proof-carrying profile for the finite-table Chapter-12 source algebra.

This packages the positive no-witness-only VE equality, the pair-subset source
fact it supports, and the matching witness-only counterexample.  It is a source
profile for the empirical/factor-graph side of ASSOC/PAT, not a new rule
semantics. -/
structure FiniteTableChapter12SourceProfile where
  noWitnessOnlyVEReadout :
    FiniteWitnessFeatureTable.veWeight witnessImpliesFeatureTable
        [⟨MembershipConcept.witness, true⟩] =
      FiniteWitnessFeatureTable.veWeight witnessImpliesFeatureTable
        [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩]
  pairSubset :
    (MembershipCounts.semanticInterpretation
      (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).PairSubsetRel
      MembershipConcept.feature MembershipConcept.feature
      MembershipConcept.witness MembershipConcept.feature
  witnessOnlyCounterexample :
    FiniteWitnessFeatureTable.veWeight witnessOnlyCounterexampleTable
        [⟨MembershipConcept.witness, true⟩] ≠
      FiniteWitnessFeatureTable.veWeight witnessOnlyCounterexampleTable
        [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩]

/-- Concrete finite-table Chapter-12 source algebra package consumed by the
public ASSOC/PAT theorem index. -/
noncomputable def finiteTableChapter12SourceProfile :
    FiniteTableChapter12SourceProfile where
  noWitnessOnlyVEReadout :=
    witnessImpliesFeatureTable_veWeight_witness_eq_feature_witness
  pairSubset :=
    witnessFeature_pairSubsetRel_table_canary
  witnessOnlyCounterexample :=
    witnessOnlyCounterexampleTable_veWeight_witness_ne_feature_witness

/-! ## OSLF pattern-coded source surface -/

/-- The concrete OSLF pattern type used to name the Chapter-12 finite-table
source concepts. -/
abbrev Chapter12Pattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- OSLF surface name for the feature concept in the finite-table canary. -/
def chapter12FeaturePattern : Chapter12Pattern :=
  .apply "chapter12-feature" []

/-- OSLF surface name for the witness concept in the finite-table canary. -/
def chapter12WitnessPattern : Chapter12Pattern :=
  .apply "chapter12-witness" []

/-- Tiny classifier from OSLF pattern names into the Chapter-12 membership
concepts.  Unknown patterns default to `feature`; the named witness pattern is
the only witness-classified pattern in this minimal source surface. -/
def chapter12PatternConcept (p : Chapter12Pattern) : MembershipConcept :=
  if p = chapter12WitnessPattern then
    MembershipConcept.witness
  else
    MembershipConcept.feature

/-- The concrete feature and witness OSLF names are distinct. -/
theorem chapter12FeaturePattern_ne_witnessPattern :
    chapter12FeaturePattern ≠ chapter12WitnessPattern := by
  decide

/-- The feature OSLF name classifies as the feature concept. -/
theorem chapter12PatternConcept_feature :
    chapter12PatternConcept chapter12FeaturePattern = MembershipConcept.feature := by
  simp [chapter12PatternConcept, chapter12FeaturePattern_ne_witnessPattern]

/-- The witness OSLF name classifies as the witness concept. -/
theorem chapter12PatternConcept_witness :
    chapter12PatternConcept chapter12WitnessPattern = MembershipConcept.witness := by
  simp [chapter12PatternConcept]

/-- Role-wrapped OSLF pattern syntax for Chapter-12 concept sources.

The role name supplies the concept channel while the payload stays available to
carry richer surface syntax.  This is a source classifier over OSLF patterns,
not a new ASSOC/PAT evidence semantics. -/
def chapter12RolePattern (role : String) (payload : Chapter12Pattern) : Chapter12Pattern :=
  .apply "chapter12-role" [.apply role [], payload]

/-- Richer Chapter-12 pattern classifier.

Role-wrapped patterns classify by their explicit role.  Other patterns fall
back to the tiny literal classifier above, so the original finite-table canary
remains a special case. -/
def chapter12RichPatternConcept : Chapter12Pattern → MembershipConcept
  | .apply "chapter12-role" [.apply "witness" [], _] => MembershipConcept.witness
  | .apply "chapter12-role" [.apply "feature" [], _] => MembershipConcept.feature
  | p => chapter12PatternConcept p

/-- Any role-wrapped feature payload classifies as the feature concept. -/
theorem chapter12RichPatternConcept_featureRole (payload : Chapter12Pattern) :
    chapter12RichPatternConcept (chapter12RolePattern "feature" payload) =
      MembershipConcept.feature := by
  rfl

/-- Any role-wrapped witness payload classifies as the witness concept. -/
theorem chapter12RichPatternConcept_witnessRole (payload : Chapter12Pattern) :
    chapter12RichPatternConcept (chapter12RolePattern "witness" payload) =
      MembershipConcept.witness := by
  rfl

/-- A role outside the Chapter-12 source vocabulary falls back to the underlying
literal classifier.  The concrete fallback remains feature for this canary. -/
theorem chapter12RichPatternConcept_otherRole_fallback (payload : Chapter12Pattern) :
    chapter12RichPatternConcept (chapter12RolePattern "distractor" payload) =
      MembershipConcept.feature := by
  simp [chapter12RichPatternConcept, chapter12RolePattern, chapter12PatternConcept,
    chapter12WitnessPattern]

/-- Negative classifier guardrail: a feature role never classifies as witness. -/
theorem chapter12RichPatternConcept_featureRole_ne_witness (payload : Chapter12Pattern) :
    chapter12RichPatternConcept (chapter12RolePattern "feature" payload) ≠
      MembershipConcept.witness := by
  simp [chapter12RichPatternConcept_featureRole payload]

/-- Negative classifier guardrail: a witness role never classifies as feature. -/
theorem chapter12RichPatternConcept_witnessRole_ne_feature (payload : Chapter12Pattern) :
    chapter12RichPatternConcept (chapter12RolePattern "witness" payload) ≠
      MembershipConcept.feature := by
  simp [chapter12RichPatternConcept_witnessRole payload]

/-- Negative classifier guardrail: an out-of-vocabulary role's concrete
fallback is not witness in this finite canary. -/
theorem chapter12RichPatternConcept_otherRole_ne_witness (payload : Chapter12Pattern) :
    chapter12RichPatternConcept (chapter12RolePattern "distractor" payload) ≠
      MembershipConcept.witness := by
  simp [chapter12RichPatternConcept_otherRole_fallback payload]

/-- Rich feature source: a role wrapper with a nontrivial payload. -/
def chapter12RichFeaturePattern : Chapter12Pattern :=
  chapter12RolePattern "feature" (.apply "observed" [chapter12FeaturePattern])

/-- Rich witness source: a role wrapper with a nontrivial payload. -/
def chapter12RichWitnessPattern : Chapter12Pattern :=
  chapter12RolePattern "witness" (.apply "observed" [chapter12WitnessPattern])

/-- The rich feature and witness source patterns are syntactically distinct. -/
theorem chapter12RichFeaturePattern_ne_witnessPattern :
    chapter12RichFeaturePattern ≠ chapter12RichWitnessPattern := by
  decide

/-- The concrete rich feature source classifies as the feature concept. -/
theorem chapter12RichPatternConcept_feature :
    chapter12RichPatternConcept chapter12RichFeaturePattern =
      MembershipConcept.feature :=
  chapter12RichPatternConcept_featureRole _

/-- The concrete rich witness source classifies as the witness concept. -/
theorem chapter12RichPatternConcept_witness :
    chapter12RichPatternConcept chapter12RichWitnessPattern =
      MembershipConcept.witness :=
  chapter12RichPatternConcept_witnessRole _

/-- Classifier-parametric pattern-coded finite-table transport.

Any OSLF pattern classifier with designated feature and witness patterns can
feed the existing finite-table pair-subset source into the predicate-vocabulary
ASSOC/PAT target.  The classifier supplies only the source typing; the evidence
flow remains the existing calibrated-intent bridge. -/
theorem chapter12PatternCoded_pairSubsetRel_transports_to_predicateVocabulary_of_classifies
    (conceptOf : Chapter12Pattern → MembershipConcept)
    (featurePattern witnessPattern : Chapter12Pattern)
    (hFeature : conceptOf featurePattern = MembershipConcept.feature)
    (hWitness : conceptOf witnessPattern = MembershipConcept.witness)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Chapter12Pattern → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : Chapter12Pattern} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning
            (conceptOf p)).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code featurePattern) (code featurePattern)
      (code witnessPattern) (code featurePattern) := by
  let conceptCode : MembershipConcept → Pred := fun c =>
    match c with
    | MembershipConcept.feature => code featurePattern
    | MembershipConcept.witness => code witnessPattern
  have hCalConcept :
      ∀ {p : MembershipConcept} {r : Pred},
        r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) M σ decode).meaning (conceptCode p)).intent ↔
          attrOf r ∈
            ((MembershipCounts.semanticInterpretation
                (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning p).intent := by
    intro p r
    cases p with
    | feature =>
        simpa [conceptCode, hFeature] using
          (hCal (p := featurePattern) (r := r))
    | witness =>
        simpa [conceptCode, hWitness] using
          (hCal (p := witnessPattern) (r := r))
  simpa [conceptCode] using
    predicateVocabularyIntensionalPairSubsetRel_of_finiteWitnessFeatureTablePairSubsetRel_viaIntentCalibration
      (table := witnessImpliesFeatureTable)
      (Base := Base) (Const := Const) (M := M) (σ := σ)
      (code := conceptCode) (decode := decode) attrOf hCalConcept W
      witnessFeature_pairSubsetRel_table_canary

/-- Proof-carrying profile for the pattern-coded Chapter-12 finite-table
surface.

The profile records that concrete OSLF pattern names select the same
witness/feature source algebra already proven for the finite table.  It is a
source classifier for the existing calibrated-intent bridge, not a new
ASSOC/PAT semantics. -/
structure PatternCodedChapter12SourceProfile where
  featureClassifies :
    chapter12PatternConcept chapter12FeaturePattern = MembershipConcept.feature
  witnessClassifies :
    chapter12PatternConcept chapter12WitnessPattern = MembershipConcept.witness
  featureWitnessDistinct :
    chapter12FeaturePattern ≠ chapter12WitnessPattern
  finiteTableSource :
    FiniteTableChapter12SourceProfile

/-- Concrete pattern-coded Chapter-12 source package consumed by the public
ASSOC/PAT theorem index. -/
noncomputable def patternCodedChapter12SourceProfile :
    PatternCodedChapter12SourceProfile where
  featureClassifies :=
    chapter12PatternConcept_feature
  witnessClassifies :=
    chapter12PatternConcept_witness
  featureWitnessDistinct :=
    chapter12FeaturePattern_ne_witnessPattern
  finiteTableSource :=
    finiteTableChapter12SourceProfile

/-- End-to-end pattern-coded finite-table canary.

The concrete OSLF pattern names for `feature` and `witness` are first classified
into the Chapter-12 finite witness/feature table.  The already-proven finite
table pair-subset source then feeds the finite HO predicate-vocabulary
ASSOC/PAT target through the same calibrated-intent seam. -/
theorem chapter12PatternCoded_pairSubsetRel_transports_to_predicateVocabulary_viaFiniteTableCalibration
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Chapter12Pattern → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : Chapter12Pattern} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning
            (chapter12PatternConcept p)).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code chapter12FeaturePattern) (code chapter12FeaturePattern)
      (code chapter12WitnessPattern) (code chapter12FeaturePattern) := by
  exact
    chapter12PatternCoded_pairSubsetRel_transports_to_predicateVocabulary_of_classifies
      chapter12PatternConcept chapter12FeaturePattern chapter12WitnessPattern
      chapter12PatternConcept_feature chapter12PatternConcept_witness
      M σ code decode attrOf hCal W

/-- Rich role-pattern finite-table transport.

The source patterns are no longer bare concept names: they are role wrappers
with payloads.  The proof is still the classifier-parametric finite-table
transport above, so richer syntax does not create a parallel ASSOC/PAT
semantics. -/
theorem chapter12RichPatternCoded_pairSubsetRel_transports_to_predicateVocabulary_viaFiniteTableCalibration
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Chapter12Pattern → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : Chapter12Pattern} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning
            (chapter12RichPatternConcept p)).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code chapter12RichFeaturePattern) (code chapter12RichFeaturePattern)
      (code chapter12RichWitnessPattern) (code chapter12RichFeaturePattern) := by
  exact
    chapter12PatternCoded_pairSubsetRel_transports_to_predicateVocabulary_of_classifies
      chapter12RichPatternConcept chapter12RichFeaturePattern chapter12RichWitnessPattern
      chapter12RichPatternConcept_feature chapter12RichPatternConcept_witness
      M σ code decode attrOf hCal W

/-- Proof-carrying profile for the richer role-pattern Chapter-12 source.

This records the payload-parametric role classifier and the concrete rich
feature/witness source used by the rule-facing transport. -/
structure RichPatternCodedChapter12SourceProfile where
  featureRoleClassifies :
    ∀ payload : Chapter12Pattern,
      chapter12RichPatternConcept (chapter12RolePattern "feature" payload) =
        MembershipConcept.feature
  witnessRoleClassifies :
    ∀ payload : Chapter12Pattern,
      chapter12RichPatternConcept (chapter12RolePattern "witness" payload) =
        MembershipConcept.witness
  otherRoleFallsBack :
    ∀ payload : Chapter12Pattern,
      chapter12RichPatternConcept (chapter12RolePattern "distractor" payload) =
        MembershipConcept.feature
  featureRoleNotWitness :
    ∀ payload : Chapter12Pattern,
      chapter12RichPatternConcept (chapter12RolePattern "feature" payload) ≠
        MembershipConcept.witness
  witnessRoleNotFeature :
    ∀ payload : Chapter12Pattern,
      chapter12RichPatternConcept (chapter12RolePattern "witness" payload) ≠
        MembershipConcept.feature
  otherRoleNotWitness :
    ∀ payload : Chapter12Pattern,
      chapter12RichPatternConcept (chapter12RolePattern "distractor" payload) ≠
        MembershipConcept.witness
  richFeatureWitnessDistinct :
    chapter12RichFeaturePattern ≠ chapter12RichWitnessPattern
  finiteTableSource :
    FiniteTableChapter12SourceProfile

/-- Concrete richer role-pattern Chapter-12 source package. -/
noncomputable def richPatternCodedChapter12SourceProfile :
    RichPatternCodedChapter12SourceProfile where
  featureRoleClassifies :=
    chapter12RichPatternConcept_featureRole
  witnessRoleClassifies :=
    chapter12RichPatternConcept_witnessRole
  otherRoleFallsBack :=
    chapter12RichPatternConcept_otherRole_fallback
  featureRoleNotWitness :=
    chapter12RichPatternConcept_featureRole_ne_witness
  witnessRoleNotFeature :=
    chapter12RichPatternConcept_witnessRole_ne_feature
  otherRoleNotWitness :=
    chapter12RichPatternConcept_otherRole_ne_witness
  richFeatureWitnessDistinct :=
    chapter12RichFeaturePattern_ne_witnessPattern
  finiteTableSource :=
    finiteTableChapter12SourceProfile

/-- Pattern-coded finite-table transport drives typed semantic-layer ASSOC/PAT
evidence monotonicity.

This is the rule-facing consumer of the OSLF pattern source above: the concrete
pattern names supply the pair-subset relation, while the typed layer still
selects the existing weighted ASSOC/PAT evidence channels. -/
theorem chapter12PatternCoded_semanticLayerAssocPatEvidence_mono_viaFiniteTableCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (layer : SemanticInheritanceLayer)
    (hLayer :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
        layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code : Chapter12Pattern → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : Chapter12Pattern} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning
            (chapter12PatternConcept p)).intent)
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc
        (code chapter12FeaturePattern)
        (code chapter12FeaturePattern) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code chapter12WitnessPattern)
          (code chapter12FeaturePattern)
      ∧
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc
        (code chapter12FeaturePattern)
        (code chapter12FeaturePattern) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code chapter12WitnessPattern)
          (code chapter12FeaturePattern) := by
  have hRel :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W
        (code chapter12FeaturePattern) (code chapter12FeaturePattern)
        (code chapter12WitnessPattern) (code chapter12FeaturePattern) :=
    chapter12PatternCoded_pairSubsetRel_transports_to_predicateVocabulary_viaFiniteTableCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal W
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerAssocPatEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      layer hLayer M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hRel

/-- Rich role-pattern finite-table transport drives typed semantic-layer
ASSOC/PAT evidence monotonicity.

This is the same consumer theorem as the bare pattern-coded canary, but the
source patterns are role wrappers with payloads.  The proof deliberately routes
through the existing rich classifier transport and the shared typed
semantic-layer ASSOC/PAT monotonicity theorem. -/
theorem chapter12RichPatternCoded_semanticLayerAssocPatEvidence_mono_viaFiniteTableCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (layer : SemanticInheritanceLayer)
    (hLayer :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
        layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code : Chapter12Pattern → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : Chapter12Pattern} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning
            (chapter12RichPatternConcept p)).intent)
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc
        (code chapter12RichFeaturePattern)
        (code chapter12RichFeaturePattern) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code chapter12RichWitnessPattern)
          (code chapter12RichFeaturePattern)
      ∧
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc
        (code chapter12RichFeaturePattern)
        (code chapter12RichFeaturePattern) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code chapter12RichWitnessPattern)
          (code chapter12RichFeaturePattern) := by
  have hRel :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W
        (code chapter12RichFeaturePattern) (code chapter12RichFeaturePattern)
        (code chapter12RichWitnessPattern) (code chapter12RichFeaturePattern) :=
    chapter12RichPatternCoded_pairSubsetRel_transports_to_predicateVocabulary_viaFiniteTableCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal W
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerAssocPatEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      layer hLayer M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hRel

/-- Proof-carrying profile for the pattern-coded Chapter-12 semantic-layer
consumer.

This packages the source classifier together with the theorem that consumes it
through the existing typed semantic-layer ASSOC/PAT monotonicity bridge. It is
not a new semantics and it does not assert numeric endpoint tightness. -/
structure PatternCodedSemanticLayerConsumerProfile where
  source :
    PatternCodedChapter12SourceProfile
  semanticLayerAssocPatMono :
    ∀ {Base : Type u} {Const : Ty Base → Type v}
      {State Pred PairQuery : Type}
      [EvidenceType State]
      [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
      (layer : SemanticInheritanceLayer)
      (_hLayer :
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
          layer)
      (M : HenkinModel.{u, v, w} Base Const)
      (σ : Ty Base)
      [Fintype Pred]
      (code : Chapter12Pattern → Pred)
      (decode : Pred →
        Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
          (Base := Base) (Const := Const) σ)
      (attrOf : Pred → MembershipConcept)
      (_hCal : ∀ {p : Chapter12Pattern} {r : Pred},
        r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
          attrOf r ∈
            ((MembershipCounts.semanticInterpretation
                (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning
              (chapter12PatternConcept p)).intent)
      (pairEnc : InheritanceQueryBuilder Pred PairQuery)
      (model : InheritanceQueryBuilder.IntensionalScoreModel
        (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
      {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
      (_hAssocLeftWeight : 0 ≤ assocLeftWeight)
      (_hAssocRightWeight : 0 ≤ assocRightWeight)
      (_hPatLeftWeight : 0 ≤ patLeftWeight)
      (_hPatRightWeight : 0 ≤ patRightWeight)
      (_hAssocScore : ∀ (W : State) (a b : Pred),
        model.assocScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            assocLeftWeight assocRightWeight a b)
      (_hPatScore : ∀ (W : State) (a b : Pred),
        model.patScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            patLeftWeight patRightWeight a b)
      {W : State},
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code chapter12FeaturePattern)
          (code chapter12FeaturePattern) ≤
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .assoc W pairEnc
            (code chapter12WitnessPattern)
            (code chapter12FeaturePattern)
        ∧
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code chapter12FeaturePattern)
          (code chapter12FeaturePattern) ≤
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .pat W pairEnc
            (code chapter12WitnessPattern)
            (code chapter12FeaturePattern)

/-- Concrete pattern-coded semantic-layer consumer package. -/
noncomputable def patternCodedSemanticLayerConsumerProfile :
    PatternCodedSemanticLayerConsumerProfile where
  source :=
    patternCodedChapter12SourceProfile
  semanticLayerAssocPatMono :=
    @chapter12PatternCoded_semanticLayerAssocPatEvidence_mono_viaFiniteTableCalibration

/-- Proof-carrying profile for the richer role-pattern Chapter-12 semantic-layer
consumer.

The source classifier recognizes payload-carrying role wrappers before the same
finite-table and typed semantic-layer ASSOC/PAT machinery consumes the source.
It is intentionally a source-syntax refinement, not a new evidence semantics. -/
structure RichPatternCodedSemanticLayerConsumerProfile where
  source :
    RichPatternCodedChapter12SourceProfile
  semanticLayerAssocPatMono :
    ∀ {Base : Type u} {Const : Ty Base → Type v}
      {State Pred PairQuery : Type}
      [EvidenceType State]
      [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
      (layer : SemanticInheritanceLayer)
      (_hLayer :
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
          layer)
      (M : HenkinModel.{u, v, w} Base Const)
      (σ : Ty Base)
      [Fintype Pred]
      (code : Chapter12Pattern → Pred)
      (decode : Pred →
        Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
          (Base := Base) (Const := Const) σ)
      (attrOf : Pred → MembershipConcept)
      (_hCal : ∀ {p : Chapter12Pattern} {r : Pred},
        r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
          attrOf r ∈
            ((MembershipCounts.semanticInterpretation
                (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning
              (chapter12RichPatternConcept p)).intent)
      (pairEnc : InheritanceQueryBuilder Pred PairQuery)
      (model : InheritanceQueryBuilder.IntensionalScoreModel
        (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
      {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
      (_hAssocLeftWeight : 0 ≤ assocLeftWeight)
      (_hAssocRightWeight : 0 ≤ assocRightWeight)
      (_hPatLeftWeight : 0 ≤ patLeftWeight)
      (_hPatRightWeight : 0 ≤ patRightWeight)
      (_hAssocScore : ∀ (W : State) (a b : Pred),
        model.assocScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            assocLeftWeight assocRightWeight a b)
      (_hPatScore : ∀ (W : State) (a b : Pred),
        model.patScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            patLeftWeight patRightWeight a b)
      {W : State},
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code chapter12RichFeaturePattern)
          (code chapter12RichFeaturePattern) ≤
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .assoc W pairEnc
            (code chapter12RichWitnessPattern)
            (code chapter12RichFeaturePattern)
        ∧
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code chapter12RichFeaturePattern)
          (code chapter12RichFeaturePattern) ≤
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .pat W pairEnc
            (code chapter12RichWitnessPattern)
            (code chapter12RichFeaturePattern)

/-- Concrete richer role-pattern semantic-layer consumer package. -/
noncomputable def richPatternCodedSemanticLayerConsumerProfile :
    RichPatternCodedSemanticLayerConsumerProfile where
  source :=
    richPatternCodedChapter12SourceProfile
  semanticLayerAssocPatMono :=
    @chapter12RichPatternCoded_semanticLayerAssocPatEvidence_mono_viaFiniteTableCalibration

/-- End-to-end empirical canary: the concrete 2x2 table's pair-subset fact
feeds the finite HO predicate-vocabulary ASSOC/PAT target once the decoded
predicate vocabulary is calibrated to empirical intent. -/
theorem witnessFeature_pairSubsetRel_transports_to_predicateVocabulary_viaEmpiricalCalibration
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : MembershipConcept → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation witnessImpliesFeatureCounts).meaning p).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
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
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀ {p : MembershipConcept} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((MembershipCounts.semanticInterpretation
              (FiniteWitnessFeatureTable.toMembershipCounts witnessImpliesFeatureTable)).meaning p).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
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
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
            witnessImpliesFeatureMemberEvidence).meaning p).intent)
    {AssocState : Type} (W : AssocState) :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
      (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) := by
  exact
    predicateVocabularyIntensionalPairSubsetRel_of_formedConceptPairSubsetRel_viaIntentCalibration
      (G := Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport)
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
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
            witnessEquivalentFeatureMemberEvidence).meaning p).intent) :
    Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode
      (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
      (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) := by
  exact
    predicateVocabularySameIntent_of_formedConceptMutualInherits_viaIntentCalibration
      (G := Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport)
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
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
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
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) :=
    witnessEquivalentFeature_sameIntent_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.assocPatEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hSame hSame

/-- Typed semantic-layer version of the formed-concept same-intent consumer.

The formed-concept source still supplies same intent; the semantic-layer tag
only selects the existing ASSOC/PAT channel.  Extensional and mixed tags are
excluded by the explicit `semanticLayerIntensionalFacing` premise. -/
theorem witnessEquivalentFeature_semanticLayerAssocPatEvidence_eq_viaFormedConceptCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (layer : SemanticInheritanceLayer)
    (hLayer :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
        layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code :
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
      ∧
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) := by
  have hSame :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) :=
    witnessEquivalentFeature_sameIntent_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerAssocPatEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      layer hLayer M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hSame hSame

/-- Proof-carrying profile for the formed-concept ASSOC/PAT semantic-layer
equality theorem.

The source is the actual Chapter-12 formed-concept mutual-inheritance canary.
The consumer theorem routes same intent through the existing typed semantic
layer, so only intensional-facing layers expose ASSOC/PAT equality. This is a
reader-facing package for the proven equality theorem, not a new ASSOC/PAT
semantics. -/
structure FormedConceptSemanticLayerAssocPatEqualityProfile where
  source :
    FormedConceptChapter12SourceProfile
  assocPatEqOfIntensionalFacing :
    ∀ {Base : Type u} {Const : Ty Base → Type v}
      {State Pred PairQuery : Type}
      [EvidenceType State]
      [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
      (layer : SemanticInheritanceLayer)
      (_hLayer :
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
          layer)
      (M : HenkinModel.{u, v, w} Base Const)
      (σ : Ty Base)
      [Fintype Pred]
      (code :
        Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence → Pred)
      (decode : Pred →
        Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
          (Base := Base) (Const := Const) σ)
      (attrOf : Pred → MembershipConcept)
      (_hCal : ∀
        {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence} {r : Pred},
        r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
          attrOf r ∈
            ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
              Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
              witnessEquivalentFeatureMemberEvidence).meaning p).intent)
      (pairEnc : InheritanceQueryBuilder Pred PairQuery)
      (model : InheritanceQueryBuilder.IntensionalScoreModel
        (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
      {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
      (_hAssocLeftWeight : 0 ≤ assocLeftWeight)
      (_hAssocRightWeight : 0 ≤ assocRightWeight)
      (_hPatLeftWeight : 0 ≤ patLeftWeight)
      (_hPatRightWeight : 0 ≤ patRightWeight)
      (_hAssocScore : ∀ (W : State) (a b : Pred),
        model.assocScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            assocLeftWeight assocRightWeight a b)
      (_hPatScore : ∀ (W : State) (a b : Pred),
        model.patScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            patLeftWeight patRightWeight a b)
      {W : State},
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .assoc W pairEnc
            (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
            (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
        ∧
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .pat W pairEnc
            (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
            (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))

/-- Concrete formed-concept ASSOC/PAT semantic-layer equality package. -/
noncomputable def formedConceptSemanticLayerAssocPatEqualityProfile :
    FormedConceptSemanticLayerAssocPatEqualityProfile where
  source :=
    formedConceptChapter12SourceProfile
  assocPatEqOfIntensionalFacing :=
    @witnessEquivalentFeature_semanticLayerAssocPatEvidence_eq_viaFormedConceptCalibration

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
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
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
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) :=
    witnessEquivalentFeature_sameIntent_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.mixedEvidence_eq_of_assocPatSemanticModel_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc m
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hExt hSame hSame

/-- Formed-concept same-intent turns the typed mixed/extensional channel
separation theorem into a concrete Chapter-12 consumer.

The source is the actual `witnessEquivalentFeature` formed-concept calibration
canary: formed concepts provide same intent, weighted ASSOC/PAT correspondences
fix the intensional channels, and a left-cancellable mixed combiner makes mixed
evidence equality equivalent to extensional evidence equality. -/
theorem witnessEquivalentFeature_semanticLayerMixedEvidence_eq_iff_extensionalEvidence_eq_viaFormedConceptCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code :
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessEquivalentFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    (hCancel :
      ∀ {x y assoc pat :
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
        m.combine x assoc pat = m.combine y assoc pat → x = y)
    {W : State} :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) ↔
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .extensional .assoc W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .extensional .assoc W pairEnc
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) := by
  have hSame :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
        (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) :=
    witnessEquivalentFeature_sameIntent_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerMixedEvidence_eq_iff_extensionalEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc m
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hCancel hSame hSame

/-- Proof-carrying profile for the formed-concept mixed semantic-layer
boundary.

The source is actual Chapter-12 concept formation. The consumer theorem says
that, once same intent fixes the ASSOC/PAT channels, mixed-channel equality is
equivalent to extensional equality exactly under the explicit cancellativity
side condition. This is a boundary package, not a new mixed semantics. -/
structure FormedConceptMixedSemanticLayerBoundaryProfile where
  source :
    FormedConceptChapter12SourceProfile
  mixedEqIffExtensionalEq :
    ∀ {Base : Type u} {Const : Ty Base → Type v}
      {State Pred PairQuery : Type}
      [EvidenceType State]
      [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
      (M : HenkinModel.{u, v, w} Base Const)
      (σ : Ty Base)
      [Fintype Pred]
      (code :
        Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence → Pred)
      (decode : Pred →
        Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
          (Base := Base) (Const := Const) σ)
      (attrOf : Pred → MembershipConcept)
      (_hCal : ∀
        {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessEquivalentFeatureMemberEvidence} {r : Pred},
        r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
          attrOf r ∈
            ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
              Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
              witnessEquivalentFeatureMemberEvidence).meaning p).intent)
      (pairEnc : InheritanceQueryBuilder Pred PairQuery)
      (m : InheritanceQueryBuilder.AssocPatSemanticModel
        (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
      {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
      (_hAssocLeftWeight : 0 ≤ assocLeftWeight)
      (_hAssocRightWeight : 0 ≤ assocRightWeight)
      (_hPatLeftWeight : 0 ≤ patLeftWeight)
      (_hPatRightWeight : 0 ≤ patRightWeight)
      (_hAssocScore : ∀ (W : State) (a b : Pred),
        m.scoreModel.assocScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            assocLeftWeight assocRightWeight a b)
      (_hPatScore : ∀ (W : State) (a b : Pred),
        m.scoreModel.patScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            patLeftWeight patRightWeight a b)
      (_hCancel :
        ∀ {x y assoc pat :
            Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
          m.combine x assoc pat = m.combine y assoc pat → x = y)
      {W : State},
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .mixed .assoc W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .mixed .assoc W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature)) ↔
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.witness)) =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))
          (code (witnessEquivalentFeatureFormedConcept MembershipConcept.feature))

/-- Concrete formed-concept mixed semantic-layer boundary package. -/
noncomputable def formedConceptMixedSemanticLayerBoundaryProfile :
    FormedConceptMixedSemanticLayerBoundaryProfile where
  source :=
    formedConceptChapter12SourceProfile
  mixedEqIffExtensionalEq :=
    @witnessEquivalentFeature_semanticLayerMixedEvidence_eq_iff_extensionalEvidence_eq_viaFormedConceptCalibration

/-- Formed-concept pair-subset transport drives typed semantic-layer ASSOC/PAT
evidence monotonicity.

The actual formed-concept source supplies the pair-subset relation; the layer
tag only chooses the existing ASSOC/PAT channel through the typed semantic gate. -/
theorem witnessFeature_semanticLayerAssocPatEvidence_mono_viaFormedConceptCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (layer : SemanticInheritanceLayer)
    (hLayer :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
        layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code :
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
            witnessImpliesFeatureMemberEvidence).meaning p).intent)
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
      ∧
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) := by
  have hRel :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) :=
    witnessFeature_pairSubsetRel_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal W
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerAssocPatEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      layer hLayer M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hRel

/-- Proof-carrying profile for the formed-concept ASSOC/PAT semantic-layer
monotonicity theorem.

The source is the actual Chapter-12 formed-concept pair-subset canary. The
consumer theorem routes it through the existing typed semantic-layer gate, so
the layer must be intensional-facing and the ASSOC/PAT score channels must be
the nonnegatively weighted finite-vocabulary scores. This packages an existing
theorem; it does not introduce a parallel ASSOC/PAT semantics. -/
structure FormedConceptSemanticLayerAssocPatMonotonicityProfile where
  source :
    FormedConceptChapter12SourceProfile
  assocPatMonoOfIntensionalFacing :
    ∀ {Base : Type u} {Const : Ty Base → Type v}
      {State Pred PairQuery : Type}
      [EvidenceType State]
      [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
      (layer : SemanticInheritanceLayer)
      (_hLayer :
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerIntensionalFacing
          layer)
      (M : HenkinModel.{u, v, w} Base Const)
      (σ : Ty Base)
      [Fintype Pred]
      (code :
        Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence → Pred)
      (decode : Pred →
        Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
          (Base := Base) (Const := Const) σ)
      (attrOf : Pred → MembershipConcept)
      (_hCal : ∀
        {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence} {r : Pred},
        r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
          attrOf r ∈
            ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
              Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
              witnessImpliesFeatureMemberEvidence).meaning p).intent)
      (pairEnc : InheritanceQueryBuilder Pred PairQuery)
      (model : InheritanceQueryBuilder.IntensionalScoreModel
        (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
      {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
      (_hAssocLeftWeight : 0 ≤ assocLeftWeight)
      (_hAssocRightWeight : 0 ≤ assocRightWeight)
      (_hPatLeftWeight : 0 ≤ patLeftWeight)
      (_hPatRightWeight : 0 ≤ patRightWeight)
      (_hAssocScore : ∀ (W : State) (a b : Pred),
        model.assocScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            assocLeftWeight assocRightWeight a b)
      (_hPatScore : ∀ (W : State) (a b : Pred),
        model.patScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            patLeftWeight patRightWeight a b)
      {W : State},
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .assoc W pairEnc
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        ∧
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            layer .pat W pairEnc
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))

/-- Concrete formed-concept ASSOC/PAT semantic-layer monotonicity package. -/
noncomputable def formedConceptSemanticLayerAssocPatMonotonicityProfile :
    FormedConceptSemanticLayerAssocPatMonotonicityProfile where
  source :=
    formedConceptChapter12SourceProfile
  assocPatMonoOfIntensionalFacing :=
    @witnessFeature_semanticLayerAssocPatEvidence_mono_viaFormedConceptCalibration

/-- Formed-concept pair-subset transport drives mixed semantic-layer evidence
monotonicity, provided the extensional channel and the mixed combiner are
monotone too.

This is the formed-source consumer of the typed mixed monotonicity guardrail:
the actual formed-concept source supplies the ASSOC/PAT pair-subset flow, while
mixed evidence remains explicitly dependent on extensional evidence and the
combiner policy. -/
theorem witnessFeature_semanticLayerMixedEvidence_mono_viaFormedConceptCalibration
    {State Pred PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype Pred]
    (code :
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence → Pred)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → MembershipConcept)
    (hCal : ∀
      {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
        Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
        witnessImpliesFeatureMemberEvidence} {r : Pred},
      r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈
          ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
            Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
            witnessImpliesFeatureMemberEvidence).meaning p).intent)
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
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    (hCombineMono :
      ∀ {e₁ e₂ a₁ a₂ p₁ p₂ :
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
        e₁ ≤ e₂ → a₁ ≤ a₂ → p₁ ≤ p₂ →
          m.combine e₁ a₁ p₁ ≤ m.combine e₂ a₂ p₂)
    {W : State}
    (hExt :
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) := by
  have hRel :
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
        (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) :=
    witnessFeature_pairSubsetRel_transports_to_predicateVocabulary_viaFormedConceptCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal W
  exact
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.semanticLayerMixedEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc m
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hCombineMono hExt hRel

/-- Proof-carrying profile for the formed-concept mixed semantic-layer
monotonicity theorem.

The source is still the actual Chapter-12 formed-concept pair-subset canary.
The consumer theorem records the honest mixed-channel side conditions:
extensional evidence must be monotone, and the mixed combiner must be monotone
in all three evidence inputs. This packages an existing theorem; it does not
introduce a new mixed semantics or a numeric-tightness claim. -/
structure FormedConceptMixedSemanticLayerMonotonicityProfile where
  source :
    FormedConceptChapter12SourceProfile
  mixedMonoOfExtensionalAndCombinerMono :
    ∀ {Base : Type u} {Const : Ty Base → Type v}
      {State Pred PairQuery : Type}
      [EvidenceType State]
      [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
      (M : HenkinModel.{u, v, w} Base Const)
      (σ : Ty Base)
      [Fintype Pred]
      (code :
        Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence → Pred)
      (decode : Pred →
        Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
          (Base := Base) (Const := Const) σ)
      (attrOf : Pred → MembershipConcept)
      (_hCal : ∀
        {p : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept
          Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
          witnessImpliesFeatureMemberEvidence} {r : Pred},
        r ∈ ((Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
          attrOf r ∈
            ((Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation
              Mettapedia.KR.ConceptOntology.EvidenceGate.positiveSupport
              witnessImpliesFeatureMemberEvidence).meaning p).intent)
      (pairEnc : InheritanceQueryBuilder Pred PairQuery)
      (m : InheritanceQueryBuilder.AssocPatSemanticModel
        (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
      {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
      (_hAssocLeftWeight : 0 ≤ assocLeftWeight)
      (_hAssocRightWeight : 0 ≤ assocRightWeight)
      (_hPatLeftWeight : 0 ≤ patLeftWeight)
      (_hPatRightWeight : 0 ≤ patRightWeight)
      (_hAssocScore : ∀ (W : State) (a b : Pred),
        m.scoreModel.assocScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            assocLeftWeight assocRightWeight a b)
      (_hPatScore : ∀ (W : State) (a b : Pred),
        m.scoreModel.patScore W a b =
          Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
            (Base := Base) (Const := Const) M σ decode
            patLeftWeight patRightWeight a b)
      (_hCombineMono :
        ∀ {e₁ e₂ a₁ a₂ p₁ p₂ :
            Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
          e₁ ≤ e₂ → a₁ ≤ a₂ → p₁ ≤ p₂ →
            m.combine e₁ a₁ p₁ ≤ m.combine e₂ a₂ p₂)
      {W : State}
      (_hExt :
        InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            .extensional .assoc W pairEnc
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
          InheritanceQueryBuilder.semanticLayerEvidence
            (State := State) (Atom := Pred) (Query := PairQuery)
            .extensional .assoc W pairEnc
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
            (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))),
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .mixed .assoc W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature)) ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .mixed .assoc W pairEnc
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.witness))
          (code (witnessImpliesFeatureFormedConcept MembershipConcept.feature))

/-- Concrete formed-concept mixed semantic-layer monotonicity package. -/
noncomputable def formedConceptMixedSemanticLayerMonotonicityProfile :
    FormedConceptMixedSemanticLayerMonotonicityProfile where
  source :=
    formedConceptChapter12SourceProfile
  mixedMonoOfExtensionalAndCombinerMono :=
    @witnessFeature_semanticLayerMixedEvidence_mono_viaFormedConceptCalibration

end Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge
