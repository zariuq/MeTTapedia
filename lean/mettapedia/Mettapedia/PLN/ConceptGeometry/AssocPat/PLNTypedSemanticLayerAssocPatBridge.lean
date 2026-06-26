import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNTypedSemanticLayerBridge
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge

/-!
# Typed Semantic-Layer Consumers for ASSOC/PAT

This module connects the semantic-layer gate to the existing finite-vocabulary
ASSOC/PAT bridge.  The layer tag chooses a channel; all score semantics and
same-intent reasoning remain the ones already provided by
`PLNHigherOrderHOLAssocPatBridge`.
-/

namespace Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge

open Mettapedia.Logic.HOL
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
variable {State Pred PairQuery : Type}
variable [EvidenceType State]
variable [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]

/-- A semantic layer is intensional-facing when it selects either ASSOC or PAT
rather than the extensional or mixed channel. -/
def semanticLayerIntensionalFacing
    (layer : SemanticInheritanceLayer) : Prop :=
  layer = .preextensional ∨ layer = .intensional

/-- ASSOC-channel semantic-layer evidence is invariant under same-intent
replacement for weighted finite-vocabulary predicate-pair scores.

The theorem is intentionally stated only for intensional-facing layer tags:
same intent controls ASSOC/PAT evidence, not the extensional channel. -/
theorem semanticLayerAssocEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (layer : SemanticInheritanceLayer)
    (hLayer : semanticLayerIntensionalFacing layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc a b =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc c d := by
  have hAssoc :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    assocEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model
      hLeftWeight hRightWeight hScore hLeft hRight
  rcases hLayer with rfl | rfl <;> simpa using hAssoc

/-- PAT-channel semantic-layer evidence is invariant under same-intent
replacement for weighted finite-vocabulary predicate-pair scores. -/
theorem semanticLayerPATEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (layer : SemanticInheritanceLayer)
    (hLayer : semanticLayerIntensionalFacing layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc a b =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc c d := by
  have hPat :
      InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    patEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model
      hLeftWeight hRightWeight hScore hLeft hRight
  rcases hLayer with rfl | rfl <;> simpa using hPat

/-- Combined semantic-layer ASSOC/PAT invariance for an intensional-facing
layer tag.  This is the typed-gate form of the existing two-channel
same-intent theorem. -/
theorem semanticLayerAssocPatEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (layer : SemanticInheritanceLayer)
    (hLayer : semanticLayerIntensionalFacing layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
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
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc a b =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc c d ∧
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc a b =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc c d := by
  exact
    ⟨semanticLayerAssocEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
        layer hLayer M σ decode pairEnc model
        hAssocLeftWeight hAssocRightWeight hAssocScore hLeft hRight,
      semanticLayerPATEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
        layer hLayer M σ decode pairEnc model
        hPatLeftWeight hPatRightWeight hPatScore hLeft hRight⟩

/-- ASSOC-channel semantic-layer evidence is monotone for nonnegatively
weighted finite-vocabulary predicate-pair scores.

This is the typed-gate lift of the existing Chapter-12 pair-subset
monotonicity theorem.  The semantic layer only selects the ASSOC channel; the
score semantics and pair-subset relation remain the finite HO predicate
vocabulary machinery from `PLNHigherOrderHOLAssocPatBridge`. -/
theorem semanticLayerAssocEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
    (layer : SemanticInheritanceLayer)
    (hLayer : semanticLayerIntensionalFacing layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b)
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc a b ≤
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc c d := by
  have hAssoc :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    assocEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (assocSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hLeftWeight hRightWeight hScore)
      hRel
  rcases hLayer with rfl | rfl <;> simpa using hAssoc

/-- PAT-channel semantic-layer evidence is monotone for nonnegatively weighted
finite-vocabulary predicate-pair scores. -/
theorem semanticLayerPATEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
    (layer : SemanticInheritanceLayer)
    (hLayer : semanticLayerIntensionalFacing layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b)
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc a b ≤
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc c d := by
  have hPat :
      InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    patEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (patSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hLeftWeight hRightWeight hScore)
      hRel
  rcases hLayer with rfl | rfl <;> simpa using hPat

/-- Two-channel typed semantic-layer ASSOC/PAT monotonicity for a finite HO
predicate-vocabulary pair-subset relation. -/
theorem semanticLayerAssocPatEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
    (layer : SemanticInheritanceLayer)
    (hLayer : semanticLayerIntensionalFacing layer)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
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
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .assoc W pairEnc a b ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .assoc W pairEnc c d ∧
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        layer .pat W pairEnc a b ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          layer .pat W pairEnc c d := by
  exact
    ⟨semanticLayerAssocEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
        layer hLayer M σ decode pairEnc model
        hAssocLeftWeight hAssocRightWeight hAssocScore hRel,
      semanticLayerPATEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
        layer hLayer M σ decode pairEnc model
        hPatLeftWeight hPatRightWeight hPatScore hRel⟩

/-- Mixed semantic-layer evidence is monotone for a weighted finite-vocabulary
predicate-pair source only when the extensional channel is monotone too and the
mixed combiner is monotone in all three channels.

This is the order-theoretic counterpart to the mixed same-intent equality
guardrail below.  ASSOC/PAT pair-subset evidence alone is not enough to move a
mixed channel; the theorem keeps the extensional contribution and combiner
policy explicit. -/
theorem semanticLayerMixedEvidence_mono_of_predicateVocabularyWeightedPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
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
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    (hCombineMono :
      ∀ {e₁ e₂ a₁ a₂ p₁ p₂ :
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
        e₁ ≤ e₂ → a₁ ≤ a₂ → p₁ ≤ p₂ →
          m.combine e₁ a₁ p₁ ≤ m.combine e₂ a₂ p₂)
    {W : State} {a b c d : Pred}
    (hExt :
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc a b ≤
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc c d)
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc a b ≤
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc c d := by
  have hExt' :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
    simpa using hExt
  have hAssoc :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    assocEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc m.scoreModel
      (assocSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc m.scoreModel
        hAssocLeftWeight hAssocRightWeight hAssocScore)
      hRel
  have hPat :
      InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    patEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc m.scoreModel
      (patSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc m.scoreModel
        hPatLeftWeight hPatRightWeight hPatScore)
      hRel
  have hAssocLift :
      m.scoreModel.scoreToEvidence (m.scoreModel.assocScore W a b) ≤
        m.scoreModel.scoreToEvidence (m.scoreModel.assocScore W c d) := by
    calc
      m.scoreModel.scoreToEvidence (m.scoreModel.assocScore W a b)
          = InheritanceQueryBuilder.intensionalAssocEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (m.scoreModel.assoc_sound W a b).symm
      _ ≤ InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hAssoc
      _ = m.scoreModel.scoreToEvidence (m.scoreModel.assocScore W c d) :=
        m.scoreModel.assoc_sound W c d
  have hPatLift :
      m.scoreModel.scoreToEvidence (m.scoreModel.patScore W a b) ≤
        m.scoreModel.scoreToEvidence (m.scoreModel.patScore W c d) := by
    calc
      m.scoreModel.scoreToEvidence (m.scoreModel.patScore W a b)
          = InheritanceQueryBuilder.intensionalPATEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (m.scoreModel.pat_sound W a b).symm
      _ ≤ InheritanceQueryBuilder.intensionalPATEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hPat
      _ = m.scoreModel.scoreToEvidence (m.scoreModel.patScore W c d) :=
        m.scoreModel.pat_sound W c d
  calc
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc a b
        = m.combine
            (InheritanceQueryBuilder.extensionalEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b)
            (m.scoreModel.scoreToEvidence (m.scoreModel.assocScore W a b))
            (m.scoreModel.scoreToEvidence (m.scoreModel.patScore W a b)) := by
      simpa using m.mixed_sound W a b
    _ ≤ m.combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
          (m.scoreModel.scoreToEvidence (m.scoreModel.assocScore W c d))
          (m.scoreModel.scoreToEvidence (m.scoreModel.patScore W c d)) :=
      hCombineMono hExt' hAssocLift hPatLift
    _ = InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .mixed .assoc W pairEnc c d := by
      simpa using (m.mixed_sound W c d).symm

/-- Mixed semantic-layer evidence is preserved by same-intent replacement only
when the extensional layer is also preserved.

This is the typed-gate version of the Chapter-12 guardrail: ASSOC/PAT are
intensional channels, while mixed evidence additionally depends on the
extensional channel. -/
theorem semanticLayerMixedEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
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
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} {a b c d : Pred}
    (hExt :
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc a b =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .extensional .assoc W pairEnc c d)
    (hLeft :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc a b =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc c d := by
  have hExt' :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
    simpa using hExt
  have hMixed :
      InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    mixedEvidence_eq_of_assocPatSemanticModel_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc m
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hExt' hLeft hRight
  simpa using hMixed

/-- If the typed mixed semantic layer is equal under same-intent replacement
and the mixed combiner is left-cancellable, then the typed extensional layer
was equal too.

This is the typed semantic-layer form of the weighted three-channel guardrail:
same intent fixes ASSOC/PAT, but a mixed-channel equality can only recover the
extensional channel through the mixed evidence itself. -/
theorem semanticLayerExtensionalEvidence_eq_of_mixedEvidence_eq_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
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
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    (hCancel :
      ∀ {x y assoc pat :
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
        m.combine x assoc pat = m.combine y assoc pat → x = y)
    {W : State} {a b c d : Pred}
    (hMixedEq :
      InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .mixed .assoc W pairEnc a b =
        InheritanceQueryBuilder.semanticLayerEvidence
          (State := State) (Atom := Pred) (Query := PairQuery)
          .mixed .assoc W pairEnc c d)
    (hLeft :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .extensional .assoc W pairEnc a b =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .extensional .assoc W pairEnc c d := by
  have hMixedEq' :
      InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
    simpa using hMixedEq
  have hExt :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    extensionalEvidence_eq_of_mixedEvidence_eq_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
      M σ decode pairEnc m.scoreModel m.combine m.mixed_sound
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hCancel hMixedEq' hLeft hRight
  simpa using hExt

/-- Typed semantic-layer version of the weighted three-channel separation
theorem: under same-intent weighted ASSOC/PAT correspondences and a
left-cancellable mixed combiner, equality of the mixed layer is equivalent to
equality of the extensional layer. -/
theorem semanticLayerMixedEvidence_eq_iff_extensionalEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
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
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    (hCancel :
      ∀ {x y assoc pat :
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
        m.combine x assoc pat = m.combine y assoc pat → x = y)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc a b =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .mixed .assoc W pairEnc c d ↔
    InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .extensional .assoc W pairEnc a b =
      InheritanceQueryBuilder.semanticLayerEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        .extensional .assoc W pairEnc c d := by
  constructor
  · intro hMixedEq
    exact
      semanticLayerExtensionalEvidence_eq_of_mixedEvidence_eq_predicateVocabularyWeightedPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
        M σ decode pairEnc m
        hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
        hAssocScore hPatScore hCancel hMixedEq hLeft hRight
  · intro hExt
    exact
      semanticLayerMixedEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
        M σ decode pairEnc m
        hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
        hAssocScore hPatScore hExt hLeft hRight

end Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge
