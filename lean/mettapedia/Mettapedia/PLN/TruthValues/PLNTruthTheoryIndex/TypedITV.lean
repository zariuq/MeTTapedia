import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.ConfidenceCoordinates

namespace Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

open Mettapedia.PLN.WorldModel

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.Algebra.TwoDimClassification
open scoped ENNReal

universe u v


/-! ## Typed ITV constructor provenance -/

/-- Raw ITV fields are not constructor provenance: the same displayed interval
can be carried under different typed semantics. -/
theorem raw_itv_fields_do_not_identify_constructor_provenance :
    let raw := ITV.fullWidthWithCredibility 0 (by norm_num)
    let generic : TypedITV genericITVSemantics := TypedITV.fromGeneric raw
    let walley : TypedITV (walleyBinaryITVSemantics 1) :=
      TypedITV.fromWalleyBinary 1 (by norm_num)
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.zero
    generic.lower = walley.lower ∧
      generic.upper = walley.upper ∧
        generic.credibility = walley.credibility :=
  TypedITV.generic_and_walley_zero_can_share_raw_fields

/-- The typed Walley binary constructor carries the width-complement law. -/
theorem typed_walley_binary_has_width_complement
    (s : ℝ) (hs : 0 < s)
    (e : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence) :
    (TypedITV.fromWalleyBinary s hs e).width +
      (TypedITV.fromWalleyBinary s hs e).credibility = 1 :=
  TypedITV.walleyBinary_width_add_credibility s hs e

/-- The typed Bayesian credible constructor keeps credibility tied to evidence
concentration at the fixed prior context. -/
theorem typed_bayes_credible_credibility_is_evidence_concentration
    (backend : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.CredibleIntervalBackend)
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1)
    (e : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence) :
    (TypedITV.fromBayesCredible backend ctx level hlevel e).credibility =
      (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toConfidence
        (ctx.α₀ + ctx.β₀) e).toReal :=
  TypedITV.bayesCredible_credibility_eq backend ctx level hlevel e

/-- The typed Walley categorical constructor carries the same
width-complement law as the binary IDM slice. -/
theorem typed_walley_categorical_has_width_complement
    {k : ℕ} (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (TypedITV.fromWalleyCategorical ctx e i).width +
      (TypedITV.fromWalleyCategorical ctx e i).credibility = 1 :=
  TypedITV.walleyCategorical_width_add_credibility ctx e i

/-- The typed Walley categorical constructor's credibility is the IDM
precision proxy determined by total categorical evidence and IDM strength. -/
theorem typed_walley_categorical_credibility_is_idm_precision
    {k : ℕ} (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (TypedITV.fromWalleyCategorical ctx e i).credibility =
      (e.total : ℝ) /
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmDenom ctx e :=
  TypedITV.walleyCategorical_credibility_eq ctx e i

/-- In a nondegenerate categorical carrier, the typed Walley categorical ITV
width is exactly the credal-set lower/upper envelope width for the queried
category. -/
theorem typed_walley_categorical_width_matches_credal_envelope
    {k : ℕ} (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    (TypedITV.fromWalleyCategorical ctx e i).width =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i) -
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i) :=
  TypedITV.walleyCategorical_width_eq_credal_width_of_other ctx e i j hji

/-! ## Typed ITV operation compatibility -/

/-- Same-semantics typed conjunction is available without discarding
provenance, but its result has derived-operation provenance rather than
pretending to be a fresh value of the original constructor semantics. -/
theorem typed_itv_same_semantics_conjunction_raw_value
    {Sem : ITVSemantics} (x y : TypedITV Sem) :
    (TypedITV.conjunctionSameSemantics x y).value =
      ITV.conjunction x.value y.value :=
  TypedITV.value_conjunctionSameSemantics x y

/-- Same-semantics typed implication is also a derived-operation value, not a
silent reuse of the input constructor semantics. -/
theorem typed_itv_same_semantics_implication_raw_value
    {Sem : ITVSemantics} (x y : TypedITV Sem) :
    (TypedITV.implicationSameSemantics x y).value =
      ITV.implication x.value y.value :=
  TypedITV.value_implicationSameSemantics x y

/-- Forgetting into the generic raw-ITV semantics preserves displayed fields,
but it is an explicit operation so constructor provenance is not silently
mixed. -/
theorem typed_itv_forget_to_generic_preserves_raw_value
    {Sem : ITVSemantics} (x : TypedITV Sem) :
    (TypedITV.forgetToGeneric x).value = x.value :=
  TypedITV.value_forgetToGeneric x

/-- Cross-semantics conjunction is routed through an explicit bridge to a
shared target semantics. -/
theorem typed_itv_cross_semantics_conjunction_via_bridge_raw_value
    {Sem₁ Sem₂ Target : ITVSemantics}
    (B : TypedITV.Bridge Sem₁ Sem₂ Target)
    (x : TypedITV Sem₁) (y : TypedITV Sem₂) :
    (TypedITV.conjunctionViaBridge B x y).value =
      ITV.conjunction (B.left x).value (B.right y).value :=
  TypedITV.value_conjunctionViaBridge B x y

/-! ## Forced categorical queries -/

/-- Categorical query means are forced by the retained aggregate
`MultiEvidence`. -/
theorem categorical_query_mean_is_forced_by_aggregate
    {Obs Query : Type*} {k : ℕ}
    (S :
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface Obs Query
        (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k))
    {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k)
    (h :
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q) :
    ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q).counts i : ℝ) /
        ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q).total : ℝ) =
      ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q).counts i : ℝ) /
        ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q).total : ℝ) :=
  categoricalSurface_queryMean_forced_by_aggregate S i h

/-- Categorical IDM interval endpoints and width are forced by the retained
aggregate `MultiEvidence`, once the IDM context and category are chosen. -/
theorem categorical_idm_envelope_is_forced_by_aggregate
    {Obs Query : Type*} {k : ℕ}
    (S :
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface Obs Query
        (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k))
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
    {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k)
    (h :
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q) :
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmLower ctx
        (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) i =
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmLower ctx
          (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q) i ∧
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmUpper ctx
        (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) i =
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmUpper ctx
          (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q) i ∧
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmWidth ctx
        (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmWidth ctx
          (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q) :=
  categoricalSurface_idmEnvelope_forced_by_aggregate S ctx i h

/-! ## Sufficient-statistic strength and confidence queries -/

/-- Strength and confidence are views forced by retained evidence.  The
confidence scale, IDM context, and queried category are chosen parameters of
the view; once chosen, equal retained evidence forces equal answers. -/
structure SufficientStatisticQueryProfile where
  binaryWorldStrengthForced :
    ∀ {State Query : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      {W₁ W₂ : State} {q : Query},
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₁ q =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₂ q →
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryStrength
            (State := State) (Query := Query) W₁ q =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryStrength
            (State := State) (Query := Query) W₂ q
  binaryWorldConfidenceForced :
    ∀ {State Query : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel State Query]
      (κ : ℝ≥0∞) {W₁ W₂ : State} {q : Query},
      Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₁ q =
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₂ q →
        Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryConfidence
            (State := State) (Query := Query) κ W₁ q =
          Mettapedia.PLN.WorldModel.PLNWorldModel.BinaryWorldModel.queryConfidence
            (State := State) (Query := Query) κ W₂ q
  binarySurfaceStrengthForced :
    ∀ {Obs Query : Type}
      (S :
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface Obs Query
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
      {σ₁ σ₂ : Multiset Obs} {q : Query},
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q →
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength
            (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) =
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength
            (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q)
  binarySurfaceConfidenceForced :
    ∀ {Obs Query : Type}
      (S :
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface Obs Query
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
      (κ : ℝ≥0∞) {σ₁ σ₂ : Multiset Obs} {q : Query},
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q →
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toConfidence κ
            (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) =
          Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toConfidence κ
            (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q)
  categoricalMeanForced :
    ∀ {Obs Query : Type} {k : ℕ}
      (S :
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface Obs Query
          (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k))
      {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k),
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q →
        ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q).counts i : ℝ) /
            ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q).total : ℝ) =
          ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q).counts i : ℝ) /
            ((Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q).total : ℝ)
  categoricalIDMEnvelopeForced :
    ∀ {Obs Query : Type} {k : ℕ}
      (S :
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface Obs Query
          (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k))
      (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
      {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k),
      Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q →
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmLower ctx
            (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) i =
            Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmLower ctx
              (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q) i ∧
          Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmUpper ctx
            (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) i =
              Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmUpper ctx
                (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q) i ∧
          Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmWidth ctx
            (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₁ q) =
              Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmWidth ctx
                (Mettapedia.PLN.WorldModel.SufficientStatisticSurface.aggregate S σ₂ q)

/-- Sufficient-statistic query profile for strength, confidence, categorical
means, and categorical IDM envelopes. -/
def sufficientStatisticQueryProfile : SufficientStatisticQueryProfile where
  binaryWorldStrengthForced := by
    intro State Query instEvidence instWM W₁ W₂ q h
    exact
      Mettapedia.PLN.TruthValues.PLNForcedQueries.queryStrength_eq_of_same_evidence h
  binaryWorldConfidenceForced := by
    intro State Query instEvidence instWM κ W₁ W₂ q h
    exact
      Mettapedia.PLN.TruthValues.PLNForcedQueries.queryConfidence_eq_of_same_evidence
        κ h
  binarySurfaceStrengthForced := by
    intro Obs Query S σ₁ σ₂ q h
    exact
      Mettapedia.PLN.TruthValues.PLNForcedQueries.binarySurface_strength_eq_of_same_aggregate
        S h
  binarySurfaceConfidenceForced := by
    intro Obs Query S κ σ₁ σ₂ q h
    exact
      Mettapedia.PLN.TruthValues.PLNForcedQueries.binarySurface_confidence_eq_of_same_aggregate
        S κ h
  categoricalMeanForced := by
    intro Obs Query k S σ₁ σ₂ q i h
    exact categorical_query_mean_is_forced_by_aggregate S i h
  categoricalIDMEnvelopeForced := by
    intro Obs Query k S ctx σ₁ σ₂ q i h
    exact categorical_idm_envelope_is_forced_by_aggregate S ctx i h

/-! ## Credal and lower-prevision forced queries -/

/-- Lower expectation is a forced projection of a retained credal set. -/
theorem credal_lower_expectation_is_forced_by_credal_set
    {World Ω : Type*} [Fintype Ω]
    (credal :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (credal W₁) f =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (credal W₂) f :=
  Mettapedia.PLN.TruthValues.PLNForcedQueries.credalLower_eq_of_same_credalSet
    credal f h

/-- Upper expectation is a forced projection of a retained credal set. -/
theorem credal_upper_expectation_is_forced_by_credal_set
    {World Ω : Type*} [Fintype Ω]
    (credal :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (credal W₁) f =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (credal W₂) f :=
  Mettapedia.PLN.TruthValues.PLNForcedQueries.credalUpper_eq_of_same_credalSet
    credal f h

/-- The full lower/upper envelope is a forced projection of a retained credal
set. -/
theorem credal_envelope_is_forced_by_credal_set
    {World Ω : Type*} [Fintype Ω]
    (credal :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (credal W₁) f,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (credal W₁) f) =
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (credal W₂) f,
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (credal W₂) f) :=
  Mettapedia.PLN.TruthValues.PLNForcedQueries.credalEnvelope_eq_of_same_credalSet
    credal f h

/-- A coherent lower-prevision value is forced by the retained lower
prevision. -/
theorem lower_prevision_value_is_forced_by_lower_prevision
    {World Ω : Type*}
    (prevision :
      World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    {W₁ W₂ : World} (h : prevision W₁ = prevision W₂) :
    prevision W₁ X = prevision W₂ X :=
  Mettapedia.PLN.TruthValues.PLNForcedQueries.lowerPrevisionValue_eq_of_same_lowerPrevision
    prevision X h

/-- The conjugate upper-prevision value is also forced by the retained lower
prevision. -/
theorem upper_prevision_value_is_forced_by_lower_prevision
    {World Ω : Type*}
    (prevision :
      World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    {W₁ W₂ : World} (h : prevision W₁ = prevision W₂) :
    (prevision W₁).conjugate X = (prevision W₂).conjugate X :=
  Mettapedia.PLN.TruthValues.PLNForcedQueries.upperPrevisionValue_eq_of_same_lowerPrevision
    prevision X h

/-- The lower prevision induced by a retained coherent desirable-gamble set is
a forced projection of that retained set. -/
theorem desirable_lower_prevision_is_forced_by_desirable_set
    {World Ω : Type*}
    (desirable :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : desirable W₁ = desirable W₂) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (desirable W₁) f =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (desirable W₂) f :=
  Mettapedia.PLN.TruthValues.PLNForcedQueries.desirableLowerPrevision_eq_of_same_desirableSet
    desirable f h

/-! ## Credal envelopes as typed ITV views -/

/-- A finite credal-set envelope typed as an ITV has lower endpoint forced by
the retained credal set and queried gamble. -/
theorem credal_envelope_typed_itv_lower_forced
    {Ω : Type*} [Fintype Ω]
    (src : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalEnvelopeITVSource Ω) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope src).lower =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        src.credal src.gamble :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope_lower src

/-- A finite credal-set envelope typed as an ITV has upper endpoint forced by
the retained credal set and queried gamble. -/
theorem credal_envelope_typed_itv_upper_forced
    {Ω : Type*} [Fintype Ω]
    (src : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalEnvelopeITVSource Ω) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope src).upper =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        src.credal src.gamble :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope_upper src

/-- The typed credal-envelope ITV records the selected credibility coordinate
explicitly rather than deriving it from the lower/upper envelope. -/
theorem credal_envelope_typed_itv_credibility_is_selected
    {Ω : Type*} [Fintype Ω]
    (src : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalEnvelopeITVSource Ω) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope src).credibility =
      src.credibility :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope_credibility src

/-- Credal lower/upper endpoints do not force the credibility coordinate. -/
theorem credal_envelope_bounds_do_not_force_confidence_coordinate
    {Ω : Type*} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    let x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
        { credal := K
          gamble := f
          credal_nonempty := hK
          gamble_in_unit := hf
          credibility := 0
          credibility_in_unit := by norm_num }
    let y : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
        { credal := K
          gamble := f
          credal_nonempty := hK
          gamble_in_unit := hf
          credibility := 1
          credibility_in_unit := by norm_num }
    x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelope_bounds_do_not_force_credibility K hK f hf

/-! ## Abstract lower-prevision envelopes as typed ITV views -/

/-- A lower-prevision envelope typed as an ITV has lower endpoint forced by
the retained lower prevision and queried gamble. -/
theorem lower_prevision_typed_itv_lower_forced
    {Ω : Type*}
    (src : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionITVSource Ω) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision src).lower =
      src.prevision src.gamble :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision_lower src

/-- A lower-prevision envelope typed as an ITV has upper endpoint forced by
the conjugate upper prevision and queried gamble. -/
theorem lower_prevision_typed_itv_upper_forced
    {Ω : Type*}
    (src : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionITVSource Ω) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision src).upper =
      src.prevision.conjugate src.gamble :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision_upper src

/-- The typed lower-prevision ITV records the selected credibility coordinate
explicitly rather than deriving it from the lower/upper envelope. -/
theorem lower_prevision_typed_itv_credibility_is_selected
    {Ω : Type*}
    (src : Mettapedia.PLN.TruthValues.PLNTruthTower.LowerPrevisionITVSource Ω) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision src).credibility =
      src.credibility :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision_credibility src

/-- Abstract lower-prevision lower/upper endpoints do not force the credibility
coordinate. -/
theorem lower_prevision_bounds_do_not_force_confidence_coordinate
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    let x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
        { prevision := P
          gamble := X
          gamble_in_unit := hX
          credibility := 0
          credibility_in_unit := by norm_num }
    let y : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
        { prevision := P
          gamble := X
          gamble_in_unit := hX
          credibility := 1
          credibility_in_unit := by norm_num }
    x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevision_bounds_do_not_force_credibility
    P X hX

/-- Singleton finite credal envelopes agree with the precise lower-prevision
ITV induced by the singleton probability distribution. -/
theorem singleton_credal_lower_prevision_itv_agrees
    {Ω : Type*} [Fintype Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let lp : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
        (Mettapedia.PLN.TruthValues.PLNTruthTower.SingletonCredalLowerPrevision.source
          P X hX credibility hc);
    let ce : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
        (Mettapedia.PLN.TruthValues.PLNTruthTower.SingletonCredalLowerPrevision.credalEnvelopeSource
          P X hX credibility hc);
    lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
      lp.credibility = ce.credibility :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.SingletonCredalLowerPrevision.typedLowerPrevision_agrees_with_singletonCredalEnvelope
    P X hX credibility hc

/-- Finite credal envelopes agree with the lower-prevision ITV induced by the
finite credal lower envelope. -/
theorem finite_credal_lower_prevision_itv_agrees
    {Ω : Type*} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let lp : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromLowerPrevision
        (Mettapedia.PLN.TruthValues.PLNTruthTower.FiniteCredalLowerPrevision.source
          K hK X hX credibility hc);
    let ce : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
        (Mettapedia.PLN.TruthValues.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.fromCredalEnvelope
        { credal := K
          gamble := X
          credal_nonempty := hK
          gamble_in_unit := hX
          credibility := credibility
          credibility_in_unit := hc };
    lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
      lp.credibility = ce.credibility :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.FiniteCredalLowerPrevision.typedLowerPrevision_agrees_with_credalEnvelope
    K hK X hX credibility hc

/-! ## Credal projection tower: forced envelope plus selected confidence -/

/-- In the credal projection tower, lower is forced by the retained credal set
and queried gamble. -/
theorem credal_projection_tower_lower_forced
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.lower =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        t.credal t.gamble :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.lower_toTypedITV t

/-- In the credal projection tower, upper is forced by the retained credal set
and queried gamble. -/
theorem credal_projection_tower_upper_forced
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.upper =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        t.credal t.gamble :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.upper_toTypedITV t

/-- In the credal projection tower, displayed credibility is selected by the
chosen evidence-weight coordinate and evidence weight. -/
theorem credal_projection_tower_credibility_selected
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.credibility = t.coordinate.encode t.weight :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.credibility_toTypedITV t

/-- The tower's typed confidence decodes back to the selected evidence weight. -/
theorem credal_projection_tower_confidence_decodes_weight
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω) :
    t.typedConfidence.weight = t.weight :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.typedConfidence_weight t

/-- The width-complement bridge, when explicitly assumed, forces the selected
display to be the complement of credal width. -/
theorem credal_projection_width_complement_bridge_forces_display
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω)
    (h : t.WidthComplementBridge) :
    t.credibilityDisplay = 1 - t.toTypedITV.width :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.widthComplementBridge_forces_display t h

/-- Same credal envelope and same evidence weight can still display different
credibilities when the coordinate choice differs. -/
theorem credal_projection_same_weight_can_display_different_confidence
    {Ω : Type*} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K
        credal_nonempty := hK
        gamble := f
        gamble_in_unit := hf
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K
        credal_nonempty := hK
        gamble := f
        gamble_in_unit := hf
        coordinate := reserveHalfCoordinate 1 (by norm_num)
        coordinate_unit := reserveHalfCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    x.toTypedITV.lower = y.toTypedITV.lower ∧
      x.toTypedITV.upper = y.toTypedITV.upper ∧
      x.toTypedITV.credibility ≠ y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.same_weight_can_display_different_credibility
    K hK f hf

/-- Same coordinate and same evidence weight force the same displayed
credibility, independently of the retained credal envelope. -/
theorem credal_projection_same_coordinate_weight_forces_same_confidence
    {Ω : Type*} [Fintype Ω]
    (K₁ K₂ :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
    (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
    (w : ℝ) (hw : 0 ≤ w) :
    let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K₁
        credal_nonempty := hK₁
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K₂
        credal_nonempty := hK₂
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.same_coordinate_weight_forces_same_confidence
    K₁ K₂ hK₁ hK₂ f hf χ hχ w hw

/-- Same coordinate and same evidence weight can coexist with a different credal
envelope; a changed lower envelope leaves displayed confidence untouched. -/
theorem credal_projection_same_confidence_can_have_different_envelope
    {Ω : Type*} [Fintype Ω]
    (K₁ K₂ :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
    (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
    (w : ℝ) (hw : 0 ≤ w)
    (hLower :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₁ f ≠
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₂ f) :
    let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K₁
        credal_nonempty := hK₁
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K₂
        credal_nonempty := hK₂
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight ∧
        x.toTypedITV.lower ≠ y.toTypedITV.lower :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.same_confidence_can_have_different_credal_envelope
    K₁ K₂ hK₁ hK₂ f hf χ hχ w hw hLower

/-- Concrete Bool witness for the projection tower: same confidence coordinate
and evidence weight, but different lower credal envelopes. -/
theorem credal_projection_bool_same_confidence_different_envelope :
    let x : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolFalseProbDist
        credal_nonempty :=
          ⟨Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolFalseProbDist, rfl⟩
        gamble :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTrueProbDist
        credal_nonempty :=
          ⟨Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTrueProbDist, rfl⟩
        gamble :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight ∧
      x.toTypedITV.lower = 0 ∧
      y.toTypedITV.lower = 1 ∧
      x.toTypedITV.lower ≠ y.toTypedITV.lower :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.concreteBool_same_confidence_different_credal_envelope


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
