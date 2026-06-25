import Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
import Mettapedia.PLN.WorldModel.SufficientStatisticSurface
import Mettapedia.ProbabilityTheory.ImpreciseProbability.Basic
import Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-!
# Forced Queries and Chosen ITV Projections

This module isolates a small but important boundary in the PLN truth-value
stack:

* a query is forced by a statistic when it factors through that statistic;
* an interval projection is a chosen selector unless a constructor supplies an
  extra law that makes it canonical.

The point is deliberately modest.  It provides a reusable theorem interface for
"same statistic, same answer" and canaries showing that generic indefinite
truth values do not choose lower, midpoint, or upper by themselves.
-/

namespace Mettapedia.PLN.TruthValues.PLNForcedQueries

open scoped ENNReal

open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelAdditive

/-! ## Factoring through a statistic -/

/-- A value projection is forced by a statistic when evaluation factors through
that statistic.  The statistic is the canonical data retained by the model; the
projection is a view of that data. -/
structure ForcedByStatistic (World Stat Val : Type*) where
  stat : World → Stat
  project : Stat → Val
  eval : World → Val
  eval_eq_project_stat : ∀ W, eval W = project (stat W)

namespace ForcedByStatistic

variable {World Stat Val : Type*}

/-- If two worlds have the same retained statistic, every projection forced by
that statistic gives the same value. -/
theorem eval_eq_of_same_stat
    (F : ForcedByStatistic World Stat Val) {W₁ W₂ : World}
    (h : F.stat W₁ = F.stat W₂) :
    F.eval W₁ = F.eval W₂ := by
  calc
    F.eval W₁ = F.project (F.stat W₁) := F.eval_eq_project_stat W₁
    _ = F.project (F.stat W₂) := by rw [h]
    _ = F.eval W₂ := (F.eval_eq_project_stat W₂).symm

/-- The unbundled proposition that a map factors through a statistic. -/
def FactorsThrough (stat : World → Stat) (eval : World → Val) : Prop :=
  ∃ project : Stat → Val, ∀ W, eval W = project (stat W)

/-- The bundled interface implies the unbundled factorization proposition. -/
theorem factorsThrough (F : ForcedByStatistic World Stat Val) :
    FactorsThrough F.stat F.eval :=
  ⟨F.project, F.eval_eq_project_stat⟩

/-- The unbundled factorization proposition carries the same invariance:
worlds with the same statistic cannot be separated by the evaluation map. -/
theorem eval_eq_of_same_stat_of_factorsThrough
    {stat : World → Stat} {eval : World → Val}
    (hFactor : FactorsThrough stat eval) {W₁ W₂ : World}
    (hStat : stat W₁ = stat W₂) :
    eval W₁ = eval W₂ := by
  rcases hFactor with ⟨project, hEval⟩
  calc
    eval W₁ = project (stat W₁) := hEval W₁
    _ = project (stat W₂) := by rw [hStat]
    _ = eval W₂ := (hEval W₂).symm

end ForcedByStatistic

/-! ## World-model queries forced by extracted evidence -/

section BinaryWorldModel

variable {State Query Val : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Any projection of a binary world-model query is forced by the extracted
`BinaryEvidence` for that query. -/
noncomputable def binaryWorldModelProjectionForced
    (q : Query) (project : BinaryEvidence → Val) :
    ForcedByStatistic State BinaryEvidence Val where
  stat W := BinaryWorldModel.evidence (State := State) (Query := Query) W q
  project := project
  eval W := project (BinaryWorldModel.evidence (State := State) (Query := Query) W q)
  eval_eq_project_stat := by
    intro W
    rfl

/-- The usual strength view is forced by extracted binary evidence. -/
noncomputable def queryStrengthForcedByEvidence (q : Query) :
    ForcedByStatistic State BinaryEvidence ℝ≥0∞ :=
  binaryWorldModelProjectionForced
    (State := State) (Query := Query) q BinaryEvidence.toStrength

/-- The usual confidence view at fixed `κ` is forced by extracted binary
evidence.  The scale `κ` is part of the chosen view. -/
noncomputable def queryConfidenceForcedByEvidence (κ : ℝ≥0∞) (q : Query) :
    ForcedByStatistic State BinaryEvidence ℝ≥0∞ :=
  binaryWorldModelProjectionForced
    (State := State) (Query := Query) q (fun e => BinaryEvidence.toConfidence κ e)

/-- Equal extracted evidence forces equal query strengths. -/
theorem queryStrength_eq_of_same_evidence
    {W₁ W₂ : State} {q : Query}
    (h :
      BinaryWorldModel.evidence (State := State) (Query := Query) W₁ q =
        BinaryWorldModel.evidence (State := State) (Query := Query) W₂ q) :
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W₁ q =
      BinaryWorldModel.queryStrength (State := State) (Query := Query) W₂ q :=
  ForcedByStatistic.eval_eq_of_same_stat
    (queryStrengthForcedByEvidence (State := State) (Query := Query) q) h

/-- Equal extracted evidence forces equal query confidences at the same scale
`κ`. -/
theorem queryConfidence_eq_of_same_evidence
    (κ : ℝ≥0∞) {W₁ W₂ : State} {q : Query}
    (h :
      BinaryWorldModel.evidence (State := State) (Query := Query) W₁ q =
        BinaryWorldModel.evidence (State := State) (Query := Query) W₂ q) :
    BinaryWorldModel.queryConfidence (State := State) (Query := Query) κ W₁ q =
      BinaryWorldModel.queryConfidence (State := State) (Query := Query) κ W₂ q :=
  ForcedByStatistic.eval_eq_of_same_stat
    (queryConfidenceForcedByEvidence (State := State) (Query := Query) κ q) h

end BinaryWorldModel

/-! ## Credal and lower-prevision queries forced by imprecise models -/

section CredalSet

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

variable {World Ω : Type*} [Fintype Ω]

/-- A lower expectation query is forced by the retained credal set.  The
credal set is the imprecise-probability object; the lower endpoint is its
canonical infimum projection for the selected gamble. -/
noncomputable def credalLowerForcedByCredalSet
    (credal : World → CredalSetFinite Ω) (f : Gamble Ω) :
    ForcedByStatistic World (CredalSetFinite Ω) ℝ where
  stat := credal
  project := fun K => lowerProb K f
  eval := fun W => lowerProb (credal W) f
  eval_eq_project_stat := by
    intro W
    rfl

/-- An upper expectation query is forced by the retained credal set. -/
noncomputable def credalUpperForcedByCredalSet
    (credal : World → CredalSetFinite Ω) (f : Gamble Ω) :
    ForcedByStatistic World (CredalSetFinite Ω) ℝ where
  stat := credal
  project := fun K => upperProb K f
  eval := fun W => upperProb (credal W) f
  eval_eq_project_stat := by
    intro W
    rfl

/-- The whole lower/upper envelope is forced by the retained credal set. -/
noncomputable def credalEnvelopeForcedByCredalSet
    (credal : World → CredalSetFinite Ω) (f : Gamble Ω) :
    ForcedByStatistic World (CredalSetFinite Ω) (ℝ × ℝ) where
  stat := credal
  project := fun K => (lowerProb K f, upperProb K f)
  eval := fun W => (lowerProb (credal W) f, upperProb (credal W) f)
  eval_eq_project_stat := by
    intro W
    rfl

/-- Equal retained credal sets force equal lower expectations. -/
theorem credalLower_eq_of_same_credalSet
    (credal : World → CredalSetFinite Ω) (f : Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    lowerProb (credal W₁) f = lowerProb (credal W₂) f :=
  ForcedByStatistic.eval_eq_of_same_stat
    (credalLowerForcedByCredalSet credal f) h

/-- Equal retained credal sets force equal upper expectations. -/
theorem credalUpper_eq_of_same_credalSet
    (credal : World → CredalSetFinite Ω) (f : Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    upperProb (credal W₁) f = upperProb (credal W₂) f :=
  ForcedByStatistic.eval_eq_of_same_stat
    (credalUpperForcedByCredalSet credal f) h

/-- Equal retained credal sets force equal lower/upper envelopes. -/
theorem credalEnvelope_eq_of_same_credalSet
    (credal : World → CredalSetFinite Ω) (f : Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    (lowerProb (credal W₁) f, upperProb (credal W₁) f) =
      (lowerProb (credal W₂) f, upperProb (credal W₂) f) :=
  ForcedByStatistic.eval_eq_of_same_stat
    (credalEnvelopeForcedByCredalSet credal f) h

end CredalSet

section LowerPrevision

open Mettapedia.ProbabilityTheory.ImpreciseProbability

variable {World Ω : Type*}

/-- A lower-prevision query is forced by the retained coherent lower prevision. -/
noncomputable def lowerPrevisionValueForcedByLowerPrevision
    (prevision : World → LowerPrevision Ω) (X : Gamble Ω) :
    ForcedByStatistic World (LowerPrevision Ω) ℝ where
  stat := prevision
  project := fun P => P X
  eval := fun W => prevision W X
  eval_eq_project_stat := by
    intro W
    rfl

/-- A conjugate upper-prevision query is forced by the retained lower
prevision plus the selected gamble. -/
noncomputable def upperPrevisionValueForcedByLowerPrevision
    (prevision : World → LowerPrevision Ω) (X : Gamble Ω) :
    ForcedByStatistic World (LowerPrevision Ω) ℝ where
  stat := prevision
  project := fun P => P.conjugate X
  eval := fun W => (prevision W).conjugate X
  eval_eq_project_stat := by
    intro W
    rfl

/-- Equal retained lower previsions force equal lower-prevision values. -/
theorem lowerPrevisionValue_eq_of_same_lowerPrevision
    (prevision : World → LowerPrevision Ω) (X : Gamble Ω)
    {W₁ W₂ : World} (h : prevision W₁ = prevision W₂) :
    prevision W₁ X = prevision W₂ X :=
  ForcedByStatistic.eval_eq_of_same_stat
    (lowerPrevisionValueForcedByLowerPrevision prevision X) h

/-- Equal retained lower previsions force equal conjugate upper-prevision
values. -/
theorem upperPrevisionValue_eq_of_same_lowerPrevision
    (prevision : World → LowerPrevision Ω) (X : Gamble Ω)
    {W₁ W₂ : World} (h : prevision W₁ = prevision W₂) :
    (prevision W₁).conjugate X = (prevision W₂).conjugate X :=
  ForcedByStatistic.eval_eq_of_same_stat
    (upperPrevisionValueForcedByLowerPrevision prevision X) h

end LowerPrevision

section DesirableGambles

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

variable {World Ω : Type*}

/-- The lower prevision induced by a coherent desirable-gamble set is forced by
that retained desirable set.  This is the local formal version of the
"natural-extension object first, lower projection second" discipline; it does
not claim to formalize Walley's full natural-extension theorem. -/
noncomputable def desirableLowerPrevisionForcedByDesirableSet
    (desirable : World → CoherentDesirableSet Ω) (f : Gamble Ω) :
    ForcedByStatistic World (CoherentDesirableSet Ω) ℝ where
  stat := desirable
  project := fun C => lowerPrevision C f
  eval := fun W => lowerPrevision (desirable W) f
  eval_eq_project_stat := by
    intro W
    rfl

/-- Equal retained coherent desirable-gamble sets force equal induced lower
previsions for the same gamble. -/
theorem desirableLowerPrevision_eq_of_same_desirableSet
    (desirable : World → CoherentDesirableSet Ω) (f : Gamble Ω)
    {W₁ W₂ : World} (h : desirable W₁ = desirable W₂) :
    lowerPrevision (desirable W₁) f = lowerPrevision (desirable W₂) f :=
  ForcedByStatistic.eval_eq_of_same_stat
    (desirableLowerPrevisionForcedByDesirableSet desirable f) h

end DesirableGambles

/-! ## Sufficient-statistic queries forced by aggregate evidence -/

section SufficientStatistic

variable {Obs Query Ev Val : Type*}
variable [AddCommMonoid Ev]

/-- Any projection of a sufficient-statistic surface query is forced by the
canonical aggregate statistic for that query. -/
noncomputable def aggregateProjectionForced
    (S : SufficientStatisticSurface Obs Query Ev) (q : Query)
    (project : Ev → Val) :
    ForcedByStatistic (Multiset Obs) Ev Val where
  stat σ := SufficientStatisticSurface.aggregate S σ q
  project := project
  eval σ := project (SufficientStatisticSurface.aggregate S σ q)
  eval_eq_project_stat := by
    intro σ
    rfl

/-- Equal aggregate statistics force equal projected values. -/
theorem aggregateProjection_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query Ev) (q : Query)
    (project : Ev → Val) {σ₁ σ₂ : Multiset Obs}
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    project (SufficientStatisticSurface.aggregate S σ₁ q) =
      project (SufficientStatisticSurface.aggregate S σ₂ q) :=
  ForcedByStatistic.eval_eq_of_same_stat
    (aggregateProjectionForced S q project) h

end SufficientStatistic

section BinarySufficientStatistic

variable {Obs Query : Type*}

/-- A binary sufficient-statistic surface's strength view is forced by the
aggregate `BinaryEvidence` for the selected query. -/
noncomputable def binarySurfaceStrengthForcedByAggregate
    (S : SufficientStatisticSurface Obs Query BinaryEvidence) (q : Query) :
    ForcedByStatistic (Multiset Obs) BinaryEvidence ℝ≥0∞ :=
  aggregateProjectionForced S q BinaryEvidence.toStrength

/-- A binary sufficient-statistic surface's confidence view is forced by the
aggregate `BinaryEvidence` and the chosen scale `κ`. -/
noncomputable def binarySurfaceConfidenceForcedByAggregate
    (S : SufficientStatisticSurface Obs Query BinaryEvidence)
    (κ : ℝ≥0∞) (q : Query) :
    ForcedByStatistic (Multiset Obs) BinaryEvidence ℝ≥0∞ :=
  aggregateProjectionForced S q (fun e => BinaryEvidence.toConfidence κ e)

/-- Equal aggregate binary evidence forces equal surface strengths. -/
theorem binarySurface_strength_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query BinaryEvidence)
    {σ₁ σ₂ : Multiset Obs} {q : Query}
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    BinaryEvidence.toStrength (SufficientStatisticSurface.aggregate S σ₁ q) =
      BinaryEvidence.toStrength (SufficientStatisticSurface.aggregate S σ₂ q) :=
  ForcedByStatistic.eval_eq_of_same_stat
    (binarySurfaceStrengthForcedByAggregate S q) h

/-- Equal aggregate binary evidence forces equal surface confidences at the
same scale `κ`. -/
theorem binarySurface_confidence_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query BinaryEvidence)
    (κ : ℝ≥0∞) {σ₁ σ₂ : Multiset Obs} {q : Query}
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    BinaryEvidence.toConfidence κ (SufficientStatisticSurface.aggregate S σ₁ q) =
      BinaryEvidence.toConfidence κ (SufficientStatisticSurface.aggregate S σ₂ q) :=
  ForcedByStatistic.eval_eq_of_same_stat
    (binarySurfaceConfidenceForcedByAggregate S κ q) h

end BinarySufficientStatistic

section CategoricalSufficientStatistic

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet

variable {Obs Query : Type*} {k : ℕ}

/-- A categorical sufficient-statistic surface's category count view is forced
by the aggregate `MultiEvidence` for the selected query. -/
noncomputable def categoricalSurfaceCategoryCountForcedByAggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (q : Query) (i : Fin k) :
    ForcedByStatistic (Multiset Obs) (MultiEvidence k) ℕ :=
  aggregateProjectionForced S q (fun e => e.counts i)

/-- A categorical sufficient-statistic surface's total-count view is forced by
the aggregate `MultiEvidence` for the selected query. -/
noncomputable def categoricalSurfaceTotalForcedByAggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (q : Query) :
    ForcedByStatistic (Multiset Obs) (MultiEvidence k) ℕ :=
  aggregateProjectionForced S q MultiEvidence.total

/-- A categorical sufficient-statistic surface's empirical category mean is
forced by the aggregate `MultiEvidence`. -/
noncomputable def categoricalSurfaceMeanForcedByAggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (q : Query) (i : Fin k) :
    ForcedByStatistic (Multiset Obs) (MultiEvidence k) ℝ :=
  aggregateProjectionForced S q
    (fun e => (e.counts i : ℝ) / (e.total : ℝ))

/-- A categorical IDM lower endpoint is forced by the aggregate
`MultiEvidence` once the IDM context and queried category are chosen. -/
noncomputable def categoricalSurfaceIDMLowerForcedByAggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (ctx : IDMPredictiveContext) (q : Query) (i : Fin k) :
    ForcedByStatistic (Multiset Obs) (MultiEvidence k) ℝ :=
  aggregateProjectionForced S q (fun e => idmLower ctx e i)

/-- A categorical IDM upper endpoint is forced by the aggregate
`MultiEvidence` once the IDM context and queried category are chosen. -/
noncomputable def categoricalSurfaceIDMUpperForcedByAggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (ctx : IDMPredictiveContext) (q : Query) (i : Fin k) :
    ForcedByStatistic (Multiset Obs) (MultiEvidence k) ℝ :=
  aggregateProjectionForced S q (fun e => idmUpper ctx e i)

/-- A categorical IDM width is forced by the aggregate `MultiEvidence` once the
IDM context is chosen. -/
noncomputable def categoricalSurfaceIDMWidthForcedByAggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (ctx : IDMPredictiveContext) (q : Query) :
    ForcedByStatistic (Multiset Obs) (MultiEvidence k) ℝ :=
  aggregateProjectionForced S q (fun e => idmWidth ctx e)

/-- Equal aggregate categorical evidence forces equal category counts. -/
theorem categoricalSurface_categoryCount_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k)
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    (SufficientStatisticSurface.aggregate S σ₁ q).counts i =
      (SufficientStatisticSurface.aggregate S σ₂ q).counts i :=
  ForcedByStatistic.eval_eq_of_same_stat
    (categoricalSurfaceCategoryCountForcedByAggregate S q i) h

/-- Equal aggregate categorical evidence forces equal total counts. -/
theorem categoricalSurface_total_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    {σ₁ σ₂ : Multiset Obs} {q : Query}
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    (SufficientStatisticSurface.aggregate S σ₁ q).total =
      (SufficientStatisticSurface.aggregate S σ₂ q).total :=
  ForcedByStatistic.eval_eq_of_same_stat
    (categoricalSurfaceTotalForcedByAggregate S q) h

/-- Equal aggregate categorical evidence forces equal empirical means for a
chosen category. -/
theorem categoricalSurface_mean_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k)
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    ((SufficientStatisticSurface.aggregate S σ₁ q).counts i : ℝ) /
        ((SufficientStatisticSurface.aggregate S σ₁ q).total : ℝ) =
      ((SufficientStatisticSurface.aggregate S σ₂ q).counts i : ℝ) /
        ((SufficientStatisticSurface.aggregate S σ₂ q).total : ℝ) :=
  ForcedByStatistic.eval_eq_of_same_stat
    (categoricalSurfaceMeanForcedByAggregate S q i) h

/-- Equal aggregate categorical evidence forces equal IDM lower endpoints. -/
theorem categoricalSurface_idmLower_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (ctx : IDMPredictiveContext) {σ₁ σ₂ : Multiset Obs} {q : Query}
    (i : Fin k)
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    idmLower ctx (SufficientStatisticSurface.aggregate S σ₁ q) i =
      idmLower ctx (SufficientStatisticSurface.aggregate S σ₂ q) i :=
  ForcedByStatistic.eval_eq_of_same_stat
    (categoricalSurfaceIDMLowerForcedByAggregate S ctx q i) h

/-- Equal aggregate categorical evidence forces equal IDM upper endpoints. -/
theorem categoricalSurface_idmUpper_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (ctx : IDMPredictiveContext) {σ₁ σ₂ : Multiset Obs} {q : Query}
    (i : Fin k)
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    idmUpper ctx (SufficientStatisticSurface.aggregate S σ₁ q) i =
      idmUpper ctx (SufficientStatisticSurface.aggregate S σ₂ q) i :=
  ForcedByStatistic.eval_eq_of_same_stat
    (categoricalSurfaceIDMUpperForcedByAggregate S ctx q i) h

/-- Equal aggregate categorical evidence forces equal IDM widths. -/
theorem categoricalSurface_idmWidth_eq_of_same_aggregate
    (S : SufficientStatisticSurface Obs Query (MultiEvidence k))
    (ctx : IDMPredictiveContext) {σ₁ σ₂ : Multiset Obs} {q : Query}
    (h :
      SufficientStatisticSurface.aggregate S σ₁ q =
        SufficientStatisticSurface.aggregate S σ₂ q) :
    idmWidth ctx (SufficientStatisticSurface.aggregate S σ₁ q) =
      idmWidth ctx (SufficientStatisticSurface.aggregate S σ₂ q) :=
  ForcedByStatistic.eval_eq_of_same_stat
    (categoricalSurfaceIDMWidthForcedByAggregate S ctx q) h

end CategoricalSufficientStatistic

/-! ## Chosen projections from generic ITVs -/

/-- A selector for turning an interval-valued truth value into one displayed
point.  Generic ITVs do not determine which selector is appropriate; a semantic
constructor or decision rule must choose it. -/
inductive ITVSelector where
  | lower
  | midpoint
  | upper
  deriving DecidableEq, Repr

namespace ITVSelector

/-- Evaluate a selected point projection of an ITV. -/
noncomputable def eval : ITVSelector → ITV → ℝ
  | lower, itv => itv.lower
  | midpoint, itv => itv.strength
  | upper, itv => itv.upper

@[simp] theorem eval_lower (itv : ITV) : eval lower itv = itv.lower := rfl
@[simp] theorem eval_midpoint (itv : ITV) : eval midpoint itv = itv.strength := rfl
@[simp] theorem eval_upper (itv : ITV) : eval upper itv = itv.upper := rfl

end ITVSelector

/-- A generic ITV can make the lower and upper selectors disagree.  Therefore
the interval record alone does not force a unique point projection. -/
theorem genericITV_lower_selector_ne_upper_selector :
    ∃ itv : ITV,
      ITVSelector.eval .lower itv ≠ ITVSelector.eval .upper itv := by
  refine ⟨ITV.fullWidthWithCredibility (1 / 2) ?_, ?_⟩
  · norm_num
  · norm_num [ITVSelector.eval, ITV.fullWidthWithCredibility]

/-- A generic ITV can make the lower and midpoint selectors disagree. -/
theorem genericITV_lower_selector_ne_midpoint_selector :
    ∃ itv : ITV,
      ITVSelector.eval .lower itv ≠ ITVSelector.eval .midpoint itv := by
  refine ⟨ITV.fullWidthWithCredibility (1 / 2) ?_, ?_⟩
  · norm_num
  · norm_num [ITVSelector.eval, ITV.fullWidthWithCredibility, ITV.strength]

/-- A generic ITV can make the midpoint and upper selectors disagree. -/
theorem genericITV_midpoint_selector_ne_upper_selector :
    ∃ itv : ITV,
      ITVSelector.eval .midpoint itv ≠ ITVSelector.eval .upper itv := by
  refine ⟨ITV.fullWidthWithCredibility (1 / 2) ?_, ?_⟩
  · norm_num
  · norm_num [ITVSelector.eval, ITV.fullWidthWithCredibility, ITV.strength]

/-- Fixed interval endpoints do not force the selected point: the same ITV can
be projected to lower, midpoint, or upper values. -/
theorem sameITV_has_three_distinct_selector_values :
    ∃ itv : ITV,
      ITVSelector.eval .lower itv ≠ ITVSelector.eval .midpoint itv ∧
        ITVSelector.eval .midpoint itv ≠ ITVSelector.eval .upper itv ∧
          ITVSelector.eval .lower itv ≠ ITVSelector.eval .upper itv := by
  refine ⟨ITV.fullWidthWithCredibility (1 / 2) ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num [ITVSelector.eval, ITV.fullWidthWithCredibility, ITV.strength]
  · norm_num [ITVSelector.eval, ITV.fullWidthWithCredibility, ITV.strength]
  · norm_num [ITVSelector.eval, ITV.fullWidthWithCredibility]

end Mettapedia.PLN.TruthValues.PLNForcedQueries
