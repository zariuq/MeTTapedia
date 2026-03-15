import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# WM Experiment Interface (Minimal Core)

This module adds a minimal experiment/channel/query interface under the WM
calculus:

- experiment state: multiset of hypotheses (`Multiset Θ`)
- channel: deterministic map `Θ → Ω`
- query: channel + outcome predicate on observations
- evidence: count of hypotheses satisfying / refuting the query

It also adds a Blackwell-style factorization wrapper:

- if `weak = κ ∘ strong`, then any weak query is equivalent to a pulled-back
  strong query, yielding a WM consequence rule.
-/

namespace Mettapedia.Logic.PLNWorldModelExperiment

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

variable {Θ Ω : Type*}

/-- Deterministic experiment channel from hypotheses `Θ` to observations `Ω`. -/
@[ext] structure ExperimentChannel (Θ Ω : Type*) where
  run : Θ → Ω

/-- Experiment query: evaluate an outcome predicate under one channel. -/
@[ext] structure ExperimentQuery (Θ Ω : Type*) where
  channel : ExperimentChannel Θ Ω
  outcome : Ω → Prop

/-- Canonical query constructor from a channel and an observation predicate. -/
def queryOf (c : ExperimentChannel Θ Ω) (p : Ω → Prop) : ExperimentQuery Θ Ω :=
  ⟨c, p⟩

/-- Pointwise query satisfiability at one hypothesis. -/
def queryHolds (θ : Θ) (q : ExperimentQuery Θ Ω) : Prop :=
  q.outcome (q.channel.run θ)

instance : EvidenceType (Multiset Θ) where

/-- Evidence for an experiment query:
positive count = satisfying hypotheses; negative count = refuting hypotheses. -/
noncomputable def experimentEvidence
    (W : Multiset Θ) (q : ExperimentQuery Θ Ω) : Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun θ : Θ => queryHolds θ q) W : ℝ≥0∞),
     (Multiset.countP (fun θ : Θ => ¬ queryHolds θ q) W : ℝ≥0∞)⟩

theorem experimentEvidence_add
    (W₁ W₂ : Multiset Θ) (q : ExperimentQuery Θ Ω) :
    experimentEvidence (W₁ + W₂) q =
      experimentEvidence W₁ q + experimentEvidence W₂ q := by
  classical
  apply Evidence.ext'
  · simp [experimentEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [experimentEvidence, Multiset.countP_add, Evidence.hplus_def]

/-- WM instance induced by multiset counting over hypotheses. -/
noncomputable instance : WorldModel (Multiset Θ) (ExperimentQuery Θ Ω) where
  evidence := experimentEvidence
  evidence_add := experimentEvidence_add
  evidence_zero q := by
    classical
    simp only [experimentEvidence, Multiset.countP_zero, Nat.cast_zero]; rfl

/-- Blackwell-style factorization witness (`weak = κ ∘ strong`). -/
def BlackwellFactorsThrough
    (strong weak : ExperimentChannel Θ Ω) (κ : Ω → Ω) : Prop :=
  ∀ θ : Θ, weak.run θ = κ (strong.run θ)

/-- Existential Blackwell-style dominance witness. -/
def BlackwellDominates
    (strong weak : ExperimentChannel Θ Ω) : Prop :=
  ∃ κ : Ω → Ω, BlackwellFactorsThrough strong weak κ

/-- Pullback of a weak outcome predicate along garbling `κ` to the strong channel. -/
def pullbackQuery
    (strong : ExperimentChannel Θ Ω)
    (κ : Ω → Ω)
    (p : Ω → Prop) : ExperimentQuery Θ Ω :=
  queryOf strong (fun o => p (κ o))

/-- Factorization yields query-level equivalence (evidence equality) under pullback. -/
theorem wmQueryEq_of_blackwellFactor
    (strong weak : ExperimentChannel Θ Ω)
    (κ : Ω → Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (p : Ω → Prop) :
    WMQueryEq (State := Multiset Θ) (Query := ExperimentQuery Θ Ω)
      (queryOf weak p) (pullbackQuery strong κ p) := by
  intro W
  classical
  have hpred :
      (fun θ : Θ => p (weak.run θ)) =
        (fun θ : Θ => p (κ (strong.run θ))) := by
    funext θ
    simpa [BlackwellFactorsThrough] using congrArg p (hfactor θ)
  have hpredNeg :
      (fun θ : Θ => ¬ p (weak.run θ)) =
        (fun θ : Θ => ¬ p (κ (strong.run θ))) := by
    funext θ
    simpa [hpred] using congrArg Not (congrArg p (hfactor θ))
  apply Evidence.ext'
  · simp [WorldModel.evidence, experimentEvidence, queryOf, pullbackQuery, queryHolds, hpred]
  · simp [WorldModel.evidence, experimentEvidence, queryOf, pullbackQuery, queryHolds, hpredNeg]

/-- Strength equality transport for Blackwell-style factorization. -/
theorem queryStrength_eq_of_blackwellFactor
    (strong weak : ExperimentChannel Θ Ω)
    (κ : Ω → Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (p : Ω → Prop)
    (W : Multiset Θ) :
    WorldModel.queryStrength (State := Multiset Θ) (Query := ExperimentQuery Θ Ω)
        W (queryOf weak p) =
      WorldModel.queryStrength (State := Multiset Θ) (Query := ExperimentQuery Θ Ω)
        W (pullbackQuery strong κ p) := by
  exact
    WMQueryEq.to_queryStrength
      (State := Multiset Θ) (Query := ExperimentQuery Θ Ω)
      (wmQueryEq_of_blackwellFactor strong weak κ hfactor p) W

/-- Blackwell-style dominance-to-consequence wrapper:
if `weak = κ ∘ strong`, weak-query strength is bounded by pullback strong-query
strength on every WM state. -/
theorem queryStrength_le_of_blackwellFactor
    (strong weak : ExperimentChannel Θ Ω)
    (κ : Ω → Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (p : Ω → Prop)
    (W : Multiset Θ) :
    WorldModel.queryStrength (State := Multiset Θ) (Query := ExperimentQuery Θ Ω)
        W (queryOf weak p) ≤
      WorldModel.queryStrength (State := Multiset Θ) (Query := ExperimentQuery Θ Ω)
        W (pullbackQuery strong κ p) := by
  exact le_of_eq (queryStrength_eq_of_blackwellFactor strong weak κ hfactor p W)

/-- Existential Blackwell dominance yields an explicit consequence inequality
after choosing the garbling witness. -/
theorem blackwellDominates_to_strengthLE
    (strong weak : ExperimentChannel Θ Ω)
    (hdom : BlackwellDominates strong weak)
    (p : Ω → Prop) :
    ∃ κ : Ω → Ω,
      WMStrengthLE (State := Multiset Θ) (Query := ExperimentQuery Θ Ω)
        (queryOf weak p) (pullbackQuery strong κ p) := by
  rcases hdom with ⟨κ, hκ⟩
  refine ⟨κ, ?_⟩
  intro W
  exact queryStrength_le_of_blackwellFactor strong weak κ hκ p W

/-- Consequence-rule packaging for one Blackwell factorization witness. -/
def wmConsequenceRule_of_blackwellFactor
    (strong weak : ExperimentChannel Θ Ω)
    (κ : Ω → Ω)
    (p : Ω → Prop) :
    WMConsequenceRule (Multiset Θ) (ExperimentQuery Θ Ω) where
  side := BlackwellFactorsThrough strong weak κ
  premise := queryOf weak p
  conclusion := pullbackQuery strong κ p
  sound := by
    intro hSide W
    exact queryStrength_le_of_blackwellFactor strong weak κ hSide p W

end Mettapedia.Logic.PLNWorldModelExperiment
