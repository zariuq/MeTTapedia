import Mettapedia.PLN.TruthValues.EvidenceHorizonInterval
import Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM

/-!
# NARS frequency intervals and Walley predictive intervals

Pei Wang observed in *Formalization of Evidence: A Comparative Study*
(JAGI 1, 2009, pp. 46--47) that the NARS near-future frequency interval

`[w⁺/(w+k), (w⁺+k)/(w+k)]`

has the same numerical form as Walley's binary predictive interval after the
enumerative-induction substitution `w⁺ = w₀ t⁺`, `w = w₀ t`, and a common
change of evidence unit for the horizon.  Wang also stresses that the
semantics are different: NARS values are experience-grounded in a retained
body and scope of evidence, whereas Walley's interval is a coherent
lower/upper predictive-probability envelope.

This module proves both halves.  The numerical agreement is positive; the
scope-erasure theorem is the negative control preventing that agreement from
being promoted into an identification of theories.  The later NARS
incoherence development strengthens this local boundary to whole belief
states and inference paths.

References:

* Pei Wang, "Formalization of Evidence: A Comparative Study", JAGI 1 (2009).
* Peter Walley, *Statistical Reasoning with Imprecise Probabilities* (1991).
-/

namespace Mettapedia.NARS.Bridges.ProbabilityTheory.WalleyInterval

open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.EvidenceHorizonInterval
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

abbrev EvidenceHorizon :=
  Mettapedia.PLN.TruthValues.EvidenceHorizonInterval.EvidenceHorizon

namespace WalleySemantics

/-- The binary IDM credal set interpreting a finite evidence horizon. -/
noncomputable def credalSet (x : EvidenceHorizon) : CredalSetFinite Bool :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.credalSet
    x.counts.nPlus x.counts.nMinus x.horizon
    x.counts.nPlus_nonneg x.counts.nMinus_nonneg x.horizon_pos

/-- Every binary evidence horizon has at least the lower prior extreme
`t = 0`, so its Walley credal interpretation is inhabited. -/
theorem credalSet_nonempty (x : EvidenceHorizon) : (credalSet x).Nonempty := by
  refine ⟨Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.predictiveDist
      x.counts.nPlus x.counts.nMinus x.horizon 0
      x.counts.nPlus_nonneg x.counts.nMinus_nonneg x.horizon_pos (by norm_num), ?_⟩
  exact ⟨0, by norm_num, rfl⟩

/-- Walley's coherent finite lower-prevision semantics for an evidence
horizon. -/
noncomputable def lowerPrevision (x : EvidenceHorizon) : LowerPrevision Bool :=
  FiniteCredalLowerPrevision.credalLowerPrevision
    (credalSet x) (credalSet_nonempty x)

/-- Coherence belongs to the Walley interpretation, not to the bare interval
triple. -/
theorem lowerPrevision_coherent (x : EvidenceHorizon) :
    (lowerPrevision x).isCoherent :=
  LowerPrevision.isCoherent_of_finite (lowerPrevision x)

/-- The lower endpoint of the common interval is the lower expectation of the
true-event gamble under the Walley credal set. -/
theorem lowerProb_trueGamble_eq_interval_lower (x : EvidenceHorizon) :
    lowerProb (credalSet x)
        Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.trueGamble =
      x.toITV.lower := by
  unfold credalSet
  rw [Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.lowerProb_trueGamble_eq]
  rfl

/-- The upper endpoint of the common interval is the upper expectation of the
true-event gamble under the Walley credal set. -/
theorem upperProb_trueGamble_eq_interval_upper (x : EvidenceHorizon) :
    upperProb (credalSet x)
        Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.trueGamble =
      x.toITV.upper := by
  unfold credalSet
  rw [Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.upperProb_trueGamble_eq]
  rfl

end WalleySemantics

/-! ## NARS evidence sources retain scope -/

/-- A NARS interval source retains the body/scope identifier in addition to
the finite weights used by its numerical readout.  The abstract scope type is
intentional: later developments may use derivation histories, reference
classes, or explicit extensional/intensional evidence scopes. -/
structure NARSEvidenceSource (Scope : Type*) where
  scope : Scope
  horizon : EvidenceHorizon

namespace NARSEvidenceSource

/-- Wang's near-future frequency interval.  Its numerical layer is the common
finite-evidence-horizon readout; its source retains NARS evidence scope. -/
noncomputable def frequencyInterval {Scope : Type*}
    (source : NARSEvidenceSource Scope) : ITV :=
  source.horizon.toITV

@[simp] theorem frequencyInterval_lower {Scope : Type*}
    (source : NARSEvidenceSource Scope) :
    source.frequencyInterval.lower =
      source.horizon.counts.nPlus / source.horizon.denominator :=
  rfl

@[simp] theorem frequencyInterval_upper {Scope : Type*}
    (source : NARSEvidenceSource Scope) :
    source.frequencyInterval.upper =
      (source.horizon.counts.nPlus + source.horizon.horizon) /
        source.horizon.denominator :=
  rfl

@[simp] theorem frequencyInterval_credibility {Scope : Type*}
    (source : NARSEvidenceSource Scope) :
    source.frequencyInterval.credibility =
      source.horizon.counts.total / source.horizon.denominator :=
  rfl

/-- NARS enumerative evidence measured in units `scale` from a Walley-style
count/horizon presentation.  Thus `w⁺ = scale * t⁺`,
`w⁻ = scale * t⁻`, and `k = scale * s₀`. -/
def ofEnumerativeScaling {Scope : Type*}
    (scope : Scope) (perUnit : EvidenceHorizon)
    (scale : ℝ) (scale_pos : 0 < scale) : NARSEvidenceSource Scope where
  scope := scope
  horizon := perUnit.scale scale scale_pos

/-- Wang's NARS interval and Walley's predictive interval agree numerically
under their enumerative-induction parameter correspondence.  This is the
scale-invariance theorem, not a semantic identification. -/
theorem frequencyInterval_eq_walley_under_enumerative_scaling
    {Scope : Type*} (scope : Scope) (perUnit : EvidenceHorizon)
    (scale : ℝ) (scale_pos : 0 < scale) :
    (ofEnumerativeScaling scope perUnit scale scale_pos).frequencyInterval =
      perUnit.toITV :=
  perUnit.scale_toITV scale scale_pos

/-- A numerical interval readout retains evidence scope when equal readouts
force equal scopes. -/
def RetainsScope {Scope : Type*}
    (readout : NARSEvidenceSource Scope → ITV) : Prop :=
  ∀ {left right}, readout left = readout right → left.scope = right.scope

namespace ScopeLossCanary

def base : EvidenceHorizon where
  counts :=
    { nPlus := 1
      nMinus := 1
      nPlus_nonneg := by norm_num
      nMinus_nonneg := by norm_num }
  horizon := 1
  horizon_pos := by norm_num

def left : NARSEvidenceSource Bool := ⟨false, base⟩
def right : NARSEvidenceSource Bool := ⟨true, base⟩

theorem sources_ne : left ≠ right := by
  intro h
  have hscope := congrArg NARSEvidenceSource.scope h
  simp [left, right] at hscope

theorem intervals_eq : left.frequencyInterval = right.frequencyInterval :=
  rfl

end ScopeLossCanary

/-- The frequency interval is a lossy readout of NARS semantics: two distinct
evidence scopes can have identical weights, interval, and credibility. -/
theorem frequencyInterval_does_not_retain_scope :
    ¬ RetainsScope (@frequencyInterval Bool) := by
  intro h
  have hscope := h ScopeLossCanary.intervals_eq
  change false = true at hscope
  exact Bool.noConfusion hscope

/-- In particular, equality with Walley's coherent interval cannot by itself
identify a NARS evidence source: the common interval does not reconstruct the
scope that Wang's semantics treats as meaningful. -/
theorem numerical_agreement_does_not_identify_nars_sources :
    ∃ left right : NARSEvidenceSource Bool,
      left ≠ right ∧ left.frequencyInterval = right.frequencyInterval :=
  ⟨ScopeLossCanary.left, ScopeLossCanary.right,
    ScopeLossCanary.sources_ne, ScopeLossCanary.intervals_eq⟩

end NARSEvidenceSource

#print axioms NARSEvidenceSource.frequencyInterval_eq_walley_under_enumerative_scaling
#print axioms NARSEvidenceSource.frequencyInterval_does_not_retain_scope
#print axioms NARSEvidenceSource.numerical_agreement_does_not_identify_nars_sources

end Mettapedia.NARS.Bridges.ProbabilityTheory.WalleyInterval
