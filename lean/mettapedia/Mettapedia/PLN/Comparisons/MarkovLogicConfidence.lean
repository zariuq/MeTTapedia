import Mettapedia.Logic.MarkovLogicAbstract
import Mettapedia.PLN.Comparisons.StructuralAdvantages

/-!
# What a mass semantics cannot say about confidence

`StructuralAdvantages.strengthOnly_readout_loses_total` is a statement about an
arbitrary readout that depends only on strength.  This file discharges its
hypothesis for Markov Logic, so the comparison it was written for becomes a
theorem rather than a claim.

The bridge is already in the tree and is exact, not an analogy:

* `MassSemantics.evidenceOfMasses q = ⟨queryMass q, totalMass - queryMass q⟩`
  is the evidence a query induces;
* `MassSemantics.toStrength_evidenceOfMasses` proves
  `toStrength (evidenceOfMasses q) = queryProb q` — a Markov Logic query
  probability **is** the PLN strength of that evidence;
* `MassSemantics.evidenceOfMasses_total` proves
  `(evidenceOfMasses q).total = totalMass`.

The third of these is the one nobody drew a consequence from, and it is the
whole negative result. The total does not mention `q`. So within a single mass
semantics **every query carries exactly the same total evidence**: a query
settled by three observations and a query settled by three thousand are
assigned the same confidence, because confidence is computed from the total and
the total is a property of the model, not of the query.

`evidenceOfMasses_never_oneFailure_and_twoFailures` states this in the sharpest
available form: no mass semantics induces both of
`StructuralAdvantages`'s two witnesses, which differ only in total. PLN's
representation holds both, since they are just values of `BinaryEvidence`.

What is **not** claimed: that Markov Logic is thereby deficient for its own
purposes, or that the same holds of ProbLog. The latter needs its own bridge —
its BDD semantics is not a `MassSemantics` — and is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons

open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.PLN.Evidence.EvidenceQuantale

variable {Query : Type*}

/-! ## The readout is strength-determined -/

/-- **A mass semantics' query probability depends only on strength**, which is
the hypothesis of `strengthOnly_readout_loses_total`.  Immediate from the
existing bridge. -/
theorem queryProb_strengthDetermined (S : MassSemantics Query) (q₁ q₂ : Query)
    (h : BinaryEvidence.toStrength (S.evidenceOfMasses q₁)
       = BinaryEvidence.toStrength (S.evidenceOfMasses q₂)) :
    S.queryProb q₁ = S.queryProb q₂ := by
  rw [← S.toStrength_evidenceOfMasses q₁, ← S.toStrength_evidenceOfMasses q₂]
  exact h

/-! ## And the total it is computed against does not depend on the query -/

/-- **Every query carries the same total evidence.**  Both totals are the
model's `totalMass`, which mentions no query. -/
theorem evidenceOfMasses_total_query_independent
    (S : MassSemantics Query) (q₁ q₂ : Query) :
    (S.evidenceOfMasses q₁).total = (S.evidenceOfMasses q₂).total := by
  rw [S.evidenceOfMasses_total q₁, S.evidenceOfMasses_total q₂]

/-- **The negative structural theorem.**  No mass semantics induces both of the
two evidence states that differ only in total.  A framework of this shape
therefore cannot distinguish one failure from two. -/
theorem evidenceOfMasses_never_oneFailure_and_twoFailures
    (S : MassSemantics Query) (q₁ q₂ : Query) :
    ¬ (S.evidenceOfMasses q₁ = oneFailure ∧ S.evidenceOfMasses q₂ = twoFailures) := by
  rintro ⟨h₁, h₂⟩
  have htot := evidenceOfMasses_total_query_independent S q₁ q₂
  rw [h₁, h₂] at htot
  exact total_separates htot

/-- Said the other way round: if two queries' induced evidence differ at all,
they differ in strength, never in total. -/
theorem evidenceOfMasses_differ_only_in_strength
    (S : MassSemantics Query) (q₁ q₂ : Query)
    (hne : S.evidenceOfMasses q₁ ≠ S.evidenceOfMasses q₂) :
    (S.evidenceOfMasses q₁).pos ≠ (S.evidenceOfMasses q₂).pos ∧
      (S.evidenceOfMasses q₁).total = (S.evidenceOfMasses q₂).total := by
  refine ⟨?_, evidenceOfMasses_total_query_independent S q₁ q₂⟩
  intro hpos
  refine hne (BinaryEvidence.ext' hpos ?_)
  show S.totalMass - S.queryMass q₁ = S.totalMass - S.queryMass q₂
  rw [show S.queryMass q₁ = S.queryMass q₂ from hpos]

/-! ## Controls -/

namespace MarkovLogicConfidenceControls

/-- The contrast, so the theorem is not vacuous: PLN's representation *does*
hold both witnesses, because they are values of `BinaryEvidence`. -/
theorem pln_holds_both : oneFailure ≠ twoFailures := evidence_separates

/-- And they differ exactly where a mass semantics cannot: in total. -/
theorem pln_totals_differ : oneFailure.total ≠ twoFailures.total := total_separates

/-- Strength alone does not separate them, which is why a strength-determined
readout is blind to the difference. -/
theorem strengths_agree :
    BinaryEvidence.toStrength oneFailure = BinaryEvidence.toStrength twoFailures := by
  rw [oneFailure_strength, twoFailures_strength]

end MarkovLogicConfidenceControls

end Mettapedia.PLN.Comparisons

#print axioms Mettapedia.PLN.Comparisons.queryProb_strengthDetermined
#print axioms Mettapedia.PLN.Comparisons.evidenceOfMasses_total_query_independent
#print axioms Mettapedia.PLN.Comparisons.evidenceOfMasses_never_oneFailure_and_twoFailures
