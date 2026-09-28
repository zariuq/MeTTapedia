import Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
import Mettapedia.PLN.Comparisons.StructuralAdvantages

/-!
# What a distribution semantics cannot say about confidence

The companion to `MarkovLogicConfidence`, for ProbLog. The conclusion is the
same and the reason is sharper.

ProbLog's distribution semantics is not a `MassSemantics`, so the Markov Logic
argument does not transfer; it needs its own bridge. That bridge is already in
the tree:

* `propEvidence (E := probLogToJointEvidence p) A` is the evidence a
  proposition induces;
* `propEvidence_total_eq_totalMass` proves its total is `totalMass p`;
* `toStrength_propEvidence` proves the strength is the ProbLog query
  probability.

As with Markov Logic, the total does not mention the query. So **within a fixed
program every proposition carries the same total evidence**, and a proposition
supported by three worlds is assigned the same confidence as one supported by
three thousand.

For ProbLog the collapse is more complete than for Markov Logic. A Markov Logic
model at least has a `totalMass` that varies from model to model. For a
*normalized* ProbLog program — every `p i ≤ 1`, which is the intended reading —
`BDDCore.WMPLNBDDWMCExact.totalMass_eq_one` gives `totalMass p = 1`, so the
total is not merely query-independent but pinned to the same constant in every
program.

For conditionals the picture is genuinely different, and a blanket claim would
be false.  `linkEvidence_total_eq_antecedentMass` shows a link's total is the
mass of its *antecedent*, so it varies across antecedents: conditional
confidence is not collapsed.  What is collapsed is dependence on the
*consequent*, and that is what is proved.

Not claimed: any deficiency of ProbLog for its own purposes. A distribution
semantics is a semantics for probabilities, and this says what such a semantics
does not additionally carry.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons

open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open Mettapedia.PLN.Core.CompletePLN

variable {n : ℕ}

/-! ## The total does not depend on the query -/

/-- **Every proposition carries the same total evidence.**  Both totals are the
program's `totalMass`, which mentions no proposition. -/
theorem propEvidence_total_query_independent (p : ProbAssignment n) (A B : Fin n) :
    (propEvidence (n := n) (E := probLogToJointEvidence p) A).total
      = (propEvidence (n := n) (E := probLogToJointEvidence p) B).total := by
  rw [propEvidence_total_eq_totalMass p A, propEvidence_total_eq_totalMass p B]

/-- **The negative structural theorem for ProbLog.**  No program induces both
of the two evidence states that differ only in total, so a distribution
semantics cannot distinguish one failure from two. -/
theorem propEvidence_never_oneFailure_and_twoFailures
    (p : ProbAssignment n) (A B : Fin n) :
    ¬ (propEvidence (n := n) (E := probLogToJointEvidence p) A = oneFailure ∧
       propEvidence (n := n) (E := probLogToJointEvidence p) B = twoFailures) := by
  rintro ⟨h₁, h₂⟩
  have htot := propEvidence_total_query_independent p A B
  rw [h₁, h₂] at htot
  exact total_separates htot

/-! ## Conditionals are different, and the difference is real

The propositional collapse does **not** extend to links.  `linkEvidence_total_eq`
gives the total as the mass of the *antecedent*, so it varies from one
antecedent to the next.  A blanket "no confidence tracking" would be false
here, and the honest statement is narrower: the total is independent of the
**consequent** only. -/

/-- Splitting a predicate by a second one and re-summing recovers the first.
Pointwise, since each world lands in exactly one of the two halves. -/
private theorem countWorld_split (E : JointEvidence n) (f g : Fin (2 ^ n) → Bool) :
    countWorld (n := n) (E := E) (fun w => f w && g w)
      + countWorld (n := n) (E := E) (fun w => f w && !g w)
      = countWorld (n := n) (E := E) f := by
  unfold countWorld
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  cases hf : f w <;> cases hg : g w <;> simp [hf, hg]

/-- **A link's total evidence is the mass of its antecedent.** -/
theorem linkEvidence_total_eq_antecedentMass (p : ProbAssignment n) (A B : Fin n) :
    (linkEvidence (n := n) (E := probLogToJointEvidence p) A B).total
      = queryMass p (fun w => worldToAssignment n w A) := by
  rw [linkEvidence_total_eq p A B]
  exact countWorld_split _ _ _

/-- **So a link's confidence ignores its consequent** — but not its antecedent.
This is the correct scope of the collapse for conditionals. -/
theorem linkEvidence_total_indep_of_consequent
    (p : ProbAssignment n) (A B B' : Fin n) :
    (linkEvidence (n := n) (E := probLogToJointEvidence p) A B).total
      = (linkEvidence (n := n) (E := probLogToJointEvidence p) A B').total := by
  rw [linkEvidence_total_eq_antecedentMass p A B,
    linkEvidence_total_eq_antecedentMass p A B']

/-- The negative theorem for links, at its true strength: two links sharing an
antecedent cannot differ in total. -/
theorem linkEvidence_never_oneFailure_and_twoFailures
    (p : ProbAssignment n) (A B B' : Fin n) :
    ¬ (linkEvidence (n := n) (E := probLogToJointEvidence p) A B = oneFailure ∧
       linkEvidence (n := n) (E := probLogToJointEvidence p) A B' = twoFailures) := by
  rintro ⟨h₁, h₂⟩
  have htot := linkEvidence_total_indep_of_consequent p A B B'
  rw [h₁, h₂] at htot
  exact total_separates htot

/-! ## Controls -/

namespace ProbLogConfidenceControls

/-- The contrast: PLN's representation holds both witnesses. -/
theorem pln_holds_both : oneFailure ≠ twoFailures := evidence_separates

/-- They differ exactly where a distribution semantics cannot: in total. -/
theorem pln_totals_differ : oneFailure.total ≠ twoFailures.total := total_separates

/-- And strength alone does not separate them, which is why a probability is
blind to the difference. -/
theorem strengths_agree :
    BinaryEvidence.toStrength oneFailure = BinaryEvidence.toStrength twoFailures := by
  rw [oneFailure_strength, twoFailures_strength]

end ProbLogConfidenceControls

end Mettapedia.PLN.Comparisons

#print axioms Mettapedia.PLN.Comparisons.propEvidence_total_query_independent
#print axioms Mettapedia.PLN.Comparisons.propEvidence_never_oneFailure_and_twoFailures
#print axioms Mettapedia.PLN.Comparisons.linkEvidence_never_oneFailure_and_twoFailures
