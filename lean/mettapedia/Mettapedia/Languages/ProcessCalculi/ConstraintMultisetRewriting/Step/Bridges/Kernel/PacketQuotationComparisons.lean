import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.PacketQuotationExtensions
import Mettapedia.Languages.HOLLight.EqualityExpansion

/-!
# Explicit EQ_MP evidence at a quoted source boundary

The equality view, matched input and exact hypothesis union establish the
existing primitive check. Finset representation order is normalized as an
equality of the actual sets; no alternative inference rule or checker is
introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationComparisons

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight

theorem eq_mp_claim_checked (policy : AxiomPolicy) [DecidablePred policy]
    (equation input : Theorem) (left right : CanonicalTerm) (hypotheses : Finset CanonicalTerm)
    (view : CanonicalTerm.EqualityViewSemantics equation.sequent.concl left right)
    (matched : left = input.sequent.concl)
    (united : equation.sequent.hyp ∪ input.sequent.hyp = hypotheses) :
    (RuleRequest.inference (.eqMp equation input)).check policy =
      some (Theorem.unionResult equation input hypotheses right) := by
  change checkEqMp equation input = _
  simpa only [EqualityExpansion.eqMpResult, united] using
    EqualityExpansion.eqMpResult_checked equation input left right view matched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationComparisons
