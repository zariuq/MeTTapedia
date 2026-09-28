import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Qualification
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.FalsumConservativity

/-!
# The HOTG and qualification controls with `Falsum` defined

The definition `Falsum := ∀p. p` is conservative for sequents that do not
mention `Falsum` (`SetProfile.falsum_definition_conservative`), and for
conversion articles between such terms (`SetProfile.falsum_conversion_conservative`).
Each negative control below is derived from its version modulo the equations of
`add` and `pow` through that theorem; none mentions `Falsum`.

* `HOTGConsumer.closure_needed_defined`: without closure of the universe under
  power sets, membership of a set in its universe does not prove the HOTG step;
* `Qualification.induction_cannot_be_dropped_defined`,
  `Qualification.universe_closure_stays_an_assumption_defined`,
  `Qualification.proof_search_wrong_conclusion_defined` and
  `Qualification.proof_search_altered_equation_defined`: the labeled
  proof-search controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram

open Mettapedia.Logic

namespace HOTGConsumer

/-- **Universe closure is needed, with `Falsum` defined**, from `closure_needed`. -/
theorem closure_needed_defined :
    ¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations [univMemAxiom]
      hotgStepStatement) :=
  fun proof => closure_needed ((SetProfile.falsum_definition_conservative
    (SetProfile.noFalsumHyps (by decide)) (SetProfile.noFalsum (by decide))).mp proof)

end HOTGConsumer

namespace Qualification

theorem induction_cannot_be_dropped_defined :
    Labeled .proofSearch
      (¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations
        [SetProfile.reflAxiom, SetProfile.substAxiom] SetProfile.zeroAddStatement)) :=
  ⟨fun proof => induction_cannot_be_dropped.established
    ((SetProfile.falsum_definition_conservative (SetProfile.noFalsumHyps (by decide))
      (SetProfile.noFalsum (by decide))).mp proof)⟩

theorem universe_closure_stays_an_assumption_defined :
    Labeled .proofSearch
      (¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations
        [HOTGConsumer.univMemAxiom] HOTGConsumer.hotgStepStatement)) :=
  ⟨fun proof => universe_closure_stays_an_assumption.established
    ((SetProfile.falsum_definition_conservative (SetProfile.noFalsumHyps (by decide))
      (SetProfile.noFalsum (by decide))).mp proof)⟩

theorem proof_search_wrong_conclusion_defined :
    Labeled .proofSearch
      (¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations
        SetProfile.zeroAddAssumptions SetProfile.Models.wrongStatement)) :=
  ⟨fun proof => proof_search_wrong_conclusion.established
    ((SetProfile.falsum_definition_conservative (SetProfile.noFalsumHyps (by decide))
      (SetProfile.noFalsum (by decide))).mp proof)⟩

theorem proof_search_altered_equation_defined :
    Labeled .proofSearch
      (¬ HOL.CoreConversion SetProfile.definedEquations (Γ := [SetProfile.numTy])
        (SetProfile.addT SetProfile.zeroT (SetProfile.sucT (.var .vz)))
        (SetProfile.sucT (SetProfile.sucT
          (SetProfile.addT SetProfile.zeroT (.var .vz))))) :=
  ⟨fun conversion => proof_search_altered_equation.established
    ((SetProfile.falsum_conversion_conservative (SetProfile.noFalsum (by decide))
      (SetProfile.noFalsum (by decide))).mp conversion)⟩

end Qualification

#print axioms HOTGConsumer.closure_needed_defined
#print axioms Qualification.induction_cannot_be_dropped_defined
#print axioms Qualification.universe_closure_stays_an_assumption_defined
#print axioms Qualification.proof_search_wrong_conclusion_defined
#print axioms Qualification.proof_search_altered_equation_defined

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
