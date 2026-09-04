import Mettapedia.GSLT.LanguageDef.AtomlessBooleanQuantifierElimination
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# An atomless Boolean first-order NIK authority

Closed first-order Boolean-algebra formulas form a decidable NIK authority
whose meaning is validity in the independently selected Cantor-clopen
carrier.  The executable path is the finite profile procedure.  It does not
enumerate clopens or inspect the semantic carrier.

Because the semantic predicate is decidable, the trust-boundary checker uses
`Unit` evidence through `DecisionKernel.toChecker`.  This is intentional proof
erasure, not self-validation: the cold carrier meaning is defined first, and
the decision-correctness theorem supplies exact authority afterward.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanQuantifierElimination

universe u

private noncomputable instance cantorInfinite : Infinite CantorAlgebra :=
  infinite_of_isGunky isGunky_clopens_cantor

/-! ## Independently interpreted theory and exact finite contract -/

abbrev Kind := Unit

/-- Cold meaning in the infinite atomless Cantor-clopen algebra. -/
def ColdMeaning (formula : Formula 0) : Prop :=
  Satisfies formula (emptyValuation (B := CantorAlgebra))

/-- Closed first-order formulas with independently declared carrier meaning. -/
def theory : TheoryFamily Kind where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Formula 0
  Scope := fun _kind formula => ColdMeaning formula
  Meaning := fun _kind formula => ColdMeaning formula
  scope_sound := by
    intro _kind _formula meaningful
    exact meaningful

/-- Direct finite decision, qualified against cold Cantor-clopen meaning. -/
def decisionKernel : Checker.DecisionKernel (Formula 0) ColdMeaning where
  decide := decideClosed
  correct := by
    intro formula
    exact decideClosed_eq_true_iff_satisfies isGunky_clopens_cantor formula

/-- Exact NIK contract with intentionally erased boundary evidence. -/
def contract : AuthorityContract theory where
  Certificate := fun _kind => Unit
  checker := fun _kind => decisionKernel.toChecker
  scopeAuthority := fun _kind => decisionKernel.authority

theorem scope_iff_meaning (formula : Formula 0) :
    theory.Scope () formula <-> theory.Meaning () formula :=
  Iff.rfl

/-- Accepted finite computation projects to the independent infinite-primary
meaning. -/
theorem accepted_has_coldMeaning
    (formula : Formula 0) (certificate : contract.Certificate ())
    (accepted : (contract.checker ()).check formula certificate = true) :
    theory.Meaning () formula :=
  (contract.projection ()).sound formula certificate accepted

/-- Every nontrivial atomless Boolean algebra agrees with the selected
Cantor-clopen semantic basis on every closed formula. -/
theorem meaning_iff_satisfies_atomless
    {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    (gunky : IsGunky B) (formula : Formula 0) :
    theory.Meaning () formula <->
      Satisfies formula (emptyValuation (B := B)) :=
  (decideClosed_eq_true_iff_satisfies isGunky_clopens_cantor formula).symm.trans
    (decideClosed_eq_true_iff_satisfies gunky formula)

/-! ## Positive and negative authority canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary

theorem properPart_replays :
    (contract.checker ()).check properPartSentence () = true :=
  properPartSentence_decides_true

theorem properPart_has_coldMeaning :
    theory.Meaning () properPartSentence :=
  accepted_has_coldMeaning properPartSentence () properPart_replays

def noProperPartSentence : Formula 0 := .negation properPartSentence

theorem noProperPart_not_coldMeaning :
    ¬ theory.Meaning () noProperPartSentence := by
  intro noProperPart
  exact noProperPart properPart_has_coldMeaning

theorem noProperPart_rejected :
    (contract.checker ()).check noProperPartSentence () = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact noProperPart_not_coldMeaning
    (accepted_has_coldMeaning noProperPartSentence () accepted)

/-- The finite two-point basis disagrees on the atomlessness sentence, so it
cannot replace the selected semantic ground for this richer language. -/
theorem finiteBasis_disagrees :
    theory.Meaning () properPartSentence /\
      ¬ Satisfies properPartSentence (emptyValuation (B := Bool)) :=
  ⟨properPart_has_coldMeaning, properPartSentence_fails_in_bool⟩

/-- The authority's quantifier eliminator remains exact at the selected cold
meaning. -/
theorem properPart_elimination_preserves_coldMeaning :
    theory.Meaning () (eliminateQuantifiers properPartSentence) <->
      theory.Meaning () properPartSentence :=
  satisfies_eliminateQuantifiers_iff isGunky_clopens_cantor
    properPartSentence emptyValuation

end Canary

#print axioms ColdMeaning
#print axioms theory
#print axioms decisionKernel
#print axioms contract
#print axioms accepted_has_coldMeaning
#print axioms meaning_iff_satisfies_atomless
#print axioms Canary.properPart_replays
#print axioms Canary.properPart_has_coldMeaning
#print axioms Canary.noProperPart_rejected
#print axioms Canary.finiteBasis_disagrees
#print axioms Canary.properPart_elimination_preserves_coldMeaning

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
