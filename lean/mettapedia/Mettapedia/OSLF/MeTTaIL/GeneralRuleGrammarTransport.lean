import Mettapedia.OSLF.MeTTaIL.GeneralPremiseGrammarTransport
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProviderCongruence
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarTransport

/-! Selected-rule admission transports through grammar-preserving language
extensions and provider-row replacement. Declaration ordinals stay actual.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax

theorem ruleObligations_grammar {before after : Snapshot}
    (terms : before.language.terms = after.language.terms)
    (types : before.language.typeNames = after.language.typeNames)
    (signatures : before.provider.signatures = after.provider.signatures) (index : Nat) (rule : RewriteRule) :
    ruleObligations before index rule = ruleObligations after index rule := by
  unfold ruleObligations
  rw [GeneralRuleBindingInference.compile?_transport terms types]
  cases binding : GeneralRuleBindingInference.compile? after.language rule with
  | none => rfl
  | some binding =>
    simp only [GeneralPremise.rulePremisesAdmitted_grammar terms types,
      GeneralPremise.rulePremisesAdmitted_signatures_congr signatures]

theorem ruleObligations_isEmpty_index (snapshot : Snapshot) (first second : Nat) (rule : RewriteRule) :
    (ruleObligations snapshot first rule).isEmpty = (ruleObligations snapshot second rule).isEmpty := by
  unfold ruleObligations
  cases binding : GeneralRuleBindingInference.compile? snapshot.language rule with
  | none => rfl
  | some binding =>
    dsimp only
    split
    · split <;> rfl
    · rfl

#print axioms ruleObligations_grammar
#print axioms ruleObligations_isEmpty_index

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
