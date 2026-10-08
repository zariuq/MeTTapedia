import Mettapedia.OSLF.Syntax.PositiveGSOSControls
import Mettapedia.OSLF.Syntax.DeterministicGSOSRuleQuotient
import Mettapedia.OSLF.Syntax.DeterministicGSOSCofreeControls
import Mettapedia.OSLF.Syntax.DeterministicGSOSFinalBialgebra
import Mettapedia.OSLF.Syntax.GSOSNativeGuardControls
import Mettapedia.OSLF.Syntax.GSOSNativeOccurrenceControls
import Mettapedia.OSLF.Syntax.GSOSNativeHistoryControls
import Mettapedia.OSLF.Syntax.BehavioralEquationDescentBindingControls
import Mettapedia.OSLF.Syntax.LabelwiseFiniteBehaviourControls

/-!
# Admitted behavior rules, native guards and behavioral congruence

This entry point collects distinct, proved correspondence contracts.

* `PositivePremises.NaturalConclusion.targetEquiv` classifies natural
  conclusions by actual free targets with original arguments and one derivative at each active
  argument. Passive arguments require no outgoing event. The all-active
  and all-passive instances retain their different premise domains.
* `guardedLawEquiv` classifies arbitrary-action deterministic natural laws
  by independently authored complete guarded schemas. A complete guard
  may have infinite observation support.
* `ConsistentPresentation.equivalence` identifies ordinary finite-premise
  presentations modulo successful target readouts with exactly the laws
  having finite successful observation. Its image-finite counterpart uses
  uniform finite observation; finite action carriers recover every law.
* Native negative guards are Heyting negation of labelled source images.
  Agreement with present absence is earned from availability reflection.
  Complete firing receipts retain every authored positive occurrence and
  supplied origin; normalization of addresses does not recover receipts.
* The deterministic cofree coalgebra consists of actual coloured,
  prefix-closed partial action trees. The free monad lifting induces a
  distributive law satisfying all four Beck equations and recovering the
  original operational lifting. Final tree equality is exactly span
  bisimilarity and is preserved by every free constructor context. The
  final coalgebra is terminal in the actual Eilenberg–Moore category of
  the lifted monad, and final observation preserves its original algebra
  action.
* An independently formed binder-indexed behavior descends through the
  existing equational quotient exactly when its local equation checks
  hold, under the stated constructor compatibility. Its substitution
  comparison has separate local and admitted-input conditions.

Finite branching per action and finite total outgoing support are distinct
contracts. The labelwise finite behavior embedding does not construct a
nondeterministic GSOS distributive law. The binder-indexed quotient result
does not admit every higher-order rule format or every raw language
presentation. Language-specific operational comparisons require their
own observation and admission theorems.
-/
