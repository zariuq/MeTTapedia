import Mettapedia.OSLF.Syntax.JsonAuthoredComparison
import Mettapedia.OSLF.Syntax.MonoidAuthoredComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Operational interpretation of the algebraic Chapter 7 presentations

JSON and monoids author no reduction rules. Their data and equation models
therefore acquire the general free operational interpretation with an empty
event fiber, and the contextual executor also produces no reducts. The
underlying JSON and monoid comparisons remain the authored ones.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Chapter7AlgebraicOperationalInstances

open CategoryTheory.Limits
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

private abbrev jsonRules :
    List (Rule JsonTermRung.sig ([] : List (MetaArity JsonTermRung.sig))) := []

private abbrev jsonEquations :
    List (EqAxiom JsonTermRung.sig ([] : List (MetaArity JsonTermRung.sig))) := []

/-- The seven authored JSON constructors and their two ordered-list
expansions have the general initial operational interpretation. -/
noncomputable def jsonInitial :
    IsInitial (SubstitutionOperationalModel.presented jsonRules jsonEquations) :=
  SubstitutionOperationalModel.presentedIsInitial jsonRules jsonEquations

/-- A JSON state has no operational firing when no rule is authored. -/
theorem jsonNoFiring
    (j : Judgment
      (SubstitutionOperationalModel.presented jsonRules jsonEquations).base.algebra) :
    ¬ Reduces jsonRules j :=
  no_rules_no_reduction _ j

/-- The actual contextual executor agrees with the empty event fiber for
the authored JSON declaration, at every fuel and every input pattern. -/
theorem jsonExecutorEmpty (fuel : Nat) (term : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.reducts
      JsonAuthoredComparison.authored fuel term = [] := by
  cases fuel <;> rfl

private abbrev monoidRules :
    List (Rule MonoidEquationRung.sig MonoidEquationRung.metas) := []

/-- The actual associativity and two unit equations feed the same general
operational universal property, with no authored rule constructors. -/
noncomputable def monoidInitial :
    IsInitial (SubstitutionOperationalModel.presented monoidRules
      MonoidEquationRung.monoidE) :=
  SubstitutionOperationalModel.presentedIsInitial monoidRules
    MonoidEquationRung.monoidE

/-- Equation classes carry the monoid laws, but there is no firing event. -/
theorem monoidNoFiring
    (j : Judgment
      (SubstitutionOperationalModel.presented monoidRules
        MonoidEquationRung.monoidE).base.algebra) :
    ¬ Reduces monoidRules j :=
  no_rules_no_reduction _ j

/-- The authored monoid executor also has no operational step at any fuel;
its three equations are interpreted in the model, not as rewrite rules. -/
theorem monoidExecutorEmpty (fuel : Nat) (term : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.reducts
      MonoidAuthoredComparison.authored fuel term = [] := by
  cases fuel <;> rfl

#print axioms jsonInitial
#print axioms jsonNoFiring
#print axioms jsonExecutorEmpty
#print axioms monoidInitial
#print axioms monoidNoFiring
#print axioms monoidExecutorEmpty

end Mettapedia.OSLF.Binding.Chapter7AlgebraicOperationalInstances
