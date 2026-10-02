import Mettapedia.OSLF.Framework.PredFiniteSufficient
import Mettapedia.OSLF.MeTTaIL.RuleInstances

/-!
# Every instance of a plain rule is a step

A step of a language with plain rules is a rule whose left side matches the
source.  Conversely, when both sides of a rule are matched exactly and the
right side mentions no variable that the left side does not, every
instantiation of the left side steps to the same instantiation of the right
side.  The matcher may return another binding list than the one instantiated;
it agrees with it on every variable of the left side, hence of the right.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.Framework.PredFiniteSufficient

/-- **Every instance of a plain rule is a step.** -/
theorem step_of_instance {relEnv : RelationEnv} {lang : LanguageDef} (plain : PlainRules lang)
    {rule : RewriteRule} (member : rule ∈ lang.rewrites)
    (leftExact : isMatchCorrectAux rule.left = true)
    (rightExact : isMatchCorrectAux rule.right = true)
    (bound : ∀ name ∈ freeVars rule.right, name ∈ freeVars rule.left)
    (bindings : Bindings) :
    Step (engineBasePremises relEnv) lang (applyBindings bindings rule.left)
      (applyBindings bindings rule.right) := by
  obtain ⟨found, matched, -⟩ := matchPattern_applyBindings_complete (bs := bindings) leftExact
  have same : applyBindings found rule.left = applyBindings bindings rule.left :=
    matchPattern_correct matched leftExact
  have agree := applyBindings_injective_isMatchCorrect leftExact same
  refine (step_iff_exists_match plain).mpr ⟨rule, member, found, matched, ?_⟩
  exact applyBindings_eq_of_agree_isMatchCorrect rightExact fun name inRight =>
    agree name (bound name inRight)

end Mettapedia.OSLF.MeTTaIL.ContextualStep
