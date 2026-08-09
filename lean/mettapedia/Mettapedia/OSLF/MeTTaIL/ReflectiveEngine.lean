import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-!
# Rewrite execution with an explicit reflection profile

The ordinary rewrite engine is determined by the five-field language.  A
reflection profile is additional authored information, so an execution that
uses reflective matching or substitution must receive that profile
explicitly.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveEngine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine

/-- Apply one rewrite using a separately authored reflection profile. -/
def applyRuleWithPremisesUsingReflection
    (profile : ReflectionProfile) (relationEnvironment : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (term : Pattern) : List Pattern :=
  (matchPatternForRuleUsing profile rule term).flatMap fun bindings =>
    (applyPremisesWithEnv relationEnvironment language rule.premises bindings).map
      fun finalBindings =>
        applyBindingsForRuleUsing profile rule finalBindings

/-- Apply one rewrite with reflection and the empty relation environment. -/
def applyRuleWithReflection
    (profile : ReflectionProfile) (language : LanguageDef)
    (rule : RewriteRule) (term : Pattern) : List Pattern :=
  applyRuleWithPremisesUsingReflection profile RelationEnv.empty language rule term

/-- Apply every root rewrite using a separately authored reflection profile. -/
def rewriteStepWithPremisesUsingReflection
    (profile : ReflectionProfile) (relationEnvironment : RelationEnv)
    (language : LanguageDef) (term : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule =>
    applyRuleWithPremisesUsingReflection profile relationEnvironment language rule term

/-- Root rewriting with reflection and the empty relation environment. -/
def rewriteStepWithReflection
    (profile : ReflectionProfile) (language : LanguageDef)
    (term : Pattern) : List Pattern :=
  rewriteStepWithPremisesUsingReflection profile RelationEnv.empty language term

end Mettapedia.OSLF.MeTTaIL.ReflectiveEngine
