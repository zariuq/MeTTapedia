import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

/-!
# Scoped rule instantiation with an explicit binder operation

The authored rule, occurrence paths, dependency spines and retained contextual
values are unchanged. Only the interpretation of its explicit substitution
node is parameterized. Ordinary specialization is proved to recover the
existing scoped interpreter. No matching or binding authority is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleInstantiation

open Syntax RuleBinding Substitution ScopedRuleMatching

/-- Interpret substitutions with the shared occurrence traversal. -/
abbrev instantiateWith? := ScopedRuleMatching.instantiateWith?

/-- Interpret an ordered row with the shared occurrence traversal. -/
abbrev instantiateArgsWith? := ScopedRuleMatching.instantiateArgsWith?

/-- Ordinary binder elimination is the original scoped interpretation. -/
theorem ordinary_specialization (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) :
    instantiateWith? instantiateBVar rule spec ambient site path depth assignment pattern =
      instantiateAt? rule spec ambient site path depth assignment pattern := rfl

/-- Reuse the shared authored RHS instantiation. -/
abbrev reductWith? := ScopedRuleMatching.reductWith?

/-- Reuse the shared matcher and ordered premise execution. -/
abbrev applyRuleWithAt := ScopedRuleExecution.applyRuleWithAt

/-- Ordinary execution is the common interpreter's ordinary specialization. -/
theorem ordinary_execution_specialization (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (rule : RewriteRule) (term : Pattern) :
    applyRuleWithAt instantiateBVar relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleAt relEnv language ambient rule term := rfl

/-- Binder-eliminating reflection using the same source-selected declaration
and the same normalization of the rewrite-introduced replacement quote. -/
def reflectiveOperation (declaration : ReflectivePresentationDecl)
    (replacement body : Pattern) : Pattern :=
  ReflectiveInstantiation.instantiate declaration 0
    (ReflectiveSubstitution.normalizeReflectiveReplacement declaration replacement) body

#print axioms ordinary_specialization
#print axioms ordinary_execution_specialization

end Mettapedia.OSLF.MeTTaIL.ScopedRuleInstantiation
