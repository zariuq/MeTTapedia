import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
import Mettapedia.OSLF.MeTTaIL.ContextRuleExtension

/-!
# Premise-free root firings under additional constructors

Adding constructors to an environment's grammar keeps every premise-free root firing:
typing only grows, while matching, the selected declarations, their specifications and the
binder operation do not read the grammar. The environment of an explicitly extended plan
(`compileWithContextRules`) is the compiled plan's environment with the context rules of its
reflection profile, so a premise-free firing of the compiled plan is a firing of the
extended one.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The environment whose grammar also has the constructors `extra`. -/
def Environment.extendTerms (environment : Environment) (extra : List GrammarRule) : Environment :=
  { environment with language := { environment.language with terms := extra ++ environment.language.terms } }

theorem assignmentTyped_extendTerms {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {assignment : Assignment}
    (extra : List GrammarRule)
    (typed : ConditionalEquationExecution.AssignmentTyped language free bound rule spec assignment) :
    ConditionalEquationExecution.AssignmentTyped { language with terms := extra ++ language.terms } free bound
      rule spec assignment := by
  intro name value present
  obtain ⟨dependencies, expected, declared, context, same, ambient, sorted⟩ := typed name value present
  exact ⟨dependencies, expected, declared, context, same, ambient,
    HasType.of_terms_subset (List.subset_append_right _ _) sorted⟩

/-- Premises that hold with no events are no premises, and they leave the assignment unchanged. -/
theorem Interpreted.PremisesHold.eq_nil {Choice : Type} {meaning : MatchingInterpretation Choice}
    {environment : Environment} {context : Context} {premises : List Premise} {initial final : Assignment}
    (held : Interpreted.PremisesHold meaning environment context premises initial final []) :
    premises = [] ∧ final = initial := by
  cases held
  exact ⟨rfl, rfl⟩

/-- **A premise-free root firing survives additional constructors.** -/
theorem Interpreted.RootFiring.extendTerms {Choice : Type} {meaning : MatchingInterpretation Choice}
    {environment : Environment} (extra : List GrammarRule) {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {trace : List Choice} {captured completed : Assignment}
    (firing : Interpreted.RootFiring meaning environment bound type source index trace captured completed [] target) :
    Interpreted.RootFiring meaning (environment.extendTerms extra) bound type source index trace captured
      completed [] target := by
  cases firing with
  | fire declared specified admitted sorted matching typed premises reduced targetSorted =>
      obtain ⟨empty, rfl⟩ := premises.eq_nil
      exact .fire declared specified admitted
        ⟨HasType.of_terms_subset (List.subset_append_right _ _) sorted.1, sorted.2⟩ matching
        ⟨assignmentTyped_extendTerms extra typed.1, typed.2⟩ (empty ▸ .nil) reduced
        ⟨HasType.of_terms_subset (List.subset_append_right _ _) targetSorted.1, targetSorted.2⟩

/-- The extended plan's environment adds the context rules to the compiled plan's. -/
theorem environment_compileWithContextRules (snapshot : Snapshot) (permissions : Permissions) :
    GeneralPlanEnvironment.environment (compileWithContextRules snapshot permissions) =
      (GeneralPlanEnvironment.environment (compile snapshot permissions)).extendTerms
        permissions.reflection.contextRules := rfl

/-- **A premise-free firing of the compiled plan is a firing of the extended plan.** -/
theorem rootFiring_of_compiled {snapshot : Snapshot} {permissions : Permissions} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    (firing : RootFiring (GeneralPlanEnvironment.environment (compile snapshot permissions)) bound type source
      index trace captured completed [] target) :
    RootFiring (GeneralPlanEnvironment.environment (compileWithContextRules snapshot permissions)) bound type
      source index trace captured completed [] target := by
  rw [environment_compileWithContextRules]
  exact Interpreted.RootFiring.extendTerms _ firing

theorem exists_rootFiring_of_compiled {snapshot : Snapshot} {permissions : Permissions} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    (firing : ∃ trace captured, RootFiring (GeneralPlanEnvironment.environment (compile snapshot permissions))
      bound type source index trace captured captured [] target) :
    ∃ trace captured, RootFiring (GeneralPlanEnvironment.environment (compileWithContextRules snapshot permissions))
      bound type source index trace captured captured [] target :=
  let ⟨trace, captured, held⟩ := firing
  ⟨trace, captured, rootFiring_of_compiled held⟩

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
