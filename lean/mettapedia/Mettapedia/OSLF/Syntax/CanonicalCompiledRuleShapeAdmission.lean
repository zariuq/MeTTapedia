import Mettapedia.OSLF.Syntax.CanonicalScopedRuleExecution
import Mettapedia.OSLF.Syntax.ResultSortedScopedPremises
import Mettapedia.OSLF.Syntax.ResultSortedScopedOperationalPresentation

/-!
# Whole-language compilation admits every listed sorted rule shape

Compilation of the ordered authored rule list is stronger than compilation
of one convenient rule. Every listed rule shape in such a language has the
canonical annotation of all its recursive child contexts and result sorts.
This is shape admission only; endpoint typing is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalCompiledRuleShapeAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory)
open Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedPremises
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext HasType)

/-- A successfully compiled ordered list includes successful contextual
compilation of every listed rule, not only of the first one. -/
theorem listed_rule_compiles (language : LanguageDef)
    (ambient : List TypeExpr) :
    ∀ {entries : List (RewriteRule × Nat)}
      {compiled : List (RewriteRule × Nat × List CanonicalPremise)},
      compileRuleListAt? language ambient entries = some compiled →
      ∀ {rule : RewriteRule} {index : Nat},
        (rule, index) ∈ entries →
        ∃ premises, compileRulePremisesAt? language rule ambient =
          some premises
  | [], _, _, _, _, listed => by simp at listed
  | (headRule, headIndex) :: rest, compiled, compiledEq,
      rule, index, listed => by
      cases firstEq : compileRulePremisesAt? language headRule ambient with
      | none =>
          simp [compileRuleListAt?, firstEq] at compiledEq
      | some headPremises =>
          cases restEq : compileRuleListAt? language ambient rest with
          | none =>
              simp [compileRuleListAt?, firstEq, restEq] at compiledEq
          | some tailPremises =>
              simp [compileRuleListAt?, firstEq, restEq] at compiledEq
              rcases List.mem_cons.mp listed with head | tail
              · have pairEq : rule = headRule ∧ index = headIndex :=
                  Prod.mk.inj head
                rcases pairEq with ⟨rfl, rfl⟩
                exact ⟨headPremises, firstEq⟩
              · exact listed_rule_compiles language ambient restEq tail

/-- A successful contextual rule compilation supplies both unique schema
names and its complete, ordered canonical premise list. -/
theorem compiled_rule_components (language : LanguageDef)
    (ambient : List TypeExpr) (rule : RewriteRule)
    (premises : List CanonicalPremise)
    (compiled : compileRulePremisesAt? language rule ambient =
      some premises) :
    (rule.typeContext.map Prod.fst).Nodup ∧
      compileList? language (freeFromRuleContext rule.typeContext)
        ambient rule.premises = some premises := by
  unfold compileRulePremisesAt? at compiled
  split at compiled
  · exact ⟨‹_›, compiled⟩
  · contradiction

/-- If the complete authored language compiles at a context, every raw
constructor selected from one of its listed rules has canonical ordered
result-sort annotations on all recursive premises. -/
theorem listed_shape_has_result_children
    (relEnv : RelationEnv) (language : LanguageDef)
    (ambient : List TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled : compileRuleListAt? language ambient
      language.rewrites.zipIdx = some compiled)
    {source target : Pattern}
    (shape : RuleSkeleton RuleHistory relEnv language ambient.length
      source target) :
    ∃ children,
      ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
        ambient shape = some children := by
  obtain ⟨premises, ruleCompiled⟩ := listed_rule_compiles language ambient
    allCompiled shape.listed
  obtain ⟨unique, premiseCompiled⟩ := compiled_rule_components language
    ambient shape.rule premises ruleCompiled
  exact ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_exists_of_compiled
    ambient shape unique premises premiseCompiled

/-- A raw listed shape with independently proved endpoint typing lifts to
the genuinely result-sorted presentation. Compilation supplies its ordered
child-sort annotation; the two endpoint judgments remain explicit and cannot
be manufactured by mere declaration admission. -/
noncomputable def lift_listed_shape
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled : compileRuleListAt? language ambient
      language.rewrites.zipIdx = some compiled)
    {source target : Pattern}
    (shape : RuleSkeleton RuleHistory relEnv language ambient.length
      source target)
    (sourceTyped : HasType language free ambient source resultType)
    (targetTyped : HasType language free ambient target resultType) :
    ResultSortedScopedOperationalPresentation.RuleShape relEnv language
      free ambient resultType source target := by
  let found := listed_rule_compiles language ambient allCompiled shape.listed
  let premises := Classical.choose found
  have ruleCompiled : compileRulePremisesAt? language shape.rule ambient =
      some premises := Classical.choose_spec found
  have components := compiled_rule_components language ambient shape.rule
    premises ruleCompiled
  exact ResultSortedScopedOperationalPresentation.RuleShape.ofCompiled
    free ambient resultType shape components.1 premises components.2
      sourceTyped targetTyped

@[simp] theorem lift_listed_shape_raw
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled : compileRuleListAt? language ambient
      language.rewrites.zipIdx = some compiled)
    {source target : Pattern}
    (shape : RuleSkeleton RuleHistory relEnv language ambient.length
      source target)
    (sourceTyped : HasType language free ambient source resultType)
    (targetTyped : HasType language free ambient target resultType) :
    (lift_listed_shape relEnv language free ambient resultType compiled
      allCompiled shape sourceTyped targetTyped).raw = shape := by
  unfold lift_listed_shape
  simp

/-- Under whole-language compilation, a result-sorted constructor is
exactly a raw listed constructor together with the authored typing of its
two endpoints. The canonical ordered child annotation is determined by the
compiled rule, so it contributes no independent choice. -/
noncomputable def sortedShapeEquiv
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled : compileRuleListAt? language ambient
      language.rewrites.zipIdx = some compiled)
    (source target : Pattern) :
    ResultSortedScopedOperationalPresentation.RuleShape relEnv language
      free ambient resultType source target ≃
      {_raw : RuleSkeleton RuleHistory relEnv language ambient.length
        source target //
        HasType language free ambient source resultType ∧
        HasType language free ambient target resultType} where
  toFun typed := ⟨typed.raw, typed.sourceTyped, typed.targetTyped⟩
  invFun raw := lift_listed_shape relEnv language free ambient resultType
    compiled allCompiled raw.1 raw.2.1 raw.2.2
  left_inv typed := by
    rcases typed with ⟨raw, children, canonical, sourceTyped, targetTyped⟩
    cases hLift : lift_listed_shape relEnv language free ambient resultType
        compiled allCompiled raw sourceTyped targetTyped with
    | mk raw' children' canonical' sourceTyped' targetTyped' =>
        have rawEq := lift_listed_shape_raw relEnv language free ambient
          resultType compiled allCompiled raw sourceTyped targetTyped
        rw [hLift] at rawEq
        cases rawEq
        have childrenEq : children' = children :=
          Option.some.inj (canonical'.symm.trans canonical)
        cases childrenEq
        exact hLift
  right_inv raw := by
    apply Subtype.ext
    exact lift_listed_shape_raw relEnv language free ambient resultType
      compiled allCompiled raw.1 raw.2.1 raw.2.2

#print axioms listed_rule_compiles
#print axioms compiled_rule_components
#print axioms listed_shape_has_result_children
#print axioms lift_listed_shape
#print axioms lift_listed_shape_raw
#print axioms sortedShapeEquiv

end Mettapedia.OSLF.Binding.CanonicalCompiledRuleShapeAdmission
