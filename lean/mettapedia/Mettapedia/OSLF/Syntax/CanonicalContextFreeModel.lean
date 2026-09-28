import Mettapedia.OSLF.Syntax.CanonicalContextOracle
import Mettapedia.OSLF.Syntax.ScopedOperationalCertification

/-!
# Bounded free firing trees from an all-context authored elaboration

A recursive step premise may move into any finite local binder extension.
The compilation plan records that the same authored rule list elaborates at
each resulting sorted context. Given that plan, bounded firing histories are
generated recursively using the complete context at every premise query.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalContextFreeModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution
open Mettapedia.OSLF.Binding.CanonicalContextOracle
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.OSLF.Binding.ScopedOperationalCertification

/-- An all-context elaboration of one authored rule list. This is a real
admission condition: no failed declaration is interpreted as zero firings. -/
structure AllContextRuleElaboration (language : LanguageDef) where
  rules : List TypeExpr → List (RewriteRule × Nat × List CanonicalPremise)
  checked : ∀ ambient,
    compileRuleListAt? language ambient language.rewrites.zipIdx =
      some (rules ambient)

/-- The bounded free firing tree queries recursive premises in their full
sorted binder context and retains every rule and oracle-result ordinal. -/
def rewriteWithContexts (language : LanguageDef)
    (plan : AllContextRuleElaboration language) (relEnv : RelationEnv) :
    Nat → ContextOracle RuleHistory
  | 0, _, _ => []
  | fuel + 1, ambient, source =>
      (plan.rules ambient).flatMap fun (rule, ruleIndex, premises) =>
        (applyRule (rewriteWithContexts language plan relEnv fuel) relEnv
          language rule ambient source premises).map fun firing =>
            (.fire ruleIndex firing.history, firing.target)

/-- The new recursion agrees with the old depth-indexed free firing tree
when the authored language elaborates at every context. This equality is of
ordered lists of full histories, not merely of endpoint reachability. -/
theorem rewriteWithContexts_eq_depth (language : LanguageDef)
    (plan : AllContextRuleElaboration language) (relEnv : RelationEnv) :
    ∀ fuel ambient source,
      rewriteWithContexts language plan relEnv fuel ambient source =
        rewriteAt relEnv language fuel ambient.length source := by
  intro fuel
  induction fuel with
  | zero =>
      intro ambient source
      rfl
  | succ fuel ih =>
      intro ambient source
      have oracleEq :
          rewriteWithContexts language plan relEnv fuel =
            fromDepth (rewriteAt relEnv language fuel) := by
        funext context term
        exact ih context term
      simp only [rewriteWithContexts, rewriteAt]
      rw [oracleEq]
      have sameRuleResults :
          (plan.rules ambient).flatMap (fun (rule, index, premises) =>
            (applyRule (fromDepth (rewriteAt relEnv language fuel)) relEnv
              language rule ambient source premises).map fun firing =>
                (index, firing)) =
          language.rewrites.zipIdx.flatMap (fun (rule, index) =>
            (applyRuleWithOracle (rewriteAt relEnv language fuel) relEnv
              language ambient.length rule source).map fun firing =>
                (index, firing)) := by
        calc
          _ = (plan.rules ambient).flatMap (fun (rule, index, premises) =>
              (applyWithCanonicalPremisesAt (rewriteAt relEnv language fuel)
                relEnv language rule ambient source premises).map fun firing =>
                  (index, firing)) := by
            apply List.flatMap_congr
            intro entry _
            rcases entry with ⟨rule, index, premises⟩
            change (applyRule (fromDepth (rewriteAt relEnv language fuel))
                relEnv language rule ambient source premises).map
                (fun firing => (index, firing)) =
              (applyWithCanonicalPremisesAt (rewriteAt relEnv language fuel)
                relEnv language rule ambient source premises).map
                (fun firing => (index, firing))
            rw [applyRule_fromDepth]
          _ = _ := compileRuleListAt?_results
            (rewriteAt relEnv language fuel) relEnv language ambient source
            language.rewrites.zipIdx (plan.rules ambient)
            (plan.checked ambient)
      have transformed := congrArg
        (List.map fun (index, firing) =>
          (RuleHistory.fire index firing.history, firing.target))
        sameRuleResults
      simpa only [List.map_flatMap, List.map_map, Function.comp_def]
        using transformed

/-- Every context-indexed bounded firing is exactly a certified derivation
tree of the authored operational presentation, and conversely. Individual
firing witnesses and their selected positions remain in the decoded history. -/
theorem contextual_firing_iff_certified (language : LanguageDef)
    (plan : AllContextRuleElaboration language) (relEnv : RelationEnv)
    (fuel : Nat) (ambient : List TypeExpr)
    (source target : Pattern) (history : RuleHistory) :
    (history, target) ∈
        rewriteWithContexts language plan relEnv fuel ambient source ↔
      ∃ tree : (presentation relEnv language).Derivation ()
          ⟨fuel, ambient.length, source, target⟩,
        CertifiedTree relEnv language _ tree ∧
          decodeHistory? relEnv language _ tree = some history := by
  rw [rewriteWithContexts_eq_depth]
  exact (certified_tree_iff_execution relEnv language fuel ambient.length
    source target history).symm

#print axioms rewriteWithContexts_eq_depth
#print axioms contextual_firing_iff_certified

end Mettapedia.OSLF.Binding.CanonicalContextFreeModel
