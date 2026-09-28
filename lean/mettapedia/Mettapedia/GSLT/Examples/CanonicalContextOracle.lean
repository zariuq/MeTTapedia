import Mettapedia.OSLF.Syntax.CanonicalContextOracle
import Mettapedia.OSLF.Syntax.CanonicalContextFreeModel
import Mettapedia.GSLT.Examples.CanonicalScopedRuleExecution

/-!
# The authored lambda rule with a sorted recursive premise query

The lambda congruence rule asks for an inner beta step in the sort context
introduced by its binder. A context-indexed oracle can check that sort. Its
answer carries the same open bound variable into the outer reduct.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.CanonicalContextOracle

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory)
open Mettapedia.OSLF.Binding.CanonicalContextOracle
open Mettapedia.OSLF.Binding.CanonicalContextFreeModel
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-- Beta answers only when the caller supplies the actual term-binder sort. -/
def sortedBetaOracle : ContextOracle Unit :=
  fun context source =>
    if context = [.base "Term"] then betaOracle context.length source else []

theorem sorted_beta_open :
    sortedBetaOracle [.base "Term"] openRedex = [((), .bvar 0)] := by
  simpa [sortedBetaOracle] using inner_beta_open

theorem sorted_beta_other_sort :
    sortedBetaOracle [.base "Other"] openRedex = [] := by
  decide +kernel

/-- The actual lambda oracle's sort check cannot be implemented by the
previous depth-only interface, even though both queried contexts have one
variable. -/
theorem sorted_beta_not_fromDepth :
    ¬ ∃ depthOracle : Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.StepOracle Unit,
      fromDepth depthOracle = sortedBetaOracle := by
  rintro ⟨depthOracle, equality⟩
  have same := fromDepth_eq_of_length_eq depthOracle
    (first := [.base "Term"]) (second := [.base "Other"]) rfl
    openRedex
  rw [equality, sorted_beta_open, sorted_beta_other_sort] at same
  cases same

/-- The authored LamCong rule really consumes the sorted inner beta answer.
Its open result remains inside the outer lambda rather than escaping. -/
theorem compiled_lamCong_keeps_bound_variable :
    ∃ firings firing,
      applyCompiledRuleAt? sortedBetaOracle RelationEnv.empty language
        lamCongRule [] wrappedRedex = some firings ∧
      firing ∈ firings ∧ firing.target = wrappedTarget ∧
      firing.history.length = 1 := by
  have same :
      applyCompiledRuleAt? sortedBetaOracle RelationEnv.empty language
        lamCongRule [] wrappedRedex =
      applyCompiledRuleAt? (fromDepth betaOracle) RelationEnv.empty
        language lamCongRule [] wrappedRedex := by
    decide +kernel
  have compiled :
      Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution.compileRulePremisesAt?
        language lamCongRule [] =
        some [.step localStep] := by
    simpa only [Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution.compileRulePremisesAt?_root]
      using lamCong_premise_compiles
  have old := Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution.applyCompiledRuleAt?_eq
    betaOracle RelationEnv.empty language lamCongRule [] wrappedRedex
    [.step localStep] compiled
  obtain ⟨firing, selected, targetEq, historyLength⟩ :=
    lamCong_executes_open
  exact ⟨_, firing, same.trans
    ((applyCompiledRuleAt?_fromDepth betaOracle RelationEnv.empty language
      lamCongRule [] wrappedRedex).trans old), selected,
    targetEq, historyLength⟩

/-- At the whole-language boundary, sort erasure preserves the exact
authored rule order and all proof-relevant one-layer firings. -/
theorem lambda_language_fromDepth (source : Pattern) :
    applyCompiledLanguageAt? (fromDepth betaOracle) RelationEnv.empty
        language [] source =
      some (language.rewrites.zipIdx.flatMap fun (rule, index) =>
        (Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.applyRuleWithOracle
          betaOracle RelationEnv.empty language 0 rule source).map
          fun firing => (index, firing)) := by
  rw [applyCompiledLanguageAt?_fromDepth]
  exact Mettapedia.GSLT.Examples.CanonicalScopedRuleExecution.lambda_language_compiled_firings
    betaOracle source

/-- The actual beta and LamCong declarations elaborate in every ambient
sort context. Their premise-local binder remains the term sort. -/
theorem lambda_rules_compile_all (ambient : List TypeExpr) :
    Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution.compileRuleListAt?
        language ambient language.rewrites.zipIdx =
      some [(betaRule, 0, []),
        (lamCongRule, 1, [.step localStep])] := by
  rfl

/-- A total checked elaboration plan for the authored lambda language. -/
def lambdaPlan : AllContextRuleElaboration language where
  rules := fun _ => [(betaRule, 0, []),
    (lamCongRule, 1, [.step localStep])]
  checked := lambda_rules_compile_all

/-- Recursive, context-indexed execution of the authored lambda language
has the exact existing two-layer free firing tree, with bound variables and
premise evidence preserved. -/
theorem lambda_recursive_contextual_comparison
    (fuel : Nat) (ambient : List TypeExpr) (source : Pattern) :
    rewriteWithContexts language lambdaPlan RelationEnv.empty fuel ambient
        source =
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        RelationEnv.empty language fuel ambient.length source := by
  exact rewriteWithContexts_eq_depth language lambdaPlan RelationEnv.empty
    fuel ambient source

/-- The contextual free tree reaches the open LamCong result at fuel two;
one layer cannot discharge its recursive beta premise. -/
theorem contextual_lamCong_requires_two_layers :
    ((rewriteWithContexts language lambdaPlan RelationEnv.empty 1 []
      wrappedRedex).map Prod.snd) = [] ∧
    wrappedTarget ∈
      ((rewriteWithContexts language lambdaPlan RelationEnv.empty 2 []
        wrappedRedex).map Prod.snd) := by
  simpa only [lambda_recursive_contextual_comparison, List.length_nil] using
    lamCong_requires_two_layers

/-- The result carries the exact outer LamCong and inner Beta constructor
tree, including the selected premise and oracle-result positions. -/
theorem contextual_lamCong_tree_shape :
    (rewriteWithContexts language lambdaPlan RelationEnv.empty 2 []
      wrappedRedex).map
        (fun (history, target) =>
          (lamCongBetaHistory history, target == wrappedTarget)) =
      [(true, true)] := by
  simpa only [lambda_recursive_contextual_comparison, List.length_nil] using
    lamCong_tree_shape

/-- For this authored lambda language, contextual execution and certified
free derivation trees classify exactly the same individual histories. -/
theorem lambda_contextual_firing_iff_certified
    (fuel : Nat) (ambient : List TypeExpr)
    (source target : Pattern) (history : RuleHistory) :
    (history, target) ∈
        rewriteWithContexts language lambdaPlan RelationEnv.empty fuel
          ambient source ↔
      ∃ tree : (presentation RelationEnv.empty language).Derivation ()
          ⟨fuel, ambient.length, source, target⟩,
        CertifiedTree RelationEnv.empty language _ tree ∧
          decodeHistory? RelationEnv.empty language _ tree = some history := by
  exact contextual_firing_iff_certified language lambdaPlan
    RelationEnv.empty fuel ambient source target history

#print axioms sorted_beta_open
#print axioms sorted_beta_other_sort
#print axioms sorted_beta_not_fromDepth
#print axioms compiled_lamCong_keeps_bound_variable
#print axioms lambda_language_fromDepth
#print axioms lambda_recursive_contextual_comparison
#print axioms contextual_lamCong_tree_shape
#print axioms lambda_contextual_firing_iff_certified

end Mettapedia.GSLT.Examples.CanonicalContextOracle
