import Mettapedia.OSLF.Syntax.LambdaAuthoredAppCongExecutionComparison
import Mettapedia.OSLF.Syntax.CanonicalScopedOperationalClassification

/-!
# Canonical compilation and certified free firings for the four lambda rules

All four authored lambda declarations compile at every ambient type context.
The general canonical-layer and certified-tree comparison therefore applies
without an uninstantiated compilation premise. It retains the rule order,
premise histories, and selected oracle occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredCanonicalFreeComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison
open Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution
open Mettapedia.OSLF.Binding.CanonicalScopedOperationalClassification
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory rewriteAt)
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise (CanonicalPremise)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule lamCongRule localStep)

/-- Every declaration of the exact four-rule language compiles at any
ambient type context. The explicit binder-local step remains at position one. -/
theorem all_rules_compile (ambient : List TypeExpr) :
    compileRuleListAt? language ambient language.rewrites.zipIdx =
      some [(betaRule, 0, []),
            (lamCongRule, 1, [.step localStep]),
            (appCongLRule, 2, [.step appCongLStep]),
            (appCongRRule, 3, [.step appCongRStep])] := by
  rfl

/-- Canonical checking of the actual declaration preserves the complete
ordered runtime list at every ambient context and every fuel. -/
theorem canonical_stage_eq_runtime
    (fuel : Nat) (ambient : List TypeExpr) (source : Pattern) :
    canonicalStage? RelationEnv.empty language fuel ambient source =
      some (rewriteAt RelationEnv.empty language (fuel + 1)
        ambient.length source) :=
  canonicalStage?_eq_runtime RelationEnv.empty language fuel ambient source
    _ (all_rules_compile ambient)

/-- A selected authored runtime history is exactly a certified firing tree
in the generic free rule algebra for this same four-rule declaration. -/
theorem certified_iff_authored
    (fuel : Nat) (ambient : List TypeExpr)
    (source target : Pattern) (history : RuleHistory) :
    (history, target) ∈
      rewriteAt RelationEnv.empty language (fuel + 1)
        ambient.length source ↔
      ∃ tree : (presentation RelationEnv.empty language).Derivation ()
          ⟨fuel + 1, ambient.length, source, target⟩,
        CertifiedTree RelationEnv.empty language _ tree ∧
          Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
            RelationEnv.empty language _ tree = some history := by
  have h := canonicalStage?_certified_iff RelationEnv.empty language fuel
    ambient source target history _ (all_rules_compile ambient)
  simpa only [canonical_stage_eq_runtime, Option.getD_some] using h

/-- The actual beta-under-left-application execution yields a certified
two-node free firing tree with its complete nested history. -/
theorem beta_under_appL_certified {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨2, Γ.length,
          encodeTerm (appT (appT (lamT body) argument) outer),
          encodeTerm (appT (inst body argument) outer)⟩,
      CertifiedTree RelationEnv.empty language _ tree ∧
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language _ tree =
            some (.fire 2 [.step 0 0 (.fire 0 [])]) := by
  have executed := beta_under_appL body argument outer
  have hlen : (List.replicate Γ.length (TypeExpr.base "Term")).length =
      Γ.length := List.length_replicate
  have executed' :
      (.fire 2 [.step 0 0 (.fire 0 [])],
        encodeTerm (appT (inst body argument) outer)) ∈
        rewriteAt RelationEnv.empty language 2
          (List.replicate Γ.length (TypeExpr.base "Term")).length
          (encodeTerm (appT (appT (lamT body) argument) outer)) := by
    rw [hlen]
    exact executed
  have classified := (certified_iff_authored 1
    (List.replicate Γ.length (.base "Term"))
    (encodeTerm (appT (appT (lamT body) argument) outer))
    (encodeTerm (appT (inst body argument) outer))
    (.fire 2 [.step 0 0 (.fire 0 [])])).mp executed'
  rw [hlen] at classified
  exact classified

/-- Right-application congruence has a different outer constructor and
remains a distinct certified firing even with the same beta child. -/
theorem beta_under_appR_certified {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument outer : Term sig Γ .term) :
    ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨2, Γ.length,
          encodeTerm (appT outer (appT (lamT body) argument)),
          encodeTerm (appT outer (inst body argument))⟩,
      CertifiedTree RelationEnv.empty language _ tree ∧
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language _ tree =
            some (.fire 3 [.step 0 0 (.fire 0 [])]) := by
  have executed := beta_under_appR body argument outer
  have hlen : (List.replicate Γ.length (TypeExpr.base "Term")).length =
      Γ.length := List.length_replicate
  have executed' :
      (.fire 3 [.step 0 0 (.fire 0 [])],
        encodeTerm (appT outer (inst body argument))) ∈
        rewriteAt RelationEnv.empty language 2
          (List.replicate Γ.length (TypeExpr.base "Term")).length
          (encodeTerm (appT outer (appT (lamT body) argument))) := by
    rw [hlen]
    exact executed
  have classified := (certified_iff_authored 1
    (List.replicate Γ.length (.base "Term"))
    (encodeTerm (appT outer (appT (lamT body) argument)))
    (encodeTerm (appT outer (inst body argument)))
    (.fire 3 [.step 0 0 (.fire 0 [])])).mp executed'
  rw [hlen] at classified
  exact classified

/-- A candidate carrying LamCong's rule index cannot certify the only
one-fuel firing of an intrinsic beta redex. -/
theorem beta_wrong_rule_not_certified {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    ¬ ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨1, Γ.length,
          encodeTerm (appT (lamT body) argument),
          encodeTerm (inst body argument)⟩,
      CertifiedTree RelationEnv.empty language _ tree ∧
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language _ tree = some (.fire 1 []) := by
  intro certified
  have hlen : (List.replicate Γ.length (TypeExpr.base "Term")).length =
      Γ.length := List.length_replicate
  have certified' :
      ∃ tree : (presentation RelationEnv.empty language).Derivation ()
          ⟨1, (List.replicate Γ.length (TypeExpr.base "Term")).length,
            encodeTerm (appT (lamT body) argument),
            encodeTerm (inst body argument)⟩,
        CertifiedTree RelationEnv.empty language _ tree ∧
          Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
            RelationEnv.empty language _ tree = some (.fire 1 []) := by
    rw [hlen]
    exact certified
  have executed := (certified_iff_authored 0
    (List.replicate Γ.length (.base "Term"))
    (encodeTerm (appT (lamT body) argument))
    (encodeTerm (inst body argument)) (.fire 1 [])).mpr certified'
  rw [hlen] at executed
  rw [full_beta_one_step body argument] at executed
  simp at executed

#print axioms all_rules_compile
#print axioms canonical_stage_eq_runtime
#print axioms certified_iff_authored
#print axioms beta_under_appL_certified
#print axioms beta_under_appR_certified
#print axioms beta_wrong_rule_not_certified

end Mettapedia.OSLF.Binding.LambdaAuthoredCanonicalFreeComparison
