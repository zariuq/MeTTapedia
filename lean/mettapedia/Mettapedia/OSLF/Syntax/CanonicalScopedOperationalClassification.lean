import Mettapedia.OSLF.Syntax.CanonicalScopedRuleExecution
import Mettapedia.OSLF.Syntax.ScopedOperationalCertification

/-!
# Canonical scoped execution and certified free rule evidence

At one bounded rule layer, the checked canonical premise list has exactly
the same ordered histories as the authored scoped executor. The existing
certified-tree theorem then identifies precisely which free rule trees are
actual executions. This comparison is conditional on successful compilation
in the stated ambient context; nested calls use the already established
scoped executor and require their own contextual compilation judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalScopedOperationalClassification

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.OSLF.Binding.ScopedOperationalCertification

/-- One canonical layer uses the current recursive oracle but elaborates
every rule premise in the explicitly supplied ambient type context. -/
def canonicalStage? (relEnv : RelationEnv) (language : LanguageDef)
    (fuel : Nat) (ambient : List TypeExpr) (source : Pattern) :
    Option (List (RuleHistory × Pattern)) :=
  (applyCompiledLanguageAt? (rewriteAt relEnv language fuel)
    relEnv language ambient source).map fun results =>
      results.map fun (index, firing) =>
        (.fire index firing.history, firing.target)

/-- A successfully compiled canonical layer is equal as an ordered list to
the actual next runtime layer. No equal endpoints or histories are merged. -/
theorem canonicalStage?_eq_runtime
    (relEnv : RelationEnv) (language : LanguageDef)
    (fuel : Nat) (ambient : List TypeExpr) (source : Pattern)
    (compiled : List (RewriteRule × Nat ×
      List Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.CanonicalPremise))
    (h : compileRuleListAt? language ambient
      language.rewrites.zipIdx = some compiled) :
    canonicalStage? relEnv language fuel ambient source =
      some (rewriteAt relEnv language (fuel + 1) ambient.length source) := by
  unfold canonicalStage?
  rw [applyCompiledLanguageAt?_eq
    (rewriteAt relEnv language fuel) relEnv language ambient source
    compiled h]
  simp only [Option.map_some]
  simp only [rewriteAt, List.map_flatMap, List.map_map]
  congr 1

/-- The certified fragment of the free scoped rule algebra recognizes
exactly the histories emitted by a compiled canonical layer. -/
theorem canonicalStage?_certified_iff
    (relEnv : RelationEnv) (language : LanguageDef)
    (fuel : Nat) (ambient : List TypeExpr) (source target : Pattern)
    (history : RuleHistory)
    (compiled : List (RewriteRule × Nat ×
      List Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.CanonicalPremise))
    (h : compileRuleListAt? language ambient
      language.rewrites.zipIdx = some compiled) :
    (history, target) ∈
        (canonicalStage? relEnv language fuel ambient source).getD [] ↔
      ∃ tree : (presentation relEnv language).Derivation ()
          ⟨fuel + 1, ambient.length, source, target⟩,
        CertifiedTree relEnv language _ tree ∧
          decodeHistory? relEnv language _ tree = some history := by
  rw [canonicalStage?_eq_runtime relEnv language fuel ambient source
    compiled h]
  exact (certified_tree_iff_execution relEnv language
    (fuel + 1) ambient.length source target history).symm

#print axioms canonicalStage?_eq_runtime
#print axioms canonicalStage?_certified_iff

end Mettapedia.OSLF.Binding.CanonicalScopedOperationalClassification
