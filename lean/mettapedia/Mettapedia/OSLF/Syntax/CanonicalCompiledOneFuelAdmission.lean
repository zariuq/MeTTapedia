import Mettapedia.OSLF.Syntax.CanonicalCompiledRuleShapeAdmission
import Mettapedia.OSLF.Syntax.ResultSortedScopedFreeModel
import Mettapedia.OSLF.Syntax.CanonicalScopedOperationalClassification

/-!
# One-fuel admission from whole-language compilation

The contextual compiler checks every listed rule. Consequently a complete
one-fuel firing tree has a canonically annotated root shape. If its two
endpoints also carry the authored result type, the whole tree lifts to the
result-sorted free algebra and erases to precisely the original firing.
This theorem does not infer endpoint typing from execution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalCompiledOneFuelAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory rewriteAt)
open Mettapedia.OSLF.Binding.CanonicalCompiledRuleShapeAdmission
open Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.Binding.CanonicalScopedOperationalClassification
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext HasType)
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise (CanonicalPremise)

/-- Whole-language compilation certifies the canonical child annotation of
every complete one-fuel firing, irrespective of its selected rule. -/
theorem oneFuelCanonical_of_allCompiled
    (relEnv : RelationEnv) (language : LanguageDef)
    (ambient : List TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled :
      CanonicalScopedRuleExecution.compileRuleListAt? language ambient
        language.rewrites.zipIdx = some compiled)
    {source target : Pattern}
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv language).Derivation () ⟨1, ambient, source, target⟩) :
    OneFuelCanonical relEnv language ambient source target tree := by
  match tree with
  | .roll shape _ =>
      exact listed_shape_has_result_children relEnv language ambient
        compiled allCompiled shape

/-- A whole-language compilation and independently established endpoint
typing lift a complete one-fuel firing to the result-sorted free algebra. -/
noncomputable def admitOneFuelTreeOfCompiled
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled :
      CanonicalScopedRuleExecution.compileRuleListAt? language ambient
        language.rewrites.zipIdx = some compiled)
    {source target : Pattern}
    (sourceTyped : HasType language free ambient source resultType)
    (targetTyped : HasType language free ambient target resultType)
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv language).Derivation () ⟨1, ambient, source, target⟩) :
    (ResultSortedScopedOperationalPresentation.presentation
      relEnv language free).Derivation ()
        ⟨1, ambient, resultType, source, target⟩ :=
  admitOneFuelTree relEnv language free ambient resultType source target
    sourceTyped targetTyped tree
    (oneFuelCanonical_of_allCompiled relEnv language ambient compiled
      allCompiled tree)

/-- Erasure preserves the exact original tree, including its constructor
label, rather than merely the existence of a firing with the same endpoints. -/
theorem admitOneFuelTreeOfCompiled_erase
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled :
      CanonicalScopedRuleExecution.compileRuleListAt? language ambient
        language.rewrites.zipIdx = some compiled)
    {source target : Pattern}
    (sourceTyped : HasType language free ambient source resultType)
    (targetTyped : HasType language free ambient target resultType)
    (tree : (SortIndexedScopedOperationalPresentation.presentation
      relEnv language).Derivation () ⟨1, ambient, source, target⟩) :
    (toContextSortedFree relEnv language free).toFun ()
      ⟨1, ambient, resultType, source, target⟩
      (admitOneFuelTreeOfCompiled relEnv language free ambient resultType
        compiled allCompiled sourceTyped targetTyped tree) = tree := by
  exact admitOneFuelTree_erase relEnv language free ambient resultType
    source target sourceTyped targetTyped tree
      (oneFuelCanonical_of_allCompiled relEnv language ambient compiled
        allCompiled tree)

/-- Every selected one-fuel execution of a fully compiled language with
independently checked endpoints has a complete result-sorted firing tree.
The retained raw tree is certified against the actual evaluator; the typed
tree erases to exactly its context-sorted lift. -/
theorem runtime_oneFuel_resultSorted
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (allCompiled :
      CanonicalScopedRuleExecution.compileRuleListAt? language ambient
        language.rewrites.zipIdx = some compiled)
    {source target : Pattern} (history : RuleHistory)
    (executed : (history, target) ∈
      rewriteAt relEnv language 1 ambient.length source)
    (sourceTyped : HasType language free ambient source resultType)
    (targetTyped : HasType language free ambient target resultType) :
    ∃ rawTree : (presentation relEnv language).Derivation ()
        ⟨1, ambient.length, source, target⟩,
      ∃ typedTree :
        (ResultSortedScopedOperationalPresentation.presentation
          relEnv language free).Derivation ()
          ⟨1, ambient, resultType, source, target⟩,
        CertifiedTree relEnv language _ rawTree ∧
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          relEnv language _ rawTree = some history ∧
        (toContextSortedFree relEnv language free).toFun ()
          ⟨1, ambient, resultType, source, target⟩ typedTree =
            SortIndexedScopedTreeLifting.liftTreeAt relEnv language
              ⟨1, ambient, source, target⟩ rawTree := by
  have canonical := canonicalStage?_eq_runtime relEnv language 0 ambient
    source compiled allCompiled
  have selected : (history, target) ∈
      (canonicalStage? relEnv language 0 ambient source).getD [] := by
    rw [canonical]
    exact executed
  obtain ⟨rawTree, certified, decoded⟩ :=
    (canonicalStage?_certified_iff relEnv language 0 ambient source
      target history compiled allCompiled).mp selected
  let sorted := SortIndexedScopedTreeLifting.liftTreeAt relEnv language
    ⟨1, ambient, source, target⟩ rawTree
  let typed := admitOneFuelTreeOfCompiled relEnv language free ambient
    resultType compiled allCompiled sourceTyped targetTyped sorted
  exact ⟨rawTree, typed, certified, decoded,
    admitOneFuelTreeOfCompiled_erase relEnv language free ambient
      resultType compiled allCompiled sourceTyped targetTyped sorted⟩

#print axioms oneFuelCanonical_of_allCompiled
#print axioms admitOneFuelTreeOfCompiled
#print axioms admitOneFuelTreeOfCompiled_erase
#print axioms runtime_oneFuel_resultSorted

end Mettapedia.OSLF.Binding.CanonicalCompiledOneFuelAdmission
