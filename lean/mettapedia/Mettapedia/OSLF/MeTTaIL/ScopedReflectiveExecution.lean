import Mettapedia.OSLF.MeTTaIL.ScopedRuleInstantiation
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveComparison
import Mettapedia.OSLF.MeTTaIL.ScopedMatchMonotonicity

/-!
# Source-selected reflective execution in an explicit context

The existing reflective profile selects the binder operation for the authored
rule. The shared scoped matcher retains contextual values and every match
occurrence. Literal and source-selected name comparison share the same
traversal, premise machine and binder operation. Canonical comparison changes
only repeated name-body acceptance; captured contexts and raw values remain
unchanged. Contextual interpretation of binder-opening premises is separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

open Syntax Reflection ReflectiveSubstitution RuleBinding ScopedRuleMatching

/-- Read binder activation from the source-selected reflective declaration. -/
def binderOperation (profile : ReflectionProfile) (rule : RewriteRule) :
    Pattern → Pattern → Pattern :=
  match substitutionPresentationForRule? profile rule with
  | none => Substitution.instantiateBVar
  | some declaration => ScopedRuleInstantiation.reflectiveOperation declaration

/-- Execute one authored rule without discarding its captured contexts. -/
def applyRuleAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (term : Pattern) : List Pattern :=
  ScopedRuleExecution.applyRuleWithAt (binderOperation profile rule)
    relEnv language ambient rule term

/-- Unselected rules retain ordinary binder elimination and exact answer lists. -/
theorem ordinary_of_unselected (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern)
    (unselected : substitutionPresentationForRule? profile rule = none) :
    applyRuleAt profile relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleAt relEnv language ambient rule term := by
  simp only [applyRuleAt, binderOperation, unselected]
  rfl

/-- A selected rule uses precisely that declaration's reflective operation. -/
theorem selected (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) (declaration : ReflectivePresentationDecl)
    (chosen : substitutionPresentationForRule? profile rule = some declaration) :
    applyRuleAt profile relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleWithAt
        (ScopedRuleInstantiation.reflectiveOperation declaration)
        relEnv language ambient rule term := by
  simp only [applyRuleAt, binderOperation, chosen]

/-- Output membership retains the actual matcher and ordered premise witnesses. -/
theorem mem_applyRuleAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term result : Pattern) :
    result ∈ applyRuleAt profile relEnv language ambient rule term ↔
      ∃ spec captured assignment,
        rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        captured ∈ matchRuleAt rule spec ambient term ∧
        assignment ∈ ScopedRuleExecution.completeAssignments
          relEnv language ambient rule spec captured ∧
        reductWith? (binderOperation profile rule) rule spec ambient assignment = some result :=
  ScopedRuleExecution.mem_applyRuleWithAt_iff _ _ _ _ _ _ _

/-- The authored declaration order and every matching occurrence are retained. -/
def rewriteStepAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (term : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule => applyRuleAt profile relEnv language ambient rule term

theorem mem_rewriteStepAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (term result : Pattern) :
    result ∈ rewriteStepAt profile relEnv language ambient term ↔
      ∃ rule ∈ language.rewrites,
        result ∈ applyRuleAt profile relEnv language ambient rule term :=
  List.mem_flatMap

/-- Use the authored matching presentation for name-valued captures, while
retaining the independently selected reflective binder operation. -/
def applyRuleCanonicalAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (term : Pattern) : List Pattern :=
  ScopedRuleExecution.applyRuleComparedWithAt
    (ScopedReflectiveComparison.bodyComparison profile rule)
    (binderOperation profile rule) relEnv language ambient rule term

/-- Canonical name comparison retains every literal firing in order,
including repeated identical results. -/
theorem literal_sublist_canonical (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) :
    (applyRuleAt profile relEnv language ambient rule term).Sublist
      (applyRuleCanonicalAt profile relEnv language ambient rule term) := by
  apply ScopedRuleMatching.applyRuleComparedWithAt_mono
  intro name left right accepted
  exact ScopedReflectiveComparison.bodyComparison_of_eq profile rule name
    (beq_iff_eq.mp accepted)

/-- Both source selections must be absent to recover ordinary execution:
matching and binder activation are independent declarations. -/
theorem canonical_ordinary_of_unselected (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern)
    (matchingUnselected : matchingPresentationForRule? profile rule = none)
    (substitutionUnselected : substitutionPresentationForRule? profile rule = none) :
    applyRuleCanonicalAt profile relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleAt relEnv language ambient rule term := by
  have comparison : ScopedReflectiveComparison.bodyComparison profile rule =
      literalBodyComparison := by
    funext name left right
    exact ScopedReflectiveComparison.bodyComparison_unselected profile rule
      matchingUnselected name left right
  simp only [applyRuleCanonicalAt, comparison, binderOperation, substitutionUnselected]
  rfl

/-- The result is witnessed by the actual contextual capture, ordered
premise completion and source-selected RHS instantiation. -/
theorem mem_applyRuleCanonicalAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term result : Pattern) :
    result ∈ applyRuleCanonicalAt profile relEnv language ambient rule term ↔
      ∃ spec captured assignment,
        rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        captured ∈ matchRuleWithAt
          (ScopedReflectiveComparison.bodyComparison profile rule) rule spec ambient term ∧
        assignment ∈ ScopedRuleExecution.completeAssignments
          relEnv language ambient rule spec captured ∧
        reductWith? (binderOperation profile rule) rule spec ambient assignment = some result :=
  ScopedRuleExecution.mem_applyRuleComparedWithAt_iff _ _ _ _ _ _ _ _

/-- Apply canonical name comparison in the authored declaration order. -/
def rewriteCanonicalStepAt (profile : ReflectionProfile) (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (ambient : Nat) (term : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule =>
    applyRuleCanonicalAt profile relEnv language ambient rule term

theorem mem_rewriteCanonicalStepAt_iff (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (term result : Pattern) :
    result ∈ rewriteCanonicalStepAt profile relEnv language ambient term ↔
      ∃ rule ∈ language.rewrites,
        result ∈ applyRuleCanonicalAt profile relEnv language ambient rule term :=
  List.mem_flatMap

theorem literal_rewrite_sublist_canonical (profile : ReflectionProfile)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (term : Pattern) :
    (rewriteStepAt profile relEnv language ambient term).Sublist
      (rewriteCanonicalStepAt profile relEnv language ambient term) :=
  List.Sublist.flatMap_right language.rewrites fun rule _ =>
    literal_sublist_canonical profile relEnv language ambient rule term

end Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution
