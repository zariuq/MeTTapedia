import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution

/-!
# Binder-operation independence of object-pattern rule schemas

An explicit substitution node in the authored RHS is the only site at which
the scoped interpreter invokes its binder operation. The existing object
pattern predicate excludes these nodes. Captured values still pass through
the same contextual substitution; they are not recursively executed as rule
syntax.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.ScopedInstantiationOperation

open WellSorted
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching

private theorem list_objects (patterns : List Pattern)
    (objects : isObjectPatternList patterns = true) :
    ∀ p ∈ patterns, isObjectPattern p = true := by
  induction patterns with
  | nil => simp
  | cons head tail ih =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact objects.1
      · exact ih objects.2 p member

private theorem args_agree (left right : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) (patterns : List Pattern)
    (each : ∀ p ∈ patterns, ∀ atPath,
      instantiateWith? left rule spec ambient site atPath depth assignment p =
        instantiateWith? right rule spec ambient site atPath depth assignment p) :
    instantiateArgsWith? left rule spec ambient site path depth assignment index patterns =
      instantiateArgsWith? right rule spec ambient site path depth assignment index patterns := by
  induction patterns generalizing index with
  | nil => simp only [instantiateArgsWith?]
  | cons head tail ih =>
      simp only [instantiateArgsWith?]
      rw [each head (by simp), ih (index + 1) (fun p hp => each p (by simp [hp]))]

/-- Every binder policy agrees when the authored schema has no explicit
substitution node. Free schema parameters may still carry open contextual values. -/
theorem instantiate_object_agrees (left right : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern)
    (object : isObjectPattern pattern = true) :
    instantiateWith? left rule spec ambient site path depth assignment pattern =
      instantiateWith? right rule spec ambient site path depth assignment pattern := by
  induction pattern using Pattern.inductionOn generalizing path depth with
  | hfvar name => simp only [instantiateWith?]
  | hbvar index => simp only [instantiateWith?]
  | happly constructor arguments ih =>
      simp only [instantiateWith?]
      have each := list_objects arguments object
      rw [args_agree left right rule spec ambient site path depth assignment 0 arguments
        (fun p hp atPath => ih p hp atPath depth (each p hp))]
  | hlambda binder body ih =>
      simp only [instantiateWith?, ih _ _ object]
  | hmultiLambda arity binders body ih =>
      simp only [instantiateWith?, ih _ _ object]
  | hsubst body replacement ihBody ihReplacement =>
      simp [isObjectPattern] at object
  | hcollection kind elements rest ih =>
      simp only [isObjectPattern, Bool.and_eq_true] at object
      have each := list_objects elements object.2
      simp only [instantiateWith?]
      rw [args_agree left right rule spec ambient site path depth assignment 0 elements
        (fun p hp atPath => ih p hp atPath depth (each p hp))]

/-- For a fixed capture comparison, the entire answer list is independent
of the binder operation when the authored RHS has no substitution node. -/
theorem execution_compared_object_agrees (compare : String → Pattern → Pattern → Bool)
    (left right : Pattern → Pattern → Pattern)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) (object : isObjectPattern rule.right = true) :
    ScopedRuleExecution.applyRuleComparedWithAt compare left relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleComparedWithAt compare right relEnv language ambient rule term := by
  have same : ∀ spec, reductWith? left rule spec ambient = reductWith? right rule spec ambient := by
    intro spec
    funext assignment
    exact instantiate_object_agrees left right rule spec ambient .right [] 0 assignment rule.right object
  simp only [ScopedRuleExecution.applyRuleComparedWithAt, same]

/-- Literal execution retains the same duplicate matches and premise
occurrences for every binder operation on an object-pattern RHS. -/
theorem execution_object_agrees (left right : Pattern → Pattern → Pattern)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) (object : isObjectPattern rule.right = true) :
    ScopedRuleExecution.applyRuleWithAt left relEnv language ambient rule term =
      ScopedRuleExecution.applyRuleWithAt right relEnv language ambient rule term :=
  execution_compared_object_agrees literalBodyComparison left right
    relEnv language ambient rule term object

end Mettapedia.GSLT.LanguageDef.ScopedInstantiationOperation
