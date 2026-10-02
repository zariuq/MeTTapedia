import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Flatten

/-!
# Occurrence-preserving monotonicity of scoped matching

Enlarging repeated-body acceptance retains each old successful assignment
exactly. Consequently the answer list is a sublist of the enlarged matcher
result: both order and multiplicity are preserved. Dependency contexts,
ambient contexts, occurrence recovery and source-index choices remain fixed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

open Syntax RuleBinding

private theorem option_toList_sublist_of_some {α : Type*} {left right : Option α}
    (accept : ∀ value, left = some value → right = some value) :
    left.toList.Sublist right.toList := by
  cases left with
  | none => simp
  | some value => rw [accept value rfl]

private theorem flatMap_mono {α β : Type*} {left right : List α} {f g : α → List β}
    (inputs : left.Sublist right)
    (answers : ∀ value ∈ left, (f value).Sublist (g value)) :
    (left.flatMap f).Sublist (right.flatMap g) :=
  (List.Sublist.flatMap_right left answers).trans (inputs.flatMap g)

private theorem filterMap_mono {α β : Type*} {left right : List α} {f g : α → Option β}
    (inputs : left.Sublist right)
    (answers : ∀ value ∈ left, ∀ output, f value = some output → g value = some output) :
    (left.filterMap f).Sublist (right.filterMap g) := by
  rw [List.filterMap_eq_flatMap_toList, List.filterMap_eq_flatMap_toList]
  exact flatMap_mono inputs fun value member =>
    option_toList_sublist_of_some (answers value member)

variable {weaker stronger : String → Pattern → Pattern → Bool}

/-- Broader body comparison preserves each exact successful assignment.
In particular a repeated occurrence retains the earlier raw value. -/
theorem assignWith_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (assignment : Assignment) (name : String)
    (value : ContextualValue) (result : Assignment)
    (success : assignWith weaker assignment name value = some result) :
    assignWith stronger assignment name value = some result := by
  unfold assignWith at success ⊢
  cases found : lookup assignment name with
  | none => simpa only [found] using success
  | some prior =>
      simp only [found] at success ⊢
      split at success
      · rename_i accepted
        have parts := Bool.and_eq_true_iff.mp accepted
        have strongerAccepted := accept name prior.body value.body parts.2
        simp only [parts.1, strongerAccepted, Bool.and_self, if_true]
        exact success
      · cases success

/-- Lookup and occurrence recovery are unchanged; only the final repeated
body check may admit more answers. -/
theorem captureWith?_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (target : Pattern) (result : Assignment)
    (success : captureWith? weaker rule spec ambient depth site path
      assignment name target = some result) :
    captureWith? stronger rule spec ambient depth site path
      assignment name target = some result := by
  simp only [captureWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success ⊢
  obtain ⟨dependencies, declared, arguments, occurrence, value, recovered, assigned⟩ := success
  exact ⟨dependencies, declared, arguments, occurrence, value, recovered,
    assignWith_mono accept assignment name value result assigned⟩

theorem captureRestWith?_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (kind : CollType)
    (elements : List Pattern) (result : Assignment)
    (success : captureRestWith? weaker rule spec ambient depth site path
      assignment name kind elements = some result) :
    captureRestWith? stronger rule spec ambient depth site path
      assignment name kind elements = some result :=
  captureWith?_mono accept rule spec ambient depth site path assignment name
    (.collection kind elements none) result success

mutual
/-- Every old match remains at its original relative position, with the
same assignment and the same multiplicity of successful search branches. -/
theorem matchAtWith_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern target : Pattern) :
    (matchAtWith weaker rule spec ambient site path depth assignment pattern target).Sublist
      (matchAtWith stronger rule spec ambient site path depth assignment pattern target) := by
  cases pattern with
  | fvar name =>
      simp only [matchAtWith]
      exact option_toList_sublist_of_some
        (captureWith?_mono accept rule spec ambient depth site path assignment name target)
  | bvar expected => cases target <;> simp only [matchAtWith] <;> exact .refl _
  | apply constructor patterns =>
      cases target <;> (try simp only [matchAtWith]; try exact .refl _)
      rename_i actualConstructor targets
      split
      · exact matchArgsAtWith_mono accept rule spec ambient site path depth assignment
          0 patterns targets
      · exact .refl _
  | lambda binder body =>
      cases target <;> (try simp only [matchAtWith]; try exact .refl _)
      rename_i actualBinder targetBody
      exact matchAtWith_mono accept rule spec ambient site (path ++ [0]) (depth + 1)
        assignment body targetBody
  | multiLambda arity binders body =>
      cases target <;> (try simp only [matchAtWith]; try exact .refl _)
      rename_i actualArity actualBinders targetBody
      split
      · exact matchAtWith_mono accept rule spec ambient site (path ++ [0]) (depth + arity)
          assignment body targetBody
      · exact .refl _
  | subst body replacement =>
      cases target <;> (try simp only [matchAtWith]; try exact .refl _)
      rename_i targetBody targetReplacement
      exact flatMap_mono
        (matchAtWith_mono accept rule spec ambient site (path ++ [0]) (depth + 1)
          assignment body targetBody)
        (fun found _ => matchAtWith_mono accept rule spec ambient site (path ++ [1]) depth
          found replacement targetReplacement)
  | collection kind patterns rest =>
      cases target <;> (try simp only [matchAtWith]; try exact .refl _)
      rename_i actualKind targets actualRest
      rw [matchAtWith.eq_def, matchAtWith.eq_def]
      dsimp only
      split
      · split
        · cases rest with
          | none =>
              exact matchArgsAtWith_mono accept rule spec ambient site path depth
                assignment 0 patterns targets
          | some name =>
              exact filterMap_mono
                (matchArgsAtWith_mono accept rule spec ambient site path depth assignment
                  0 patterns (targets.take patterns.length))
                (fun found _ => captureRestWith?_mono accept rule spec ambient depth site
                  (path ++ [patterns.length]) found name kind (targets.drop patterns.length))
        · exact matchBagAtWith_mono accept rule spec ambient site path depth assignment
            0 patterns rest kind targets
      · exact .refl _
termination_by sizeOf pattern

/-- Ordered argument matching retains every previous intermediate answer. -/
theorem matchArgsAtWith_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) (patterns targets : List Pattern) :
    (matchArgsAtWith weaker rule spec ambient site path depth assignment index
      patterns targets).Sublist
      (matchArgsAtWith stronger rule spec ambient site path depth assignment index
        patterns targets) := by
  cases patterns with
  | nil => cases targets <;> simp only [matchArgsAtWith] <;> exact .refl _
  | cons pattern patterns =>
      cases targets with
      | nil => simp only [matchArgsAtWith]; exact .refl _
      | cons target targets =>
          simp only [matchArgsAtWith]
          exact flatMap_mono
            (matchAtWith_mono accept rule spec ambient site (path ++ [index]) depth
              assignment pattern target)
            (fun found _ => matchArgsAtWith_mono accept rule spec ambient site path depth
              found (index + 1) patterns targets)
termination_by sizeOf patterns

/-- Bag search keeps the same source index enumeration and erases the same
chosen occurrence in each retained branch. No permutation or deduplication
of answers is used. -/
theorem matchBagAtWith_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) (patterns : List Pattern)
    (rest : Option String) (kind : CollType) (targets : List Pattern) :
    (matchBagAtWith weaker rule spec ambient site path depth assignment index
      patterns rest kind targets).Sublist
      (matchBagAtWith stronger rule spec ambient site path depth assignment index
        patterns rest kind targets) := by
  cases patterns with
  | nil =>
      cases rest with
      | none => simp only [matchBagAtWith]; exact .refl _
      | some name =>
          simp only [matchBagAtWith]
          exact option_toList_sublist_of_some
            (captureRestWith?_mono accept rule spec ambient depth site (path ++ [index])
              assignment name kind targets)
  | cons pattern patterns =>
      simp only [matchBagAtWith]
      apply List.Sublist.flatMap_right
      intro choice _
      obtain ⟨target, selected⟩ := choice
      exact flatMap_mono
        (matchAtWith_mono accept rule spec ambient site (path ++ [index]) depth
          assignment pattern target)
        (fun found _ => matchBagAtWith_mono accept rule spec ambient site path depth
          found (index + 1) patterns rest kind (targets.eraseIdx selected))
termination_by sizeOf patterns
end

theorem matchRuleWithAt_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (target : Pattern) :
    (matchRuleWithAt weaker rule spec ambient target).Sublist
      (matchRuleWithAt stronger rule spec ambient target) :=
  matchAtWith_mono accept rule spec ambient .left [] 0 [] rule.left target

/-- With the same binder operation and premise interpreter, enlarging the
matcher retains the ordered list of existing executable reduct occurrences. -/
theorem applyRuleComparedWithAt_mono
    (accept : ∀ name left right, weaker name left right = true →
      stronger name left right = true) (operation : Pattern → Pattern → Pattern)
    (relEnv : Engine.RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) :
    (ScopedRuleExecution.applyRuleComparedWithAt weaker operation relEnv language
      ambient rule term).Sublist
      (ScopedRuleExecution.applyRuleComparedWithAt stronger operation relEnv language
        ambient rule term) := by
  unfold ScopedRuleExecution.applyRuleComparedWithAt
  cases bindings : rule.bindings with
  | none => exact .refl _
  | some spec =>
      by_cases ready : admittedFor rule spec = true
      · simp only [ready, if_true]
        exact (matchRuleWithAt_mono accept rule spec ambient term).flatMap _
      · simp only [ready]
        exact .refl _

end Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
