import Mettapedia.GSLT.LanguageDef.TypedRootPremiseAssignment

/-!
# Typed recovery at a complete local-variable spine

An occurrence that supplies every local binder once, in context order, can
recover the exact supplied term as its contextual value. This includes the
binder-local target of LamCong. Partial and permuted spines require a
separate inverse-substitution typing argument.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

set_option autoImplicit false

/-- Supply each local binder exactly once, in the dependency order. -/
def fullSpine (depth : Nat) : List Pattern :=
  (List.range depth).map Pattern.bvar

private theorem mapM_bounded_indices (depth : Nat) :
    ∀ indices : List Nat,
      (∀ index ∈ indices, index < depth) →
      indices.mapM (fun index => if index < depth then some index else none) =
        some indices
  | [], _ => rfl
  | index :: rest, bounded => by
      have first : index < depth := bounded index (by simp)
      have later : ∀ next ∈ rest, next < depth := by
        intro next member
        exact bounded next (by simp [member])
      simp [first, mapM_bounded_indices depth rest later]

private theorem variableSpine?_fullSpine (depth : Nat) :
    variableSpine? depth (fullSpine depth) = some (List.range depth) := by
  have mapped := mapM_bounded_indices depth (List.range depth) (by
    intro index member
    exact List.mem_range.mp member)
  unfold variableSpine? fullSpine
  rw [List.mapM_map]
  change (do
      let indices ← (List.range depth).mapM
        (fun index => if index < depth then some index else none)
      if indices.Nodup then some indices else none) = some (List.range depth)
  rw [mapped]
  simp
  exact List.nodup_range

private theorem recoveryAssignment_fullSpine (depth ambient : Nat) :
    recoveryAssignment depth depth ambient (List.range depth) =
      Pattern.bvar := by
  funext index
  by_cases hlocal : index < depth
  · have member : index ∈ List.range depth := List.mem_range.mpr hlocal
    have rangeBound : index < (List.range depth).length := by
      simpa using hlocal
    have atIndex : (List.range depth).get ⟨index, rangeBound⟩ = index := by
      simp
    have position : (List.range depth).idxOf index = index := by
      simpa only [atIndex] using
        (List.get_idxOf List.nodup_range ⟨index, rangeBound⟩)
    simp [recoveryAssignment, hlocal, member, position]
  · simp [recoveryAssignment, hlocal]
    omega

private theorem occurrenceAssignment_fullSpine (depth : Nat) :
    occurrenceAssignment depth depth (fullSpine depth) = Pattern.bvar := by
  funext index
  by_cases hlocal : index < depth
  · simp [occurrenceAssignment, hlocal, fullSpine]
  · simp [occurrenceAssignment, hlocal]
    omega

/-- Full-spine recovery returns the supplied term itself. Its result context
is the declared dependency context followed by the caller's ambient context. -/
theorem recoverValue?_fullSpine (dependencies ambient : List TypeExpr)
    (target : Pattern)
    (hscoped : target.isWellScopedAt
      (dependencies.length + ambient.length) = true) :
    recoverValue? dependencies ambient.length dependencies.length
      (fullSpine dependencies.length) target =
      some { dependencies, ambient := ambient.length, body := target } := by
  simp only [recoverValue?, hscoped, Bool.not_true, Bool.false_eq_true, if_false]
  rw [variableSpine?_fullSpine]
  simp [recoveryAssignment_fullSpine, substitute_id,
    instantiateValue?, hscoped, occurrenceAssignment_fullSpine]
  constructor
  · simp [fullSpine]
  · intro argument membership
    obtain ⟨index, bounded, rfl⟩ := List.mem_map.mp membership
    simp at bounded
    simp [Pattern.isWellScopedAt]
    omega

/-- Sorted full-spine premise output is a typed runtime capture with its
local binder context retained, even when the output is open. -/
theorem recoverValue?_fullSpine_typed
    (language : LanguageDef) (free : FreeTypeContext)
    (dependencies ambient : List TypeExpr) (target : Pattern)
    (resultType : TypeExpr)
    (typed : HasType language free (dependencies ++ ambient)
      target resultType) :
    ∃ value, recoverValue? dependencies ambient.length dependencies.length
        (fullSpine dependencies.length) target = some value ∧
      ContextualValueHasType language free dependencies ambient
        resultType value := by
  refine ⟨{ dependencies, ambient := ambient.length, body := target }, ?_, ?_⟩
  · exact recoverValue?_fullSpine dependencies ambient target
      (by simpa [List.length_append] using typed.forget.isWellScopedAt)
  · exact ⟨rfl, rfl, typed⟩

/-- Matching at a declared complete local spine is exactly assignment of the
supplied contextual value. This states the executable behavior for both new
and repeated metavariable occurrences. -/
theorem capture?_fullSpine
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies : List TypeExpr)
    (site : RulePatternSite) (path : List Nat)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern)
    (declared : dependencies? spec name = some dependencies)
    (arguments : arguments? rule spec name site path =
      some (fullSpine dependencies.length))
    (scopedTarget : target.isWellScopedAt
      (dependencies.length + ambient.length) = true) :
    capture? rule spec ambient.length dependencies.length site path
      assignment name target =
      assign assignment name
        (ContextualValue.mk dependencies ambient.length target) := by
  simp [capture?, declared, arguments,
    recoverValue?_fullSpine dependencies ambient target scopedTarget]

/-- A repeated full-spine occurrence preserves the earlier assignment when
the recovered contextual value agrees exactly, including both contexts. -/
theorem capture?_fullSpine_repeat
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies : List TypeExpr)
    (site : RulePatternSite) (path : List Nat)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern)
    (declared : dependencies? spec name = some dependencies)
    (arguments : arguments? rule spec name site path =
      some (fullSpine dependencies.length))
    (scopedTarget : target.isWellScopedAt
      (dependencies.length + ambient.length) = true)
    (existing : lookup assignment name =
      some (ContextualValue.mk dependencies ambient.length target)) :
    capture? rule spec ambient.length dependencies.length site path
      assignment name target = some assignment := by
  rw [capture?_fullSpine rule spec ambient dependencies site path
    assignment name target declared arguments scopedTarget]
  simp [assign, existing]

/-- A repeated full-spine occurrence with a different contextual value is
rejected rather than silently replacing the first capture. -/
theorem capture?_fullSpine_conflict
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies : List TypeExpr)
    (site : RulePatternSite) (path : List Nat)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (oldValue : ContextualValue)
    (declared : dependencies? spec name = some dependencies)
    (arguments : arguments? rule spec name site path =
      some (fullSpine dependencies.length))
    (scopedTarget : target.isWellScopedAt
      (dependencies.length + ambient.length) = true)
    (existing : lookup assignment name = some oldValue)
    (different : oldValue ≠
      ContextualValue.mk dependencies ambient.length target) :
    capture? rule spec ambient.length dependencies.length site path
      assignment name target = none := by
  rw [capture?_fullSpine rule spec ambient dependencies site path
    assignment name target declared arguments scopedTarget]
  simp [assign, existing, different]

/-- The executable assignment operation preserves the typing invariant for
every old entry. A repeated name keeps the old assignment only when its new
value agrees; a fresh name stores the supplied typed value. -/
theorem assign_preserves_types
    (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (value : ContextualValue)
    (dependencies : List TypeExpr) (resultType : TypeExpr)
    (before : AssignmentHasTypes language free spec ambient initial)
    (declared : dependencies? spec name = some dependencies)
    (namedType : free name = some resultType)
    (valueTyped : ContextualValueHasType language free dependencies ambient
      resultType value)
    (assigned : assign initial name value = some final) :
    AssignmentHasTypes language free spec ambient final := by
  cases prior : lookup initial name with
  | none =>
      simp only [assign, prior] at assigned
      cases Option.some.inj assigned
      intro otherName otherValue membership
      rcases List.mem_cons.mp membership with first | older
      · obtain ⟨nameEq, valueEq⟩ := Prod.mk.inj first
        subst otherName
        subst otherValue
        exact ⟨dependencies, resultType, declared, namedType, valueTyped⟩
      · exact before otherName otherValue older
  | some oldValue =>
      by_cases equal : oldValue = value
      · simp [assign, prior, equal] at assigned
        subst final
        exact before
      · simp [assign, prior, equal] at assigned

/-- A successful fresh or repeated full-spine capture preserves every
stored value's authored type and exact two-part context. -/
theorem capture?_fullSpine_preserves_types
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies : List TypeExpr)
    (site : RulePatternSite) (path : List Nat)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (resultType : TypeExpr)
    (before : AssignmentHasTypes language free spec ambient initial)
    (declared : dependencies? spec name = some dependencies)
    (arguments : arguments? rule spec name site path =
      some (fullSpine dependencies.length))
    (namedType : free name = some resultType)
    (typed : HasType language free (dependencies ++ ambient)
      target resultType)
    (captured : capture? rule spec ambient.length dependencies.length
      site path initial name target = some final) :
    AssignmentHasTypes language free spec ambient final := by
  have scopedTarget : target.isWellScopedAt
      (dependencies.length + ambient.length) = true := by
    simpa [List.length_append] using typed.forget.isWellScopedAt
  rw [capture?_fullSpine rule spec ambient dependencies site path initial
    name target declared arguments scopedTarget] at captured
  exact assign_preserves_types language free spec ambient initial final name
    (ContextualValue.mk dependencies ambient.length target)
    dependencies resultType before declared namedType
    ⟨rfl, rfl, typed⟩ captured

/-- The actual matcher stores a fresh full-spine capture with its typed
context. The occurrence arguments and dependency declaration are taken from
the same authored rule site. -/
theorem capture?_fullSpine_fresh
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies : List TypeExpr)
    (site : RulePatternSite) (path : List Nat)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (resultType : TypeExpr)
    (declared : dependencies? spec name = some dependencies)
    (arguments : arguments? rule spec name site path =
      some (fullSpine dependencies.length))
    (fresh : lookup assignment name = none)
    (typed : HasType language free (dependencies ++ ambient)
      target resultType) :
    capture? rule spec ambient.length dependencies.length site path
      assignment name target =
      some ((name, ContextualValue.mk dependencies ambient.length target) ::
        assignment) ∧
    ContextualValueHasType language free dependencies ambient resultType
      (ContextualValue.mk dependencies ambient.length target) := by
  constructor
  · rw [capture?_fullSpine rule spec ambient dependencies site path
      assignment name target declared arguments
      (by simpa [List.length_append] using typed.forget.isWellScopedAt)]
    simp [assign, fresh]
  · exact ⟨rfl, rfl, typed⟩

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
