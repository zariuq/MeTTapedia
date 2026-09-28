import Mettapedia.GSLT.LanguageDef.RestAwareSupportSubstitution

/-!
# Support is forced by successful partial-spine recovery

The executable matcher rejects a recovered value whose body is out of scope.
For a variable spine, its inverse assignment maps every omitted local binder
to an out-of-scope index. Scope inversion therefore proves that any accepted
target uses only selected locals, including occurrences beneath nested binders.
This discharges the support premise of the typed substitution theorem from
the actual result of the executable matcher.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

private theorem wellScoped_list_member {depth : Nat} {patterns : List Pattern}
    {pattern : Pattern}
    (hscoped : Pattern.isWellScopedListAt depth patterns = true)
    (member : pattern ∈ patterns) :
    pattern.isWellScopedAt depth = true := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at hscoped
      rcases List.mem_cons.mp member with same | rest
      · simpa [same] using hscoped.1
      · exact ih hscoped.2 rest

private theorem lift_bvar_assignment (arity : Nat) (f : Nat → Nat) :
    RawSub.lift arity (fun index => Pattern.bvar (f index)) =
      (fun index => Pattern.bvar
        (if index < arity then index else arity + f (index - arity))) := by
  funext index
  by_cases h : index < arity
  · simp [RawSub.lift, h]
  · simp [RawSub.lift, h, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
    omega

/-- A well-scoped numerical renaming cannot hide an out-of-scope image of
an outer variable occurrence, including under nested binders. -/
theorem bvar_assignment_wellScoped_used {pattern : Pattern} {index : Nat}
    (used : UsesOuterBound pattern index) :
    ∀ (f : Nat → Nat) (depth : Nat),
      (RawSub.substitute (fun v => .bvar (f v))
        pattern).isWellScopedAt depth = true → f index < depth := by
  induction used with
  | bvar index =>
      intro f depth hscoped
      simpa [RawSub.substitute, Pattern.isWellScopedAt] using hscoped
  | @apply head arguments argument index member used ih =>
      intro f depth hscoped
      simp only [RawSub.substitute, RawSub.substituteList_eq_map,
        Pattern.isWellScopedAt] at hscoped
      exact ih f depth (wellScoped_list_member hscoped (List.mem_map_of_mem member))
  | @lambda name body index used ih =>
      intro f depth hscoped
      simp only [RawSub.substitute, Pattern.isWellScopedAt] at hscoped
      rw [lift_bvar_assignment] at hscoped
      have bound := ih (fun v =>
        if v < 1 then v else 1 + f (v - 1))
        (depth + 1) hscoped
      have notLocal : ¬ index + 1 < 1 := by omega
      simp only [notLocal, ite_false, Nat.add_sub_cancel_right] at bound
      omega
  | @multiLambda arity names body index used ih =>
      intro f depth hscoped
      simp only [RawSub.substitute, Pattern.isWellScopedAt] at hscoped
      rw [lift_bvar_assignment] at hscoped
      have bound := ih (fun v =>
        if v < arity then v else arity + f (v - arity))
        (depth + arity) hscoped
      have notLocal : ¬ index + arity < arity := by omega
      simp only [notLocal, ite_false, Nat.add_sub_cancel_right] at bound
      omega
  | @substBody body replacement index used ih =>
      intro f depth hscoped
      simp only [RawSub.substitute, Pattern.isWellScopedAt,
        Bool.and_eq_true] at hscoped
      rw [lift_bvar_assignment] at hscoped
      have bound := ih (fun v =>
        if v < 1 then v else 1 + f (v - 1))
        (depth + 1) hscoped.1
      have notLocal : ¬ index + 1 < 1 := by omega
      simp only [notLocal, ite_false, Nat.add_sub_cancel_right] at bound
      omega
  | @substReplacement body replacement index used ih =>
      intro f depth hscoped
      simp only [RawSub.substitute, Pattern.isWellScopedAt,
        Bool.and_eq_true] at hscoped
      exact ih f depth hscoped.2
  | @collection kind elements rest element index member used ih =>
      intro f depth hscoped
      simp only [RawSub.substitute, RawSub.substituteList_eq_map,
        Pattern.isWellScopedAt] at hscoped
      exact ih f depth (wellScoped_list_member hscoped (List.mem_map_of_mem member))

private theorem instantiateValue?_body_scoped (value : ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) (result : Pattern)
    (h : instantiateValue? value ambient depth arguments = some result) :
    value.body.isWellScopedAt (value.dependencies.length + ambient) = true := by
  by_cases hbody : value.body.isWellScopedAt
      (value.dependencies.length + ambient) = true
  · exact hbody
  · simp [instantiateValue?, hbody] at h

private def recoveryIndex (depth dependencies ambient : Nat)
    (indices : List Nat) (index : Nat) : Nat :=
  if index < depth then
    if index ∈ indices then indices.idxOf index
    else dependencies + ambient
  else dependencies + (index - depth)

private theorem recoveryAssignment_bvar (depth dependencies ambient : Nat)
    (indices : List Nat) :
    recoveryAssignment depth dependencies ambient indices =
      (fun index => .bvar (recoveryIndex depth dependencies ambient indices index)) := by
  funext index
  simp only [recoveryAssignment, recoveryIndex]
  split_ifs <;> rfl

/-- Successful executable recovery itself proves that the captured target
does not depend on an omitted local binder. -/
theorem recoverValue?_uses_only_selected_locals
    (dependencies locals ambient : List TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (target : Pattern) (value : ContextualValue)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (recovered : recoverValue? dependencies ambient.length locals.length
      arguments target = some value) :
    UsesOnlySelectedLocals locals indices target := by
  intro index used isLocal
  have forward := recoverValue?_forward dependencies ambient.length
    locals.length arguments target value recovered
  have bodyScoped := instantiateValue?_body_scoped value ambient.length
    locals.length arguments target forward
  obtain ⟨dependenciesEq, ambientEq⟩ := recoverValue?_context
    dependencies ambient.length locals.length arguments target value recovered
  have bodyEq := recoverValue?_body_of_spine dependencies ambient.length
    locals.length arguments target indices value spineCheck recovered
  rw [dependenciesEq, bodyEq, recoveryAssignment_bvar] at bodyScoped
  have bound := bvar_assignment_wellScoped_used used
    (recoveryIndex locals.length dependencies.length ambient.length indices)
    (dependencies.length + ambient.length) bodyScoped
  unfold recoveryIndex at bound
  simp only [isLocal, ite_true] at bound
  by_contra notMember
  simp only [notMember, ite_false] at bound
  omega

/-- A successful partial-spine recovery preserves the captured result sort
without a caller-supplied support assumption. -/
theorem recoverValue?_partialSortedSpine_typed_from_success
    (language : LanguageDef) (free : FreeTypeContext)
    (dependencies locals ambient : List TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (target : Pattern) (resultType : TypeExpr) (value : ContextualValue)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : PartialSortedSpine dependencies locals indices)
    (typed : HasType language free (locals ++ ambient) target resultType)
    (recovered : recoverValue? dependencies ambient.length locals.length
      arguments target = some value) :
    ContextualValueHasType language free dependencies ambient
      resultType value := by
  exact recoverValue?_partialSortedSpine_typed language free
    dependencies locals ambient arguments indices target resultType value
    spineCheck spine
    (recoverValue?_uses_only_selected_locals dependencies locals ambient
      arguments indices target value spineCheck recovered)
    typed recovered

/-- A successful executable capture retains every stored assignment's sort
and contexts on a sort-compatible partial spine. -/
theorem capture?_partialSortedSpine_preserves_types_from_success
    (language : LanguageDef) (free : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient dependencies locals : List TypeExpr)
    (site : RulePatternSite) (path : List Nat)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (resultType : TypeExpr)
    (arguments : List Pattern) (indices : List Nat)
    (before : AssignmentHasTypes language free spec ambient initial)
    (declared : dependencies? spec name = some dependencies)
    (atSite : arguments? rule spec name site path = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : PartialSortedSpine dependencies locals indices)
    (namedType : free name = some resultType)
    (typed : HasType language free (locals ++ ambient) target resultType)
    (captured : capture? rule spec ambient.length locals.length
      site path initial name target = some final) :
    AssignmentHasTypes language free spec ambient final := by
  have existsRecovered : ∃ value,
      recoverValue? dependencies ambient.length locals.length
        arguments target = some value := by
    simp only [capture?, declared, atSite] at captured
    cases recovery : recoverValue? dependencies ambient.length
        locals.length arguments target with
    | none => simp [recovery] at captured
    | some value => exact ⟨value, rfl⟩
  obtain ⟨value, recovered⟩ := existsRecovered
  exact capture?_partialSortedSpine_preserves_types
    language free rule spec ambient dependencies locals site path
    initial final name target resultType arguments indices
    before declared atSite spineCheck spine
    (recoverValue?_uses_only_selected_locals dependencies locals ambient
      arguments indices target value spineCheck recovered)
    namedType typed captured

#print axioms bvar_assignment_wellScoped_used
#print axioms recoverValue?_uses_only_selected_locals
#print axioms recoverValue?_partialSortedSpine_typed_from_success
#print axioms capture?_partialSortedSpine_preserves_types_from_success

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
