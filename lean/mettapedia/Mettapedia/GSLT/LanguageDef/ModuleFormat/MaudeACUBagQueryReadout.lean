import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagQuery
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagReadout
import Mettapedia.Languages.Maude.ACUFlattenSubstitution

/-! Compiled ACU query bindings denote source substitutions. The selected
ground heads are separated from the one residual variable by permutation,
so its position in the authored target has no semantic significance.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem variable_parts (parts : List Maude.Term) :
    parts.filter (fun part => !isHead part) = (parts.filterMap componentName?).map Maude.Term.var := by
  induction parts with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | var name => simpa [isHead, componentName?] using congrArg (List.cons (Maude.Term.var name)) ih
    | app label arguments =>
      have filtered : (Maude.Term.app label arguments :: rest).filterMap componentName? =
          rest.filterMap componentName? := rfl
      rw [filtered]
      simpa only [List.filter_cons, isHead, Bool.not_true, Bool.false_eq_true, if_false] using ih

theorem parts_partition (parts : List Maude.Term) (name : String)
    (names : parts.filterMap componentName? = [name]) :
    parts.Perm (parts.filter isHead ++ [.var name]) := by
  have partition := (List.filter_append_perm isHead parts).symm
  simpa only [variable_parts, names, List.map_cons, List.map_nil] using partition

theorem prepare_fields {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (base : LanguageDef) (target : Maude.Term) {prepared : Prepared}
    (accepted : prepare operation base target = .ok prepared) :
    prepared.heads = (operation.flatten target).filter isHead ∧
      (operation.flatten target).filterMap componentName? = [prepared.variableName] ∧
      (∀ head ∈ prepared.heads, head.variables = []) ∧
      prepared.language.rewrites = [queryRule operation.declaration prepared.heads prepared.variableName] := by
  cases names : (operation.flatten target).filterMap componentName? with
  | nil => simp [prepare, names] at accepted
  | cons name rest =>
    cases rest with
    | cons other rest => simp [prepare, names] at accepted
    | nil =>
      cases ground : ((operation.flatten target).filter isHead).all (fun term => term.variables.isEmpty) with
      | false =>
        simp [prepare, names, ground] at accepted
        change Except.error _ = Except.ok prepared at accepted
        cases accepted
      | true =>
        simp [prepare, names, ground] at accepted
        split at accepted
        · cases Except.ok.inj accepted
          refine ⟨rfl, rfl, ?_, rfl⟩
          intro head member
          exact List.isEmpty_iff.mp (List.all_eq_true.mp ground head member)
        · cases accepted

def assignment {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (name : String) (residual : List Maude.Term) : Maude.Valuation :=
  fun actual => if actual = name then operation.fold residual else .var actual

theorem assignment_sorted {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (name : String) (residual : List Maude.Term) (sorted : operation.Sorted residual) :
    Maude.TypedValuation theory.signature [] [(name, operation.declaration.result)] (assignment operation name residual) := by
  intro actual sort found
  by_cases same : actual = name
  · subst actual
    have typeSame : operation.declaration.result = sort := by simpa [List.lookup] using found
    subst sort
    simpa only [assignment, if_true] using operation.fold_sorted residual sorted
  · have different : (actual == name) = false := Bool.eq_false_iff.mpr (fun equal => same (beq_iff_eq.mp equal))
    simp [List.lookup, different] at found

theorem expand_ground_parts {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (valuation : Maude.Valuation) (parts : List Maude.Term)
    (ground : ∀ part ∈ parts, part.variables = [])
    (stable : ∀ part ∈ parts, operation.flatten part = [part]) :
    parts.flatMap (fun part => operation.flatten (part.substitute valuation)) = parts := by
  induction parts with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.flatMap_cons]
    rw [Maude.Term.substitute_ground valuation first (ground first List.mem_cons_self),
      stable first List.mem_cons_self]
    exact congrArg (List.cons first) (ih
      (fun part member => ground part (List.mem_cons_of_mem first member))
      (fun part member => stable part (List.mem_cons_of_mem first member)))

theorem target_substitution {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (checked : theory.signature.check = true) (target : Maude.Term) (heads residual : List Maude.Term) (name : String)
    (partition : (operation.flatten target).Perm (heads ++ [.var name]))
    (ground : ∀ head ∈ heads, head.variables = [])
    (residualStable : ∀ term ∈ residual, operation.flatten term = [term]) :
    (operation.flatten (target.substitute (assignment operation name residual))).Perm (heads ++ residual) := by
  let expand := fun part : Maude.Term => operation.flatten (part.substitute (assignment operation name residual))
  have headsStable : ∀ head ∈ heads, operation.flatten head = [head] := fun head member =>
    operation.flatten_stable checked target head (partition.mem_iff.mpr (List.mem_append_left _ member))
  have expandedHeads : heads.flatMap expand = heads :=
    expand_ground_parts operation (assignment operation name residual) heads ground headsStable
  have expandedVariable : expand (.var name) = residual := by
    simp only [expand, Maude.Term.substitute, assignment, if_true]
    exact operation.flatten_fold checked residual residualStable
  rw [operation.flatten_substitute checked]
  have expanded := partition.flatMap_right expand
  simpa only [List.flatMap_append, expandedHeads, List.flatMap_singleton, expandedVariable] using expanded

theorem residual_authorizes_target {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (checked : theory.signature.check = true) (target : Maude.Term) (heads residual : List Maude.Term) (name : String)
    {source : Maude.Term} (sourceTyped : Maude.HasSort theory.signature [] source operation.declaration.result)
    (targetTyped : Maude.HasSort theory.signature [(name, operation.declaration.result)] target operation.declaration.result)
    (targetPartition : (operation.flatten target).Perm (heads ++ [.var name]))
    (ground : ∀ head ∈ heads, head.variables = [])
    (sourcePartition : (operation.flatten source).Perm (heads ++ residual)) :
    Maude.Equivalent theory [] operation.declaration.result source
      (target.substitute (assignment operation name residual)) := by
  have residualSorted : operation.Sorted residual := fun term member =>
    operation.flatten_sorted checked sourceTyped term (sourcePartition.mem_iff.mpr (List.mem_append_right _ member))
  have residualStable : ∀ term ∈ residual, operation.flatten term = [term] := fun term member =>
    operation.flatten_stable checked source term (sourcePartition.mem_iff.mpr (List.mem_append_right _ member))
  have instanceTyped := Maude.substitute_preserves_sort (assignment operation name residual)
    (assignment_sorted operation name residual residualSorted) targetTyped
  have instanceParts := target_substitution operation checked target heads residual name targetPartition ground residualStable
  exact operation.equivalent_of_flatten_perm checked sourceTyped instanceTyped (sourcePartition.trans instanceParts.symm)

theorem query_match_equivalent {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (checked : theory.signature.check = true) (base : LanguageDef) (target : Maude.Term)
    {prepared : Prepared} (accepted : prepare operation base target = .ok prepared)
    {rule : RewriteRule} (member : rule ∈ prepared.language.rewrites)
    {source : Maude.Term} (sourceTyped : Maude.HasSort theory.signature [] source operation.declaration.result)
    (targetTyped : Maude.HasSort theory.signature [(prepared.variableName, operation.declaration.result)]
      target operation.declaration.result)
    {ambient : Nat} {initial captured chosen : ScopedRuleMatching.Assignment}
    (matched : Matches rule (GeneralRuleBindingInference.inferredSpec rule) ambient .left [] 0 initial rule.left
      (.apply requestName [ACUBagPresentation.encodeBag operation (ACUBagCompilation.wrapperName operation.declaration) source])
      captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ residual,
      applyBindings (ordinary chosen) rule.right = .apply resultName [.collection .hashBag (residual.map encode) none] ∧
      Maude.Equivalent theory [] operation.declaration.result source
        (target.substitute (assignment operation prepared.variableName residual)) := by
  obtain ⟨headsSame, names, ground, rulesSame⟩ := prepare_fields operation base target accepted
  have ruleSame : rule = queryRule operation.declaration prepared.heads prepared.variableName := by
    simpa only [rulesSame, List.mem_singleton] using member
  subst rule
  have targetPartition : (operation.flatten target).Perm (prepared.heads ++ [.var prepared.variableName]) := by
    rw [headsSame]
    exact parts_partition (operation.flatten target) prepared.variableName names
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons first tail =>
      cases tail
      cases first with
      | constructor wrapperArguments =>
        cases wrapperArguments with
        | cons inner endArguments =>
          cases endArguments
          cases inner with
          | bag _ matchedBag =>
            obtain ⟨residual, partition, read⟩ := ACUBagReadout.bag_readout prepared.heads
              (operation.flatten source) prepared.variableName ground matchedBag later roots
            refine ⟨residual, ?_, residual_authorizes_target operation checked target prepared.heads residual
              prepared.variableName sourceTyped targetTyped targetPartition ground partition⟩
            have value : applyBindings (ordinary chosen) (.fvar prepared.variableName) =
                .collection .hashBag (residual.map encode) none := by
              rw [apply_variable, read]
              rfl
            simpa only [queryRule, applyBindings, List.map_cons, List.map_nil] using
              congrArg (fun part => Pattern.apply resultName [part]) value

#print axioms prepare_fields
#print axioms residual_authorizes_target
#print axioms query_match_equivalent

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery
