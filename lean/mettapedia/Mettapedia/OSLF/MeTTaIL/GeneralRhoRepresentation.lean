import Mettapedia.OSLF.MeTTaIL.GeneralRhoTyping

/-!
# Object representation through the selected reflective operation

These structural laws retain canonical binder metadata and exclude pending
schema substitutions and open tails. They are independent of scoped typing
and apply to every reflective declaration on the shared Pattern carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Substitution ReflectiveSubstitution ReflectiveInstantiation

def Represented (pattern : Pattern) : Prop :=
  pattern.hasCanonicalBinderMetadata = true ∧ isObjectPattern pattern = true

private theorem objectList_iff (patterns : List Pattern) :
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons head tail ih => simp [isObjectPatternList, ih]

theorem represented_apply_iff (constructor : String) (arguments : List Pattern) :
    Represented (.apply constructor arguments) ↔ ∀ pattern ∈ arguments, Represented pattern := by
  simp only [Represented, Pattern.hasCanonicalBinderMetadata, isObjectPattern,
    Pattern.hasCanonicalBinderMetadataList_eq_true_iff, objectList_iff]
  constructor
  · rintro ⟨metadata, objects⟩ pattern member
    exact ⟨metadata pattern member, objects pattern member⟩
  · intro represented
    exact ⟨fun p hp => (represented p hp).1, fun p hp => (represented p hp).2⟩

theorem represented_collection_iff (kind : CollType) (elements : List Pattern) :
    Represented (.collection kind elements none) ↔ ∀ pattern ∈ elements, Represented pattern := by
  simpa only [Represented, Pattern.hasCanonicalBinderMetadata, isObjectPattern,
    Option.isNone_none, Bool.true_and] using represented_apply_iff "" elements

theorem lift_represented (cutoff shift : Nat) {pattern : Pattern}
    (represented : Represented pattern) : Represented (liftBVars cutoff shift pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      unfold liftBVars
      split <;> exact ⟨rfl, rfl⟩
  | hfvar name => exact represented
  | happly constructor arguments ih =>
      apply (represented_apply_iff _ _).mpr
      rw [liftBVarsList_eq_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember cutoff ((represented_apply_iff _ _).mp represented original sourceMember)
  | hlambda binder body ih =>
      simp only [liftBVars, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at represented ⊢
      have result := ih (cutoff + 1) ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [liftBVars, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at represented ⊢
      have result := ih (cutoff + arity) ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hsubst body replacement _ _ => simp [Represented, isObjectPattern] at represented
  | hcollection kind elements rest ih =>
      have restNone : rest = none := by
        cases rest <;> simp_all [Represented, isObjectPattern]
      subst rest
      apply (represented_collection_iff _ _).mpr
      rw [liftBVarsList_eq_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember cutoff ((represented_collection_iff _ _).mp represented original sourceMember)

private theorem instantiate_variable_represented (depth : Nat) {replacement : Pattern}
    (represented : Represented replacement) (index : Nat) :
    Represented (instantiateBVarAt depth replacement (.bvar index)) := by
  unfold instantiateBVarAt
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact lift_represented 0 depth represented
    · exact ⟨rfl, rfl⟩

private theorem finish_represented (declaration : ReflectivePresentationDecl)
    (constructor : String) {arguments : List Pattern}
    (represented : ∀ pattern ∈ arguments, Represented pattern) :
    Represented (finishNormalizeReflectiveApply declaration constructor arguments) := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · rename_i drop name
      split
      · exact (represented_apply_iff drop [name]).mp (represented _ (by simp)) name (by simp)
      · exact (represented_apply_iff _ _).mpr represented
    · exact (represented_apply_iff _ _).mpr represented
  · exact (represented_apply_iff _ _).mpr represented

private theorem normalize_list_map (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    normalizeReflectiveList declaration patterns = patterns.map (normalizeReflective declaration) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [normalizeReflectiveList, ih]

theorem normalize_represented (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (represented : Represented pattern) : Represented (normalizeReflective declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ | hfvar _ => exact represented
  | happly constructor arguments ih =>
      apply finish_represented
      rw [normalize_list_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember ((represented_apply_iff _ _).mp represented original sourceMember)
  | hlambda binder body ih =>
      simp only [normalizeReflective, Represented, Pattern.hasCanonicalBinderMetadata,
        Bool.and_eq_true, isObjectPattern] at represented ⊢
      have result := ih ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [normalizeReflective, Represented, Pattern.hasCanonicalBinderMetadata,
        Bool.and_eq_true, isObjectPattern] at represented ⊢
      have result := ih ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hsubst _ _ _ _ => simp [Represented, isObjectPattern] at represented
  | hcollection kind elements rest ih =>
      have restNone : rest = none := by cases rest <;> simp_all [Represented, isObjectPattern]
      subst rest
      apply (represented_collection_iff _ _).mpr
      rw [normalize_list_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember ((represented_collection_iff _ _).mp represented original sourceMember)

private theorem leaves_represented (declaration : ReflectivePresentationDecl) {pattern member : Pattern}
    (represented : Represented pattern) (membership : member ∈ parallelLeaves declaration pattern) :
    Represented member := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact represented
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            exact ih element elementMember
              ((represented_collection_iff _ _).mp represented element elementMember) membership
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            subst membership; exact represented
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            subst membership; exact represented
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact represented
  | hbvar index => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact represented
  | hfvar name => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact represented
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact represented
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact represented
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact represented

private theorem resolve_represented (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (represented : Represented pattern) : Represented (resolveQuotes declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ | hfvar _ => exact represented
  | happly constructor arguments ih =>
      have each := (represented_apply_iff _ _).mp represented
      have mapped : ∀ pattern ∈ arguments.map (resolveQuotes declaration), Represented pattern := by
        rintro result member
        obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
        exact ih original sourceMember (each original sourceMember)
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      generalize arguments.map (resolveQuotes declaration) = resolved at mapped
      match resolved, mapped with
      | [], _ => exact ⟨rfl, rfl⟩
      | first :: second :: rest, mapped => exact (represented_apply_iff _ _).mpr mapped
      | [payload], mapped =>
          simp only [finishResolveApply]
          split
          · split
            · rename_i name exposed
              have dropRepresented := leaves_represented declaration (mapped payload (by simp))
                (by rw [ReflectiveCoherent.exposedDrop?_eq_some_iff.mp exposed]; exact List.mem_singleton_self _)
              exact (represented_apply_iff _ _).mp dropRepresented name (by simp)
            · exact (represented_apply_iff _ _).mpr mapped
          · exact (represented_apply_iff _ _).mpr mapped
  | hlambda binder body ih =>
      simp only [resolveQuotes, Represented, Pattern.hasCanonicalBinderMetadata,
        Bool.and_eq_true, isObjectPattern] at represented ⊢
      have result := ih ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [resolveQuotes, Represented, Pattern.hasCanonicalBinderMetadata,
        Bool.and_eq_true, isObjectPattern] at represented ⊢
      have result := ih ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hsubst _ _ _ _ => simp [Represented, isObjectPattern] at represented
  | hcollection kind elements rest ih =>
      have restNone : rest = none := by cases rest <;> simp_all [Represented, isObjectPattern]
      subst rest
      apply (represented_collection_iff _ _).mpr
      simp only [resolveQuotesList_eq_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember ((represented_collection_iff _ _).mp represented original sourceMember)

private theorem receive_represented (declaration : ReflectivePresentationDecl) (constructor : String)
    {name : Pattern} (represented : Represented name) :
    Represented (receive declaration constructor name) := by
  rcases ReflectiveCoherent.receive_cases (declaration := declaration) constructor name with
    plain | ⟨process, rfl, ran⟩
  · rw [plain]; exact (represented_apply_iff _ _).mpr (by simpa using represented)
  · rw [ran]; exact (represented_apply_iff _ _).mp represented process (by simp)

theorem instantiate_represented (declaration : ReflectivePresentationDecl) (depth : Nat)
    {replacement pattern : Pattern} (replacementRepresented : Represented replacement)
    (represented : Represented pattern) :
    Represented (instantiate declaration depth replacement pattern) := by
  unfold instantiate
  have resolved := resolve_represented declaration represented
  generalize resolveQuotes declaration pattern = body at resolved
  clear represented pattern
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index => exact instantiate_variable_represented depth replacementRepresented index
  | hfvar _ => exact resolved
  | happly constructor arguments ih =>
      have each := (represented_apply_iff _ _).mp resolved
      match arguments, each, resolved, ih with
      | [], _, resolved, _ => exact resolved
      | first :: second :: rest, each, _, ih =>
          simp only [substituteResolved, substituteResolvedList_eq_map]
          apply (represented_apply_iff _ _).mpr
          rintro result member
          obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
          exact ih original sourceMember depth (each original sourceMember)
      | [payload], each, resolved, ih =>
          have through : Represented (.apply constructor [substituteResolved declaration
              (fun level index => instantiateBVarAt level replacement (.bvar index)) depth payload]) :=
            (represented_apply_iff _ _).mpr (by simpa using ih payload (by simp) depth (each payload (by simp)))
          simp only [substituteResolved]
          split
          · exact resolved
          · split
            · split
              · exact receive_represented declaration constructor
                  (instantiate_variable_represented depth replacementRepresented depth)
              · exact through
            · exact through
  | hlambda binder body ih =>
      simp only [substituteResolved, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at resolved ⊢
      have result := ih (depth + 1) ⟨resolved.1.2, resolved.2⟩
      exact ⟨⟨resolved.1.1, result.1⟩, result.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [substituteResolved, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at resolved ⊢
      have result := ih (depth + arity) ⟨resolved.1.2, resolved.2⟩
      exact ⟨⟨resolved.1.1, result.1⟩, result.2⟩
  | hsubst _ _ _ _ => simp [Represented, isObjectPattern] at resolved
  | hcollection kind elements rest ih =>
      have restNone : rest = none := by cases rest <;> simp_all [Represented, isObjectPattern]
      subst rest
      apply (represented_collection_iff _ _).mpr
      simp only [substituteResolvedList_eq_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember depth ((represented_collection_iff _ _).mp resolved original sourceMember)

open DerivedPresentationSyntax

mutual
theorem derived_name_data {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name) : HasType language (typeFree free) (typeBound bound) name (.base "Name") ∧ Represented name := by
  refine ⟨derived_name_typed typed, ?_⟩
  cases typed with
  | bvar _ | fvar _ => exact ⟨rfl, rfl⟩
  | quote process =>
      apply (represented_apply_iff _ _).mpr
      simpa using (derived_process_data process).2
termination_by sizeOf name

theorem derived_process_data {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) : HasType language (typeFree free) (typeBound bound) process (.base "Proc") ∧ Represented process := by
  refine ⟨derived_process_typed typed, ?_⟩
  cases typed with
  | bvar _ | fvar _ | unit => exact ⟨rfl, rfl⟩
  | drop name =>
      apply (represented_apply_iff _ _).mpr
      simpa using (derived_name_data name).2
  | output channel payload =>
      apply (represented_apply_iff _ _).mpr
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro pattern (rfl | rfl)
      · exact (derived_name_data channel).2
      · exact (derived_process_data payload).2
  | input channel body =>
      apply (represented_apply_iff _ _).mpr
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro pattern (rfl | rfl)
      · exact (derived_name_data channel).2
      · simpa [Represented, Pattern.hasCanonicalBinderMetadata, isObjectPattern] using
          (derived_process_data body).2
  | parallel processes =>
      exact (represented_collection_iff _ _).mpr ((derived_processes_data processes).2)
termination_by sizeOf process

theorem derived_processes_data {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound processes) :
    ElementsHaveType language (typeFree free) (typeBound bound) processes (.base "Proc") ∧
      (∀ process ∈ processes, Represented process) := by
  refine ⟨derived_processes_typed typed, ?_⟩
  cases typed with
  | nil => simp
  | cons process processes =>
      simp only [List.mem_cons]
      rintro pattern (rfl | member)
      · exact (derived_process_data process).2
      · exact (derived_processes_data processes).2 pattern member
termination_by sizeOf processes
end

theorem derived_name_represented {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name) : Represented name :=
  (derived_name_data typed).2

theorem derived_process_represented {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) : Represented process :=
  (derived_process_data typed).2

theorem derived_processes_represented {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound processes) :
    ∀ process ∈ processes, Represented process := (derived_processes_data typed).2

theorem derived_name_open {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name) :
    OpenPatternWellSorted language (typeFree free) (typeBound bound) (.base "Name") name :=
  ⟨derived_name_typed typed, (derived_name_represented typed).1,
    (derived_name_represented typed).2, (derived_name_typed typed).isWellScopedAt⟩

theorem derived_process_open {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    OpenPatternWellSorted language (typeFree free) (typeBound bound) (.base "Proc") process :=
  ⟨derived_process_typed typed, (derived_process_represented typed).1,
    (derived_process_represented typed).2, (derived_process_typed typed).isWellScopedAt⟩

end Mettapedia.OSLF.MeTTaIL.GeneralRho
