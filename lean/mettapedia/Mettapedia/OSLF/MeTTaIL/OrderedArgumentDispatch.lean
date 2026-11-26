import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.Data.List.OrderedPrefilter

/-! Application and vector positions used to prefilter ordered rule lists. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.OrderedArgumentDispatch

open Syntax Match MatchSpec Engine
open Mettapedia.Data.List.OrderedPrefilter

inductive ArgumentStep where
  | application (index : Nat)
  | vector (index : Nat)

def ArgumentStep.select : ArgumentStep → Pattern → Option Pattern
  | .application index, .apply _ arguments => arguments[index]?
  | .vector index, .collection .vec elements _ => elements[index]?
  | _, _ => none

def applicationLabelAt : List ArgumentStep → Pattern → Option String
  | [], .apply label _ => some label
  | [], _ => none
  | step :: path, pattern => (step.select pattern).bind (applicationLabelAt path)

private theorem argumentMatchAt {left right : List Pattern} {bindings : Bindings}
    (matched : MatchArgsRel left right bindings) {index : Nat} {pattern : Pattern}
    (observed : left[index]? = some pattern) :
    ∃ term termBindings, right[index]? = some term ∧ MatchRel pattern term termBindings := by
  induction index generalizing left right bindings with
  | zero =>
      cases matched with
      | nil => simp at observed
      | cons headMatch tailMatch _ =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at observed
          subst pattern
          exact ⟨_, _, rfl, headMatch⟩
  | succ _ ih =>
      cases matched with
      | nil => simp at observed
      | cons _ tailMatch _ =>
          obtain ⟨term, termBindings, selected, relation⟩ := ih tailMatch (by simpa using observed)
          exact ⟨term, termBindings, selected, relation⟩

private theorem matchedSelection (step : ArgumentStep)
    {pattern term child : Pattern} {bindings : Bindings}
    (matched : MatchRel pattern term bindings) (selected : step.select pattern = some child) :
    ∃ termChild termBindings,
      step.select term = some termChild ∧ MatchRel child termChild termBindings := by
  cases step with
  | application index =>
      cases pattern <;> simp [ArgumentStep.select] at selected
      case apply name arguments =>
        cases matched with
        | apply paired _ =>
            simpa only [ArgumentStep.select] using argumentMatchAt paired selected
  | vector index =>
      cases pattern <;> simp [ArgumentStep.select] at selected
      case collection kind elements rest =>
        cases kind <;> simp at selected
        case vec =>
          cases matched with
          | collection impossible _ => exact (impossible rfl).elim
          | vector paired =>
              simpa only [ArgumentStep.select] using argumentMatchAt paired selected
          | vectorRest paired _ =>
              obtain ⟨_, _, selectedTerm, relation⟩ := argumentMatchAt paired selected
              obtain ⟨present, _⟩ := List.getElem?_eq_some_iff.mp selected
              rw [List.getElem?_take_of_lt present] at selectedTerm
              exact ⟨_, _, selectedTerm, relation⟩

/-- A rigid application label observed along a matching ordered position is
present with the same value in the matched subject. -/
theorem applicationLabelAt_of_match (path : List ArgumentStep)
    {pattern term : Pattern} {bindings : Bindings} {label : String}
    (matched : MatchRel pattern term bindings)
    (observed : applicationLabelAt path pattern = some label) :
    applicationLabelAt path term = some label := by
  induction path generalizing pattern term bindings with
  | nil =>
      cases pattern <;> simp [applicationLabelAt] at observed
      case apply head _ =>
        cases matched
        simpa only [applicationLabelAt, Option.some.injEq] using observed
  | cons step path ih =>
      cases selected : step.select pattern with
      | none => simp [applicationLabelAt, selected] at observed
      | some child =>
          simp only [applicationLabelAt, selected, Option.bind] at observed
          obtain ⟨_, _, selectedTerm, childMatch⟩ := matchedSelection step matched selected
          simpa only [applicationLabelAt, selectedTerm, Option.bind]
            using ih childMatch observed

/-- Unobserved rule heads remain candidates. -/
def compatible (path : List ArgumentStep) (termLabel : Option String) (rule : RewriteRule) : Bool :=
  match applicationLabelAt path rule.left with
  | none => true
  | some label => termLabel == some label

theorem compatible_of_match (path : List ArgumentStep)
    {rule : RewriteRule} {term : Pattern} {bindings : Bindings}
    (matched : MatchRel rule.left term bindings) :
    compatible path (applicationLabelAt path term) rule = true := by
  cases ruleHead : applicationLabelAt path rule.left with
  | none => simp [compatible, ruleHead]
  | some label => simp [compatible, ruleHead, applicationLabelAt_of_match path matched ruleHead]

def observeLabels (paths : List (List ArgumentStep)) (term : Pattern) :
    List (List ArgumentStep × Option String) :=
  paths.map fun path => (path, applicationLabelAt path term)

private def ruleFilter (observations : List (List ArgumentStep × Option String))
    (rule : RewriteRule) : Bool :=
  observations.all fun (path, label) => compatible path label rule

def selectRules (paths : List (List ArgumentStep)) (term : Pattern)
    (rules : List RewriteRule) : List RewriteRule :=
  rules.filter (ruleFilter (observeLabels paths term))

private def selectObservedIndices (observations : List (List ArgumentStep × Option String))
    (rules : List RewriteRule) : List Nat :=
  rules.zipIdx.filterMap fun (rule, index) =>
    if ruleFilter observations rule then some index else none

/-- The actual occurrences retained by the filter, in source order. -/
def selectRuleIndices (paths : List (List ArgumentStep)) (term : Pattern)
    (rules : List RewriteRule) : List Nat :=
  selectObservedIndices (observeLabels paths term) rules

/-- Checking only the indices is sufficient to reconstruct the exact ordered
rules selected by the same observations. -/
theorem selectRuleIndices_readback (paths : List (List ArgumentStep)) (term : Pattern)
    (rules : List RewriteRule) :
    (selectRuleIndices paths term rules).filterMap (fun index => rules[index]?) =
      selectRules paths term rules := by
  let keep := ruleFilter (observeLabels paths term)
  unfold selectRuleIndices selectObservedIndices selectRules
  rw [List.filterMap_filterMap]
  calc
    _ = rules.zipIdx.filterMap (fun entry => if keep entry.1 then some entry.1 else none) := by
      apply List.filterMap_congr
      intro entry member
      have found := List.mem_zipIdx_iff_getElem?.mp member
      change (if keep entry.1 then some entry.2 else none).bind (fun index => rules[index]?) =
        (if keep entry.1 then some entry.1 else none)
      cases accepted : keep entry.1 with
      | false => rfl
      | true => exact found
    _ = rules.filter keep := by
      let retain := fun rule => if keep rule then some rule else none
      change rules.zipIdx.filterMap (retain ∘ Prod.fst) = rules.filter keep
      rw [← List.filterMap_map, List.zipIdx_map_fst]
      change rules.filterMap (Option.guard keep) = rules.filter keep
      rw [List.filterMap_eq_filter]

/-- Selection preserves the result of each ordered occurrence and leaves
premise evaluation to the existing rule interpreter. -/
theorem rewriteStepWithPremisesUsing_eq_selected
    (paths : List (List ArgumentStep)) (environment : RelationEnv) (language : LanguageDef)
    (term : Pattern) :
    rewriteStepWithPremisesUsing environment language term =
      (selectRules paths term language.rewrites).flatMap
        (fun rule => applyRuleWithPremisesUsing environment language rule term) := by
  unfold rewriteStepWithPremisesUsing selectRules ruleFilter observeLabels
  symm
  apply (filter_flatMap_eq_iff _ _ _).mpr
  intro rule _ emits
  have nonempty : matchPattern rule.left term ≠ [] := by
    intro empty
    exact emits (by simp [applyRuleWithPremisesUsing, empty])
  obtain ⟨_, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have matched := matchPattern_sound member
  apply List.all_eq_true.mpr
  intro observed occurrence
  obtain ⟨path, _, rfl⟩ := List.mem_map.mp occurrence
  exact compatible_of_match path matched

end Mettapedia.OSLF.MeTTaIL.OrderedArgumentDispatch
