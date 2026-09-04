import Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
import Mettapedia.GSLT.LanguageDef.ReflectiveSupportRenaming
import Std.Data.String.ToNat

/-!
# Source-indexed syntax for selected native-type rules

A native-type rule about one selected rewrite occurrence must retain the
authored focus and right-hand side.  This module embeds those patterns into
an inference-rule schema while changing only their ordinary free-variable
names.  Constructor heads, binders, explicit substitutions, and collection
shape remain source syntax.

The renamed variables are indexed by both the selected rewrite occurrence and
their first endpoint-support position.  This prevents accidental capture by
generic rule metavariables and prevents two authored occurrences from sharing
syntactic provenance merely because their endpoint patterns are extensionally
equal.

Collection-rest variables are not renamed by `Pattern.renameFVars`; the
ordinary inference checker already rejects collection rests in rule schemas.
Thus this construction fails closed outside that representable fragment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-- First-occurrence endpoint support of one exact selected rewrite.  The
right-hand side is included because premise-produced variables need not occur
in the left-hand side of every authored language. -/
def endpointVariableNames {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List String :=
  ((typingAt demand slot).site.rewrite.left.freeFvarNames ++
    (typingAt demand slot).site.rewrite.right.freeFvarNames).eraseDups

@[simp]
theorem mem_endpointVariableNames_iff {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (name : String) :
    name ∈ endpointVariableNames demand slot ↔
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames ∨
        name ∈
          (typingAt demand slot).site.rewrite.right.freeFvarNames := by
  simp [endpointVariableNames]

/-- Collision-free compact name for one occurrence-local authored variable.
`Nat.pair` keeps occurrence identity and support position independently
recoverable, while decimal rendering avoids the quadratic unary names that
would result from feeding the paired coordinate to `indexedMetavariable`. -/
def authoredVariableName (slot index : Nat) : String :=
  "$oslf:authored-variable:" ++ toString (Nat.pair slot index)

theorem authoredVariableName_injective :
    Function.Injective fun coordinate : Nat × Nat =>
      authoredVariableName coordinate.1 coordinate.2 := by
  intro first second equality
  have paired : Nat.pair first.1 first.2 = Nat.pair second.1 second.2 := by
    apply Nat.repr_injective
    exact (String.append_right_inj "$oslf:authored-variable:").mp equality
  exact Prod.ext (Nat.pair_eq_pair.mp paired).1 (Nat.pair_eq_pair.mp paired).2

theorem authoredVariableName_eq_iff
    (firstSlot firstIndex secondSlot secondIndex : Nat) :
    authoredVariableName firstSlot firstIndex =
        authoredVariableName secondSlot secondIndex ↔
      firstSlot = secondSlot ∧ firstIndex = secondIndex := by
  constructor
  · intro equality
    have coordinates :
        (firstSlot, firstIndex) = (secondSlot, secondIndex) :=
      authoredVariableName_injective equality
    exact Prod.mk.inj coordinates
  · rintro ⟨rfl, rfl⟩
    rfl

theorem authoredVariableName_ne_focus (slot index : Nat) :
    authoredVariableName slot index ≠ "focus" := by
  intro equality
  have lists := congrArg String.toList equality
  simp [authoredVariableName] at lists

theorem authoredVariableName_ne_reduct (slot index : Nat) :
    authoredVariableName slot index ≠ "reduct" := by
  intro equality
  have lists := congrArg String.toList equality
  simp [authoredVariableName] at lists

/-- Rename an authored endpoint variable by its exact occurrence and its first
position in the ordered endpoint support.  Names outside the endpoint support
map to the first index after that support and therefore fail later scope
admission instead of acquiring silent authority. -/
def renameVariable {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (name : String) : String :=
  authoredVariableName slot.val
    ((endpointVariableNames demand slot).idxOf name)

/-- Every occurrence-local authored variable has a nonempty private name,
including a source variable outside the declared endpoint support.  The latter
will still be rejected by typing/scope admission rather than acquiring an
ambient public name. -/
theorem renameVariable_ne_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (name : String) :
    renameVariable demand slot name ≠ "" := by
  intro equality
  have lists := congrArg String.toList equality
  simp [renameVariable, authoredVariableName] at lists

/-- Renaming ordinary free variables preserves locally nameless scope. -/
@[simp] theorem isWellScopedAt_renameFVars
    (rename : String → String) (depth : Nat) (pattern : Pattern) :
    (Pattern.renameFVars rename pattern).isWellScopedAt depth =
      pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [Pattern.renameFVars, Pattern.isWellScopedAt]
  | hfvar name => simp [Pattern.renameFVars, Pattern.isWellScopedAt]
  | happly constructor arguments inductionHypothesis =>
      have listEq :
          Pattern.isWellScopedListAt depth
              (arguments.map (Pattern.renameFVars rename)) =
            Pattern.isWellScopedListAt depth arguments := by
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons, Pattern.isWellScopedListAt]
            rw [inductionHypothesis argument (by simp)]
            exact congrArg (Pattern.isWellScopedAt depth argument && ·)
              (listInduction fun other membership =>
                inductionHypothesis other (by simp [membership]))
      simpa [Pattern.renameFVars, Pattern.isWellScopedAt] using listEq
  | hlambda binder body inductionHypothesis =>
      simp [Pattern.renameFVars, Pattern.isWellScopedAt,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Pattern.renameFVars, Pattern.isWellScopedAt,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, Pattern.isWellScopedAt,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have listEq :
          Pattern.isWellScopedListAt depth
              (elements.map (Pattern.renameFVars rename)) =
            Pattern.isWellScopedListAt depth elements := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [List.map_cons, Pattern.isWellScopedListAt]
            rw [inductionHypothesis element (by simp)]
            exact congrArg (Pattern.isWellScopedAt depth element && ·)
              (listInduction fun other membership =>
                inductionHypothesis other (by simp [membership]))
      simpa [Pattern.renameFVars, Pattern.isWellScopedAt] using listEq

/-- Renaming ordinary free variables neither creates nor removes a collection
rest metavariable. -/
@[simp] theorem patternHasNoCollectionRest_renameFVars
    (rename : String → String) (pattern : Pattern) :
    patternHasNoCollectionRest (Pattern.renameFVars rename pattern) =
      patternHasNoCollectionRest pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.renameFVars, patternHasNoCollectionRest]
  | hfvar name => simp [Pattern.renameFVars, patternHasNoCollectionRest]
  | happly constructor arguments inductionHypothesis =>
      have listEq :
          patternsHaveNoCollectionRest
              (arguments.map (Pattern.renameFVars rename)) =
            patternsHaveNoCollectionRest arguments := by
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons, patternsHaveNoCollectionRest]
            rw [inductionHypothesis argument (by simp)]
            exact congrArg (patternHasNoCollectionRest argument && ·)
              (listInduction fun other membership =>
                inductionHypothesis other (by simp [membership]))
      simpa [Pattern.renameFVars, patternHasNoCollectionRest] using listEq
  | hlambda binder body inductionHypothesis =>
      simp [Pattern.renameFVars, patternHasNoCollectionRest,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Pattern.renameFVars, patternHasNoCollectionRest,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, patternHasNoCollectionRest,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have listEq :
          patternsHaveNoCollectionRest
              (elements.map (Pattern.renameFVars rename)) =
            patternsHaveNoCollectionRest elements := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [List.map_cons, patternsHaveNoCollectionRest]
            rw [inductionHypothesis element (by simp)]
            exact congrArg (patternHasNoCollectionRest element && ·)
              (listInduction fun other membership =>
                inductionHypothesis other (by simp [membership]))
      simp [Pattern.renameFVars, patternHasNoCollectionRest, listEq]

/-- Free-variable renaming changes occurrence names and nothing else: order,
multiplicity, and binder depth are retained exactly. -/
theorem patternMetavariableOccurrencesAt_renameFVars
    (rename : String → String) (depth : Nat) (pattern : Pattern) :
    patternMetavariableOccurrencesAt depth
        (Pattern.renameFVars rename pattern) =
      (patternMetavariableOccurrencesAt depth pattern).map
        (fun occurrence => (rename occurrence.1, occurrence.2)) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [Pattern.renameFVars,
      patternMetavariableOccurrencesAt]
  | hfvar name => simp [Pattern.renameFVars,
      patternMetavariableOccurrencesAt]
  | happly constructor arguments inductionHypothesis =>
      simp only [Pattern.renameFVars, patternMetavariableOccurrencesAt]
      induction arguments with
      | nil => simp [patternsMetavariableOccurrencesAt]
      | cons argument arguments listInduction =>
          simp only [List.map_cons, patternsMetavariableOccurrencesAt,
            List.map_append]
          rw [inductionHypothesis argument (by simp)]
          exact congrArg
            (List.append
              ((patternMetavariableOccurrencesAt depth argument).map
                fun occurrence => (rename occurrence.1, occurrence.2)))
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))
  | hlambda binder body inductionHypothesis =>
      simp [Pattern.renameFVars, patternMetavariableOccurrencesAt,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Pattern.renameFVars, patternMetavariableOccurrencesAt,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, patternMetavariableOccurrencesAt,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.renameFVars, patternMetavariableOccurrencesAt]
      induction elements with
      | nil => simp [patternsMetavariableOccurrencesAt]
      | cons element elements listInduction =>
          simp only [List.map_cons, patternsMetavariableOccurrencesAt,
            List.map_append]
          rw [inductionHypothesis element (by simp)]
          exact congrArg
            (List.append
              ((patternMetavariableOccurrencesAt depth element).map
                fun occurrence => (rename occurrence.1, occurrence.2)))
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))

/-- Alpha-renaming free schema variables preserves the complete fixed
constructor check.  This is the structural bridge that lets an authored
source certificate qualify its occurrence-local embedding without reopening
constructor lookup for every generated rule. -/
@[simp] theorem fixedConstructorsValid_renameFVars
    (language : LanguageDef) (rename : String → String)
    (pattern : Pattern) :
    fixedConstructorsValid language (Pattern.renameFVars rename pattern) =
      fixedConstructorsValid language pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.renameFVars, fixedConstructorsValid]
  | hfvar name => simp [Pattern.renameFVars, fixedConstructorsValid]
  | happly constructor arguments inductionHypothesis =>
      have listEq :
          fixedConstructorListsValid language
              (arguments.map (Pattern.renameFVars rename)) =
            fixedConstructorListsValid language arguments := by
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons, fixedConstructorListsValid]
            rw [inductionHypothesis argument (by simp)]
            exact congrArg
              (fixedConstructorsValid language argument && ·)
              (listInduction fun other membership =>
                inductionHypothesis other (by simp [membership]))
      simp [Pattern.renameFVars, fixedConstructorsValid, listEq]
  | hlambda binder body inductionHypothesis =>
      simp [Pattern.renameFVars, fixedConstructorsValid,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Pattern.renameFVars, fixedConstructorsValid,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, fixedConstructorsValid,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have listEq :
          fixedConstructorListsValid language
              (elements.map (Pattern.renameFVars rename)) =
            fixedConstructorListsValid language elements := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [List.map_cons, fixedConstructorListsValid]
            rw [inductionHypothesis element (by simp)]
            exact congrArg
              (fixedConstructorsValid language element && ·)
              (listInduction fun other membership =>
                inductionHypothesis other (by simp [membership]))
      simpa [Pattern.renameFVars, fixedConstructorsValid] using listEq

/-- Structural embedding of one authored pattern into the local inference
schema namespace. -/
def authoredPattern {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (pattern : Pattern) : Pattern :=
  Pattern.renameFVars (renameVariable demand slot) pattern

/-- Structural source condition for the binder-free introduction fragment.
Every free schema variable occurs at the top level, while de Bruijn scope,
collection-tail absence, and binder metadata are checked independently. -/
structure TopLevelPatternAdmission (pattern : Pattern) : Prop where
  metavariablesAtTop :
    ∀ occurrence ∈ patternMetavariableOccurrencesAt 0 pattern,
      occurrence.2 = 0
  wellScoped : pattern.isWellScoped = true
  noCollectionRest : patternHasNoCollectionRest pattern = true
  canonicalBinders : pattern.hasCanonicalBinderMetadata = true

/-- Executable structural certificate for `TopLevelPatternAdmission`. -/
def topLevelPatternAdmissionCheck (pattern : Pattern) : Bool :=
  (patternMetavariableOccurrencesAt 0 pattern).all
      (fun occurrence => occurrence.2 == 0) &&
    pattern.isWellScoped &&
    patternHasNoCollectionRest pattern &&
    pattern.hasCanonicalBinderMetadata

/-- The finite source-pattern check reconstructs the proof-facing admission
record. -/
theorem topLevelPatternAdmission_of_check (pattern : Pattern)
    (checked : topLevelPatternAdmissionCheck pattern = true) :
    TopLevelPatternAdmission pattern := by
  unfold topLevelPatternAdmissionCheck at checked
  rcases Bool.and_eq_true_iff.mp checked with ⟨checked, canonical⟩
  rcases Bool.and_eq_true_iff.mp checked with ⟨checked, noRest⟩
  rcases Bool.and_eq_true_iff.mp checked with ⟨atTop, scopeCheck⟩
  exact
    { metavariablesAtTop := fun occurrence membership =>
        beq_iff_eq.mp (List.all_eq_true.mp atTop occurrence membership)
      wellScoped := scopeCheck
      noCollectionRest := noRest
      canonicalBinders := canonical }

/-- Every metavariable occurrence in an authored embedding has a nonempty
occurrence-local name. -/
theorem authoredPattern_occurrence_name_nonempty
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (pattern : Pattern) (occurrence : String × Nat)
    (membership : occurrence ∈ patternMetavariableOccurrencesAt 0
      (authoredPattern demand slot pattern)) :
    occurrence.1 ≠ "" := by
  unfold authoredPattern at membership
  rw [patternMetavariableOccurrencesAt_renameFVars] at membership
  obtain ⟨sourceOccurrence, sourceMembership, equality⟩ :=
    List.mem_map.mp membership
  subst occurrence
  exact renameVariable_ne_empty demand slot sourceOccurrence.1

/-- Top-level schema occurrences remain top-level after occurrence-local
renaming. -/
theorem authoredPattern_occurrence_depth_zero
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (pattern : Pattern) (admission : TopLevelPatternAdmission pattern)
    (occurrence : String × Nat)
    (membership : occurrence ∈ patternMetavariableOccurrencesAt 0
      (authoredPattern demand slot pattern)) :
    occurrence.2 = 0 := by
  unfold authoredPattern at membership
  rw [patternMetavariableOccurrencesAt_renameFVars] at membership
  obtain ⟨sourceOccurrence, sourceMembership, equality⟩ :=
    List.mem_map.mp membership
  subst occurrence
  exact admission.metavariablesAtTop sourceOccurrence sourceMembership

@[simp] theorem authoredPattern_isWellScoped
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (pattern : Pattern) (admission : TopLevelPatternAdmission pattern) :
    (authoredPattern demand slot pattern).isWellScoped = true := by
  simpa [authoredPattern, Pattern.isWellScoped] using admission.wellScoped

@[simp] theorem authoredPattern_hasNoCollectionRest
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (pattern : Pattern) (admission : TopLevelPatternAdmission pattern) :
    patternHasNoCollectionRest (authoredPattern demand slot pattern) = true := by
  simpa [authoredPattern] using admission.noCollectionRest

@[simp] theorem authoredPattern_hasCanonicalBinderMetadata
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (pattern : Pattern) (admission : TopLevelPatternAdmission pattern) :
    (authoredPattern demand slot pattern).hasCanonicalBinderMetadata = true := by
  simpa [authoredPattern] using admission.canonicalBinders

def authoredFocus {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Pattern :=
  authoredPattern demand slot (typingAt demand slot).site.focus

def authoredSource {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Pattern :=
  authoredPattern demand slot (typingAt demand slot).site.rewrite.left

def authoredTarget {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Pattern :=
  authoredPattern demand slot (typingAt demand slot).site.rewrite.right

/-- Exact occurrence-local authored-variable inventory corresponding to the
ordered endpoint support.  Generated rules infer their complete formal row
from actual syntax; this inventory remains useful for provenance and exact
support theorems. -/
def authoredMetavariables {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List (String × Nat) :=
  List.ofFn fun index : Fin (endpointVariableNames demand slot).length =>
    (authoredVariableName slot.val index.val, 0)

@[simp]
theorem length_authoredMetavariables {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (authoredMetavariables demand slot).length =
      (endpointVariableNames demand slot).length := by
  simp [authoredMetavariables]

/-! ## Discriminating source-occurrence witness -/

namespace Canary

open SelectedNativeTypeContextualCalculus.Canary
open ContextualModalSignature.Canary

/-- Ordinary binder-free authored syntax lies in the admitted generation
fragment. -/
theorem top_level_application_admitted :
    topLevelPatternAdmissionCheck
        (.apply "constructor" [.fvar "left", .fvar "right"]) = true := by
  decide +kernel

/-- A free schema variable below a binder is rejected.  Binder-bearing source
rules require the later alpha-safe/eigenvariable lowering rather than being
silently admitted by the binder-free generator. -/
theorem bound_context_free_variable_rejected :
    topLevelPatternAdmissionCheck (.lambda none (.fvar "capturable")) =
      false := by
  decide +kernel

/-- Collection-rest variables are a separate binding surface and therefore
fail closed in the current source-indexed fragment. -/
theorem collection_rest_rejected :
    topLevelPatternAdmissionCheck
        (.collection .hashBag [] (some "rest")) = false := by
  decide +kernel

private abbrev middleSlot : Occurrence (middleDemand .star) :=
  ⟨0, by simp [middleDemand]⟩

theorem middle_endpointVariableNames :
    endpointVariableNames (middleDemand .star) middleSlot =
      ["left", "focus", "right"] := by
  unfold endpointVariableNames
  rw [middle_typingAt]
  have rewriteEq : middleTyping.site.rewrite = contextualRewrite := rfl
  rw [rewriteEq]
  simp [contextualRewrite, Pattern.freeFvarNames, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop]

/-- The selected middle focus is retained, with only its authored variable
alpha-renamed into the occurrence-local namespace. -/
theorem middle_authoredFocus_exact :
    authoredFocus (middleDemand .star) middleSlot =
      .fvar (authoredVariableName 0 1) := by
  unfold authoredFocus authoredPattern
  rw [middle_typingAt]
  simp only [middleTyping, middleSite, Pattern.renameFVars]
  unfold renameVariable
  rw [middle_endpointVariableNames]
  rfl

/-- Constructor structure and authored argument order survive the embedding.
-/
theorem middle_authoredSource_exact :
    authoredSource (middleDemand .star) middleSlot =
      .apply ternaryTerm.label
        [.fvar (authoredVariableName 0 0),
         .fvar (authoredVariableName 0 1),
         .fvar (authoredVariableName 0 2)] := by
  unfold authoredSource authoredPattern
  rw [middle_typingAt]
  have rewriteEq : middleTyping.site.rewrite = contextualRewrite := rfl
  rw [rewriteEq]
  simp only [contextualRewrite, Pattern.renameFVars, List.map_cons,
    List.map_nil]
  unfold renameVariable
  rw [middle_endpointVariableNames]
  rfl

/-- The authored right-hand side is retained rather than replaced by an
unrelated reduct token. -/
theorem middle_authoredTarget_exact :
    authoredTarget (middleDemand .star) middleSlot =
      .fvar (authoredVariableName 0 1) := by
  unfold authoredTarget authoredPattern
  rw [middle_typingAt]
  have rewriteEq : middleTyping.site.rewrite = contextualRewrite := rfl
  rw [rewriteEq]
  simp only [contextualRewrite, Pattern.renameFVars]
  unfold renameVariable
  rw [middle_endpointVariableNames]
  rfl

theorem middle_authoredFocus_ne_private_focus :
    authoredFocus (middleDemand .star) middleSlot ≠ .fvar "focus" := by
  rw [middle_authoredFocus_exact]
  simpa using authoredVariableName_ne_focus 0 1

theorem middle_authoredTarget_ne_private_reduct :
    authoredTarget (middleDemand .star) middleSlot ≠ .fvar "reduct" := by
  rw [middle_authoredTarget_exact]
  simpa using authoredVariableName_ne_reduct 0 1

theorem middle_distinct_endpoint_variables_remain_distinct :
    authoredVariableName 0 0 ≠ authoredVariableName 0 2 := by
  rw [Ne, authoredVariableName_eq_iff]
  decide

end Canary

#print axioms authoredVariableName_eq_iff
#print axioms Canary.top_level_application_admitted
#print axioms Canary.bound_context_free_variable_rejected
#print axioms Canary.collection_rest_rejected
#print axioms Canary.middle_authoredSource_exact
#print axioms Canary.middle_authoredTarget_exact
#print axioms Canary.middle_distinct_endpoint_variables_remain_distinct

end Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
