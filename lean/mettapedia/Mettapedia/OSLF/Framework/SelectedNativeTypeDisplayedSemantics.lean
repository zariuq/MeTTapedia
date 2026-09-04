import Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
import Mettapedia.OSLF.Framework.DisplayedRewriteVariableProfile
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Displayed semantics for selected native types

This module fixes the independent semantic boundary used to qualify a
selected native-type calculus.  Universe levels and behavioral modalities
remain different coordinates:

* a carrier model supplies actual carrier-indexed universe objects and an
  authored typing relation, including `star :: box`;
* a modal former is indexed by one exact displayed rewrite occurrence;
* its behavioral meaning quantifies over the displayed rely telescope and
  requires a step made by that exact authored rewrite row.

The reduction environment is an explicit parameter.  Neither generated
derivability nor checker acceptance occurs in these definitions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef

/-! ## Directional names for the reduction-span modalities -/

/-- Forward possibility: the current state has a successor satisfying the
predicate. -/
def stepFuture {State : Type*} (span : ReductionSpan State)
    (predicate : State → Prop) : State → Prop :=
  derivedDiamond span predicate

/-- The right adjoint of `stepFuture`.  It quantifies over predecessors of
the current state, not over all forward successors. -/
def pastUniversal {State : Type*} (span : ReductionSpan State)
    (predicate : State → Prop) : State → Prop :=
  derivedBox span predicate

theorem stepFuture_pastUniversal_galois {State : Type*}
    (span : ReductionSpan State) :
    GaloisConnection (stepFuture span) (pastUniversal span) :=
  derived_galois span

/-! ## The cold relation and its proof-relevant span -/

/-- One edge of the cold authored reduction graph.  Endpoints remain data;
the reduction witness establishes their authority. -/
structure ColdEdge (relations : RelationEnv)
    (source : ValidatedLanguageDef) where
  before : Pattern
  after : Pattern
  reduces : langReducesUsing relations source.language before after

/-- Reduction span induced by the exact authored language and relation
environment. -/
def coldSpan (relations : RelationEnv) (source : ValidatedLanguageDef) :
    ReductionSpan Pattern where
  Edge := ColdEdge relations source
  source := ColdEdge.before
  target := ColdEdge.after

/-- Forward possibility over the cold relation, expanded without categorical
notation. -/
theorem cold_stepFuture_iff (relations : RelationEnv)
    (source : ValidatedLanguageDef) (predicate : Pattern → Prop)
    (before : Pattern) :
    stepFuture (coldSpan relations source) predicate before ↔
      ∃ after,
        langReducesUsing relations source.language before after ∧
          predicate after := by
  constructor
  · rintro ⟨edge, sourceEq, targetHolds⟩
    refine ⟨edge.after, ?_, targetHolds⟩
    simpa [coldSpan] using sourceEq ▸ edge.reduces
  · rintro ⟨after, reduces, targetHolds⟩
    exact ⟨⟨before, after, reduces⟩, rfl, targetHolds⟩

/-- The behavioral right adjoint over the cold relation quantifies over
incoming predecessors. -/
theorem cold_pastUniversal_iff (relations : RelationEnv)
    (source : ValidatedLanguageDef) (predicate : Pattern → Prop)
    (after : Pattern) :
    pastUniversal (coldSpan relations source) predicate after ↔
      ∀ before,
        langReducesUsing relations source.language before after →
          predicate before := by
  constructor
  · intro universal before reduces
    exact universal ⟨before, after, reduces⟩ rfl
  · intro universal edge targetEq
    exact universal edge.before (targetEq ▸ edge.reduces)

/-! ## Carrier-indexed universes -/

/-- Independent interpretation of the authored carrier hierarchy.  The two
universe objects are data in the same carrier-indexed typing relation as
ordinary types; they are not merely names for arbitrary predicates. -/
structure CarrierModel where
  universeObject : TypeExpr → CarrierUniverseSignature.Code → Pattern
  Typed : TypeExpr → Pattern → Pattern → Prop
  starTypedBox : ∀ carrier,
    Typed carrier (universeObject carrier .star)
      (universeObject carrier .box)

/-- The model interface exposes the manuscript's universe axiom directly. -/
theorem universe_axiom (model : CarrierModel) (carrier : TypeExpr) :
    model.Typed carrier (model.universeObject carrier .star)
      (model.universeObject carrier .box) :=
  model.starTypedBox carrier

/-! ## Exact selected-occurrence steps -/

/-- The selected rewrite row belongs to the exact source language by its
retained authored-list index. -/
theorem selectedRewrite_mem {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    typing.site.rewrite ∈ source.language.rewrites := by
  exact List.get_mem source.language.rewrites typing.site.rewriteIndex

/-- A proof-relevant application of one exact selected rewrite occurrence.
The rule is fixed by the type index; matching and ordered-premise evidence
cannot be supplied for a different row with extensionally equal endpoints. -/
structure SelectedOccurrenceStep
    {source : ValidatedLanguageDef}
    (relations : RelationEnv) (typing : DisplayedRewriteTyping source)
    (before after : Pattern) where
  premiseFuel : Nat
  initialBindings : Bindings
  finalBindings : Bindings
  matched : initialBindings ∈
    matchPatternForRule source.language typing.site.rewrite before
  premises : PremisesAt (engineBasePremises relations) source.language
    premiseFuel initialBindings typing.site.rewrite.premises finalBindings
  result :
    applyBindingsForRule source.language typing.site.rewrite finalBindings =
      after

namespace SelectedOccurrenceStep

/-- Forgetting occurrence identity yields an ordinary step of the cold
authored language. -/
def toStepAt {source : ValidatedLanguageDef} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {before after : Pattern}
    (step : SelectedOccurrenceStep relations typing before after) :
    StepAt (engineBasePremises relations) source.language
      (step.premiseFuel + 1) before after :=
  .rule (selectedRewrite_mem typing) step.matched step.premises step.result

/-- Exact occurrence execution is sound for the cold reduction relation. -/
theorem toColdRelation {source : ValidatedLanguageDef}
    {relations : RelationEnv} {typing : DisplayedRewriteTyping source}
    {before after : Pattern}
    (step : SelectedOccurrenceStep relations typing before after) :
    langReducesUsing relations source.language before after := by
  exact ⟨step.premiseFuel + 1, step.toStepAt⟩

end SelectedOccurrenceStep

/-- Propositional existence of a proof-relevant exact-occurrence step. -/
def OccursAt {source : ValidatedLanguageDef} (relations : RelationEnv)
    (typing : DisplayedRewriteTyping source) (before after : Pattern) : Prop :=
  Nonempty (SelectedOccurrenceStep relations typing before after)

theorem occursAt_implies_cold {source : ValidatedLanguageDef}
    {relations : RelationEnv} {typing : DisplayedRewriteTyping source}
    {before after : Pattern} :
    OccursAt relations typing before after →
      langReducesUsing relations source.language before after := by
  rintro ⟨step⟩
  exact step.toColdRelation

/-! ## Ordered rely environments -/

/-- One position in the exact authored-order rely telescope. -/
abbrev RelyIndex {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :=
  Fin (DisplayedContextProfile.bindings typing).length

/-- An intrinsically length-aligned row over the rely telescope. -/
abbrev RelyRow {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :=
  RelyIndex typing → Pattern

/-- Stable authored-order list view of an indexed rely row. -/
def rowList {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source} (row : RelyRow typing) :
    List Pattern :=
  List.ofFn row

/-- Bind each fixed-context variable to the value at the same exact telescope
position. -/
def instantiateRelyBindings {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) (values : RelyRow typing) :
  Bindings :=
  List.ofFn fun index : RelyIndex typing =>
    (((DisplayedContextProfile.bindings typing).get index).1, values index)

/-- Instantiate the displayed source context with an ordered rely row and a
candidate focus.  A root context is the identity context: it must not traverse
or evaluate syntax inside the already supplied focus. -/
def displayedSource {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) (values : RelyRow typing)
    (focus : Pattern) : Pattern :=
  match typing.site.context with
  | .hole => focus
  | context =>
      applyBindings (instantiateRelyBindings typing values)
        (context.fill focus)

/-- A displayed root is the identity context on every candidate focus,
including syntax whose ordinary binding application would compute. -/
theorem displayedSource_of_context_eq_hole
    {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) (values : RelyRow typing)
    (focus : Pattern) (root : typing.site.context = .hole) :
    displayedSource typing values focus = focus := by
  simp [displayedSource, root]

/-- The manuscript's `V`/`W` presentation covers occurrences whose fixed
context and selected focus have disjoint free-variable support.  Shared
variables require an additional equality/matching constraint and remain
outside this first sound fragment. -/
def SupportSeparated {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : Prop :=
  DisplayedRewriteVariableProfile.sharedNames typing.site = []

/-- Every root occurrence belongs to the separated-support fragment. -/
theorem supportSeparated_of_root {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (index : Fin source.language.rewrites.length)
    (siteEquality : typing.site =
      DisplayedRewriteSite.root source.language index) :
    SupportSeparated typing := by
  rw [SupportSeparated, siteEquality,
    DisplayedRewriteVariableProfile.sharedNames_root]

/-- Every rely value inhabits its corresponding authored type. -/
def RelyValuesTyped {source : ValidatedLanguageDef}
    (model : CarrierModel) (typing : DisplayedRewriteTyping source)
    (types values : RelyRow typing) : Prop :=
  ∀ index,
    let binding := (DisplayedContextProfile.bindings typing).get index
    model.Typed binding.2 (values index) (types index)

/-- Every rely type lies at the universe level selected for its exact local
slot. -/
def RelyTypesSorted {source : ValidatedLanguageDef}
    (model : CarrierModel) (occurrence : ProfiledRewriteOccurrence source)
    (types : RelyRow occurrence.typing) : Prop :=
  ∀ index,
    let binding :=
      (DisplayedContextProfile.bindings occurrence.typing).get index
    model.Typed binding.2 (types index)
      (model.universeObject binding.2
        (occurrence.profile
          (ContextualModalProfile.relySlot occurrence.typing index)))

/-- A dependent result family yields, for every well-typed rely row, an
authored result type at the selected result universe. -/
def ResultFamilySorted {source : ValidatedLanguageDef}
    (model : CarrierModel) (occurrence : ProfiledRewriteOccurrence source)
    (types : RelyRow occurrence.typing) (family : Pattern) : Prop :=
  ∀ values,
    RelyValuesTyped model occurrence.typing types values →
      ∃ resultType,
        ContextualFamilyApplication.Denotes family (rowList values)
          resultType ∧
        model.Typed occurrence.typing.rewriteType resultType
          (model.universeObject occurrence.typing.rewriteType
            (ContextualModalProfile.resultCode occurrence.profile))

/-- One occurrence-indexed modal former.  The dependent index retains the
source language, exact rewrite occurrence, displayed context, typing, local
profile, and grounding evidence. -/
structure ModalFormer {source : ValidatedLanguageDef}
    (occurrence : ProfiledRewriteOccurrence source) where
  relyTypes : RelyRow occurrence.typing
  resultFamily : Pattern

/-- Formation meaning for the selected modal former. -/
def ModalFormer.WellFormed {source : ValidatedLanguageDef}
    (model : CarrierModel) {occurrence : ProfiledRewriteOccurrence source}
    (former : ModalFormer occurrence) : Prop :=
  RelyTypesSorted model occurrence former.relyTypes ∧
    ResultFamilySorted model occurrence former.relyTypes former.resultFamily

/-- Paper-faithful rely-possibly meaning for one exact selected occurrence.
For every well-typed ordered rely assignment, the displayed context filled by
the candidate focus must take the selected authored rewrite row to a result
inhabiting the instantiated result family. -/
def RelyPossibly {source : ValidatedLanguageDef}
    (model : CarrierModel) (relations : RelationEnv)
    (typing : DisplayedRewriteTyping source) (types : RelyRow typing)
    (family focus : Pattern) : Prop :=
  SupportSeparated typing ∧
    ∀ values,
      RelyValuesTyped model typing types values →
        ∃ after resultType,
          OccursAt relations typing (displayedSource typing values focus) after ∧
          ContextualFamilyApplication.Denotes family (rowList values)
            resultType ∧
          model.Typed typing.rewriteType after resultType

theorem relyPossibly_supportSeparated {source : ValidatedLanguageDef}
    {model : CarrierModel} {relations : RelationEnv}
    {typing : DisplayedRewriteTyping source} {types : RelyRow typing}
    {family focus : Pattern} :
    RelyPossibly model relations typing types family focus →
      SupportSeparated typing :=
  And.left

/-- Behavioral membership of a selected modal former.  Universe profile codes
do not choose a direction here; they occur only in `WellFormed`. -/
def ModalFormer.Member {source : ValidatedLanguageDef}
    (model : CarrierModel) (relations : RelationEnv)
    {occurrence : ProfiledRewriteOccurrence source}
    (former : ModalFormer occurrence) (focus : Pattern) : Prop :=
  RelyPossibly model relations occurrence.typing former.relyTypes
    former.resultFamily focus

/-! ## Direction canary -/

namespace Canary

open Mettapedia.OSLF.Framework.ContextualModalSignature.Canary

inductive Point
  | before
  | after
deriving DecidableEq

inductive OneEdge
  | only

def oneEdgeSpan : ReductionSpan Point where
  Edge := OneEdge
  source := fun _ => .before
  target := fun _ => .after

/-- Forward possibility reads the successor of the edge. -/
theorem stepFuture_reads_successor :
    stepFuture oneEdgeSpan (fun point => point = .after) .before := by
  exact ⟨.only, rfl, rfl⟩

/-- The right adjoint reads the predecessor of an incoming edge. -/
theorem pastUniversal_reads_predecessor :
    pastUniversal oneEdgeSpan (fun point => point = .before) .after := by
  intro edge targetEq
  cases edge
  rfl

/-- Calling the right adjoint forward necessity would reverse the observable
orientation on the same one-edge graph. -/
theorem pastUniversal_not_forward_successor_test :
    ¬ pastUniversal oneEdgeSpan (fun point => point = .after) .after := by
  intro universal
  have predecessorMustBeAfter := universal .only rfl
  cases predecessorMustBeAfter

/-! ### Exact-occurrence and universe-axis canaries -/

private def leftValue : Pattern :=
  .apply "selected-displayed-semantics:left-value" []

private def focusValue : Pattern :=
  .apply "selected-displayed-semantics:focus-value" []

private def rightValue : Pattern :=
  .apply "selected-displayed-semantics:right-value" []

private def middleBefore : Pattern :=
  .apply ternaryTerm.label [leftValue, focusValue, rightValue]

private def exactBindings : Bindings :=
  [("focus", focusValue), ("right", rightValue), ("left", leftValue)]

/-- The proof-relevant occurrence witness executes the selected authored row;
its result is reconstructed from matching and substitution evidence. -/
private def exactMiddleStep :
    SelectedOccurrenceStep RelationEnv.empty middleTyping middleBefore
      focusValue where
  premiseFuel := 0
  initialBindings := exactBindings
  finalBindings := exactBindings
  matched := by
    simp [matchPatternForRule, middleTyping, middleSite,
      DisplayedRewriteSite.rewrite, source, sourceLanguage,
      contextualRewrite, ternaryTerm, middleBefore, exactBindings,
      leftValue, focusValue, rightValue, matchPattern, matchArgs,
      mergeBindings]
  premises := .nil exactBindings
  result := by
    simp [applyBindingsForRule, applyBindingsForRuleUsing, middleTyping,
      middleSite, DisplayedRewriteSite.rewrite, source, sourceLanguage,
      contextualRewrite, exactBindings, leftValue, focusValue, rightValue,
      applyBindings]

/-- Positive control: the selected non-root occurrence produces its exact
authored right-hand side. -/
theorem middle_occurrence_reduces_to_focus :
    OccursAt RelationEnv.empty middleTyping middleBefore focusValue :=
  ⟨exactMiddleStep⟩

/-- Negative control: exact-occurrence evidence cannot invent a different
result merely because that value also occurs in the source term. -/
theorem middle_occurrence_cannot_invent_left_result :
    ¬ OccursAt RelationEnv.empty middleTyping middleBefore leftValue := by
  intro occurrence
  have reduction := occursAt_implies_cold occurrence
  rw [langReducesUsing_iff_execUsing] at reduction
  rcases reduction with ⟨fuel, member⟩
  cases fuel with
  | zero => simp [rewriteAt] at member
  | succ fuel =>
      simp [rewriteAt, applyRuleUsing, matchPatternForRule,
        source, sourceLanguage, contextualRewrite, ternaryTerm, middleBefore,
        leftValue, focusValue, rightValue, matchPattern, matchArgs,
        mergeBindings, premisesUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, applyBindings] at member

/-- Universe classification and behavioral occurrence are independent axes.
Changing the constant universe profile from `star` to `box` leaves the exact
rewrite behavior unchanged. -/
theorem middle_behavior_independent_of_universe_code
    (model : CarrierModel) (relations : RelationEnv)
    (types : RelyRow middleTyping) (family focus : Pattern) :
    RelyPossibly model relations
        (SelectedNativeTypeContextualCalculus.Canary.middleOccurrence
          .star).typing types family focus ↔
      RelyPossibly model relations
        (SelectedNativeTypeContextualCalculus.Canary.middleOccurrence
          .box).typing types family focus := by
  rfl

end Canary

#print axioms stepFuture_pastUniversal_galois
#print axioms cold_stepFuture_iff
#print axioms cold_pastUniversal_iff
#print axioms universe_axiom
#print axioms selectedRewrite_mem
#print axioms SelectedOccurrenceStep.toColdRelation
#print axioms occursAt_implies_cold
#print axioms supportSeparated_of_root
#print axioms displayedSource_of_context_eq_hole
#print axioms relyPossibly_supportSeparated
#print axioms Canary.stepFuture_reads_successor
#print axioms Canary.pastUniversal_reads_predecessor
#print axioms Canary.pastUniversal_not_forward_successor_test
#print axioms Canary.middle_occurrence_reduces_to_focus
#print axioms Canary.middle_occurrence_cannot_invent_left_result
#print axioms Canary.middle_behavior_independent_of_universe_code

end Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
