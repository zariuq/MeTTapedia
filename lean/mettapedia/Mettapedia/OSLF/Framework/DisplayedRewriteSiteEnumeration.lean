import Mettapedia.OSLF.Framework.DisplayedLanguage

/-!
# Enumeration of displayed rewrite sites

The full source-indexed OSLF construction assigns a contextual modality to every
physical subterm occurrence on the source side of every authored rewrite.
This module makes that finite input executable without losing occurrence
identity.  Equal subterms at different positions are emitted separately,
paired with their distinct one-hole contexts.

`DisplayedSiteSelection.complete` is the full paper-style request.  Any
smaller authored request is covered by it, which gives sparse generation a
precise meaning: it is a selected subfamily of the full construction rather
than a different typing semantics.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef

/-- A physical pattern occurrence, represented by its focused subterm and
the exact one-hole context locating it in the containing pattern. -/
abbrev FocusedPatternOccurrence := Pattern × OneHoleContext

namespace FocusedPatternOccurrence

mutual

  /-- Number of physical nodes in a pattern tree.  Unlike constructor
  support, this counts repeated equal subterms separately. -/
  def physicalNodeCount : Pattern → Nat
    | .bvar _ | .fvar _ => 1
    | .apply _ arguments => 1 + physicalNodeCountList arguments
    | .lambda _ body | .multiLambda _ _ body =>
        1 + physicalNodeCount body
    | .subst body replacement =>
        1 + physicalNodeCount body + physicalNodeCount replacement
    | .collection _ elements _ => 1 + physicalNodeCountList elements

  /-- Aggregate physical-node count of a pattern list. -/
  def physicalNodeCountList : List Pattern → Nat
    | [] => 0
    | pattern :: patterns =>
        physicalNodeCount pattern + physicalNodeCountList patterns

end

/-- Enumerate every physical occurrence in a pattern exactly once by a
preorder traversal.  The outer pair is the root occurrence; recursive rows
retain their argument position in the surrounding zipper. -/
def enumerate : Pattern → List FocusedPatternOccurrence
  | pattern@(.bvar _) => [(pattern, .hole)]
  | pattern@(.fvar _) => [(pattern, .hole)]
  | pattern@(.apply constructor arguments) =>
      (pattern, .hole) ::
        arguments.attach.zipIdx.flatMap fun (argument, index) =>
          (enumerate argument.1).map fun occurrence =>
            (occurrence.1,
              .apply constructor (arguments.take index) occurrence.2
                (arguments.drop (index + 1)))
  | pattern@(.lambda binderName body) =>
      (pattern, .hole) ::
        (enumerate body).map fun occurrence =>
          (occurrence.1, .lambda binderName occurrence.2)
  | pattern@(.multiLambda arity binderNames body) =>
      (pattern, .hole) ::
        (enumerate body).map fun occurrence =>
          (occurrence.1, .multiLambda arity binderNames occurrence.2)
  | pattern@(.subst body replacement) =>
      (pattern, .hole) ::
        (((enumerate body).map fun occurrence =>
          (occurrence.1, .substBody occurrence.2 replacement)) ++
        ((enumerate replacement).map fun occurrence =>
          (occurrence.1, .substReplacement body occurrence.2)))
  | pattern@(.collection collectionType elements rest) =>
      (pattern, .hole) ::
        elements.attach.zipIdx.flatMap fun (element, index) =>
          (enumerate element.1).map fun occurrence =>
            (occurrence.1,
              .collection collectionType (elements.take index) occurrence.2
                (elements.drop (index + 1)) rest)
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have smaller := List.sizeOf_lt_of_mem argument.property; omega)
    | (have smaller := List.sizeOf_lt_of_mem element.property; omega)
    | omega

private theorem take_getElem_drop {α : Type*} (elements : List α)
    (index : Nat) (inBounds : index < elements.length) :
    elements.take index ++ elements[index] :: elements.drop (index + 1) =
      elements := by
  rw [List.getElem_cons_drop inBounds]
  exact List.take_append_drop index elements

private theorem zipIdx_getElem_mem {α : Type*} (elements : List α)
    (index : Nat) (inBounds : index < elements.length) :
    (elements[index], index) ∈ elements.zipIdx := by
  have zipBounds : index < elements.zipIdx.length := by simpa
  have member := List.getElem_mem (l := elements.zipIdx) zipBounds
  rw [List.getElem_zipIdx (j := 0) zipBounds] at member
  simpa using member

private theorem sum_attach_zipIdx {α : Type*} (elements : List α)
    (weight : α → Nat) :
    (elements.attach.zipIdx.map fun entry => weight entry.1.1).sum =
      (elements.map weight).sum := by
  have eraseIndex :
      (elements.attach.zipIdx.map fun entry => weight entry.1.1) =
        (elements.attach.zipIdx.map Prod.fst).map
          (fun item => weight item.1) := by
    rw [List.map_map]
    rfl
  rw [eraseIndex, List.zipIdx_map_fst]
  have eraseProof :
      (elements.attach.map fun item => weight item.1) =
        (elements.attach.map Subtype.val).map weight := by
    rw [List.map_map]
    rfl
  rw [eraseProof, List.attach_map_subtype_val]

theorem root_mem (pattern : Pattern) :
    (pattern, OneHoleContext.hole) ∈ enumerate pattern := by
  cases pattern <;> simp [enumerate]

/-- Enumeration work is exactly linear in the physical pattern tree: one row
is emitted per node, including repeated equal-looking occurrences. -/
theorem length_enumerate (pattern : Pattern) :
    (enumerate pattern).length = physicalNodeCount pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [enumerate, physicalNodeCount]
  | hfvar name => simp [enumerate, physicalNodeCount]
  | happly constructor arguments recurse =>
      rw [show physicalNodeCount (.apply constructor arguments) =
          1 + physicalNodeCountList arguments by rfl]
      simp only [enumerate, List.length_cons, List.length_flatMap,
        List.length_map]
      rw [sum_attach_zipIdx arguments (fun pattern => (enumerate pattern).length)]
      have sumEquality :
          (arguments.map fun pattern => (enumerate pattern).length).sum =
            physicalNodeCountList arguments := by
        induction arguments with
        | nil => rfl
        | cons head tail inductionHypothesis =>
            simp only [List.map_cons, List.sum_cons, physicalNodeCountList]
            rw [recurse head (List.Mem.head _)]
            rw [inductionHypothesis]
            intro pattern membership
            exact recurse pattern (List.Mem.tail head membership)
      rw [sumEquality]
      omega
  | hlambda binderName body recurse =>
      simp only [enumerate, List.length_cons, List.length_map,
        physicalNodeCount]
      rw [recurse]
      omega
  | hmultiLambda arity binderNames body recurse =>
      simp only [enumerate, List.length_cons, List.length_map,
        physicalNodeCount]
      rw [recurse]
      omega
  | hsubst body replacement recurseBody recurseReplacement =>
      simp only [enumerate, List.length_cons, List.length_append,
        List.length_map, physicalNodeCount]
      rw [recurseBody, recurseReplacement]
      omega
  | hcollection collectionType elements rest recurse =>
      rw [show physicalNodeCount (.collection collectionType elements rest) =
          1 + physicalNodeCountList elements by rfl]
      simp only [enumerate, List.length_cons, List.length_flatMap,
        List.length_map]
      rw [sum_attach_zipIdx elements (fun pattern => (enumerate pattern).length)]
      have sumEquality :
          (elements.map fun pattern => (enumerate pattern).length).sum =
            physicalNodeCountList elements := by
        induction elements with
        | nil => rfl
        | cons head tail inductionHypothesis =>
            simp only [List.map_cons, List.sum_cons, physicalNodeCountList]
            rw [recurse head (List.Mem.head _)]
            rw [inductionHypothesis]
            intro pattern membership
            exact recurse pattern (List.Mem.tail head membership)
      rw [sumEquality]
      omega

/-- Every enumerated row denotes a genuine selection in the original
pattern. -/
theorem enumerate_sound {pattern focus : Pattern}
    {context : OneHoleContext}
    (membership : (focus, context) ∈ enumerate pattern) :
    Selects focus context pattern := by
  revert focus context
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro focus context membership
      simp only [enumerate, List.mem_singleton, Prod.mk.injEq] at membership
      rcases membership with ⟨rfl, rfl⟩
      exact .here
  | hfvar name =>
      intro focus context membership
      simp only [enumerate, List.mem_singleton, Prod.mk.injEq] at membership
      rcases membership with ⟨rfl, rfl⟩
      exact .here
  | happly constructor arguments recurse =>
      intro focus context membership
      simp only [enumerate, List.mem_cons] at membership
      rcases membership with root | nested
      · rcases Prod.ext_iff.mp root with ⟨rfl, rfl⟩
        exact .here
      · rw [List.mem_flatMap] at nested
        obtain ⟨entry, entryMembership, nested⟩ := nested
        rcases entry with ⟨⟨argument, argumentMembership⟩, index⟩
        rw [List.mem_map] at nested
        obtain ⟨⟨innerFocus, innerContext⟩, innerMembership, equality⟩ := nested
        cases equality
        have attachedInfo := List.mem_zipIdx entryMembership
        have indexBounds : index < arguments.attach.length := by omega
        have argumentAt : arguments.attach[index] =
            ⟨argument, argumentMembership⟩ := by
          simpa using attachedInfo.2.2.symm
        have originalBounds : index < arguments.length := by
          simpa using indexBounds
        have originalAt : arguments[index] = argument := by
          have valueEquality := congrArg Subtype.val argumentAt
          simpa using valueEquality
        have selected := recurse argument argumentMembership innerMembership
        have lifted := @Selects.apply innerFocus argument innerContext
          constructor (arguments.take index) (arguments.drop (index + 1))
          selected
        rw [← originalAt] at lifted
        simpa [take_getElem_drop arguments index originalBounds] using lifted
  | hlambda binderName body recurse =>
      intro focus context membership
      simp only [enumerate, List.mem_cons] at membership
      rcases membership with root | nested
      · rcases Prod.ext_iff.mp root with ⟨rfl, rfl⟩
        exact .here
      · rw [List.mem_map] at nested
        obtain ⟨⟨innerFocus, innerContext⟩, innerMembership, equality⟩ := nested
        cases equality
        exact .lambda (recurse innerMembership)
  | hmultiLambda arity binderNames body recurse =>
      intro focus context membership
      simp only [enumerate, List.mem_cons] at membership
      rcases membership with root | nested
      · rcases Prod.ext_iff.mp root with ⟨rfl, rfl⟩
        exact .here
      · rw [List.mem_map] at nested
        obtain ⟨⟨innerFocus, innerContext⟩, innerMembership, equality⟩ := nested
        cases equality
        exact .multiLambda (recurse innerMembership)
  | hsubst body replacement recurseBody recurseReplacement =>
      intro focus context membership
      simp only [enumerate, List.mem_cons] at membership
      rcases membership with root | nested
      · cases root
        exact .here
      · rw [List.mem_append] at nested
        rcases nested with inBody | inReplacement
        · rw [List.mem_map] at inBody
          obtain ⟨⟨innerFocus, innerContext⟩, innerMembership, equality⟩ := inBody
          cases equality
          exact .substBody (recurseBody innerMembership)
        · rw [List.mem_map] at inReplacement
          obtain ⟨⟨innerFocus, innerContext⟩, innerMembership, equality⟩ :=
            inReplacement
          cases equality
          exact .substReplacement (recurseReplacement innerMembership)
  | hcollection collectionType elements rest recurse =>
      intro focus context membership
      simp only [enumerate, List.mem_cons] at membership
      rcases membership with root | nested
      · rcases Prod.ext_iff.mp root with ⟨rfl, rfl⟩
        exact .here
      · rw [List.mem_flatMap] at nested
        obtain ⟨entry, entryMembership, nested⟩ := nested
        rcases entry with ⟨⟨element, elementMembership⟩, index⟩
        rw [List.mem_map] at nested
        obtain ⟨⟨innerFocus, innerContext⟩, innerMembership, equality⟩ := nested
        cases equality
        have attachedInfo := List.mem_zipIdx entryMembership
        have indexBounds : index < elements.attach.length := by omega
        have elementAt : elements.attach[index] =
            ⟨element, elementMembership⟩ := by
          simpa using attachedInfo.2.2.symm
        have originalBounds : index < elements.length := by
          simpa using indexBounds
        have originalAt : elements[index] = element := by
          have valueEquality := congrArg Subtype.val elementAt
          simpa using valueEquality
        have selected := recurse element elementMembership innerMembership
        have lifted := @Selects.collection innerFocus innerContext element
          collectionType (elements.take index) (elements.drop (index + 1)) rest
          selected
        rw [← originalAt] at lifted
        simpa [take_getElem_drop elements index originalBounds] using lifted

/-- Every relationally selected occurrence appears in the executable
enumeration. -/
theorem enumerate_complete {pattern focus : Pattern}
    {context : OneHoleContext}
    (selected : Selects focus context pattern) :
    (focus, context) ∈ enumerate pattern := by
  induction selected with
  | here => exact root_mem focus
  | @apply innerPattern inner constructor before after selected recurse =>
      simp only [enumerate, List.mem_cons]
      right
      rw [List.mem_flatMap]
      let arguments := before ++ innerPattern :: after
      have inBounds : before.length < arguments.length := by
        simp [arguments]
      let attachedArgument : { argument // argument ∈ arguments } :=
        ⟨arguments[before.length], List.getElem_mem inBounds⟩
      have attachedBounds : before.length < arguments.attach.length := by simpa
      have attachedAt : arguments.attach[before.length] = attachedArgument := by
        apply Subtype.ext
        simp [attachedArgument]
      refine ⟨(attachedArgument, before.length), ?_, ?_⟩
      · rw [← attachedAt]
        exact zipIdx_getElem_mem arguments.attach before.length attachedBounds
      · rw [List.mem_map]
        refine ⟨(focus, inner), ?_, ?_⟩
        · have valueEquality : attachedArgument.1 = innerPattern := by
            simp [attachedArgument, arguments]
          rw [valueEquality]
          exact recurse
        · simp
  | lambda selected recurse =>
      simp [enumerate, recurse]
  | multiLambda selected recurse =>
      simp [enumerate, recurse]
  | substBody selected recurse =>
      simp [enumerate, recurse]
  | substReplacement selected recurse =>
      simp [enumerate, recurse]
  | @collection inner innerPattern collectionType before after rest selected recurse =>
      simp only [enumerate, List.mem_cons]
      right
      rw [List.mem_flatMap]
      let elements := before ++ innerPattern :: after
      have inBounds : before.length < elements.length := by
        simp [elements]
      let attachedElement : { element // element ∈ elements } :=
        ⟨elements[before.length], List.getElem_mem inBounds⟩
      have attachedBounds : before.length < elements.attach.length := by simpa
      have attachedAt : elements.attach[before.length] = attachedElement := by
        apply Subtype.ext
        simp [attachedElement]
      refine ⟨(attachedElement, before.length), ?_, ?_⟩
      · rw [← attachedAt]
        exact zipIdx_getElem_mem elements.attach before.length attachedBounds
      · rw [List.mem_map]
        refine ⟨(focus, inner), ?_, ?_⟩
        · have valueEquality : attachedElement.1 = innerPattern := by
            simp [attachedElement, elements]
          rw [valueEquality]
          exact recurse
        · simp

theorem mem_enumerate_iff_selects {pattern focus : Pattern}
    {context : OneHoleContext} :
    (focus, context) ∈ enumerate pattern ↔ Selects focus context pattern :=
  ⟨enumerate_sound, enumerate_complete⟩

end FocusedPatternOccurrence

namespace DisplayedRewriteSite

/-- All displayed occurrences belonging to one authored rewrite row. -/
def enumerateRewrite (language : LanguageDef)
    (rewriteIndex : Fin language.rewrites.length) :
    DisplayedSiteSelection language :=
  (FocusedPatternOccurrence.enumerate
      language.rewrites[rewriteIndex].left).attach.map fun occurrence =>
    { rewriteIndex := rewriteIndex
      focus := occurrence.1.1
      context := occurrence.1.2
      selects := FocusedPatternOccurrence.enumerate_sound
        occurrence.2 }

/-- Every displayed occurrence of a rewrite belongs to that rewrite's full
enumeration. -/
theorem mem_enumerateRewrite {language : LanguageDef}
    (site : DisplayedRewriteSite language) :
    site ∈ enumerateRewrite language site.rewriteIndex := by
  unfold enumerateRewrite
  rw [List.mem_map]
  let occurrence :
      { occurrence // occurrence ∈
        FocusedPatternOccurrence.enumerate
          language.rewrites[site.rewriteIndex].left } :=
    ⟨(site.focus, site.context),
      FocusedPatternOccurrence.enumerate_complete site.selects⟩
  refine ⟨occurrence, List.mem_attach _ occurrence, ?_⟩
  apply DisplayedRewriteSite.ext <;> rfl

/-- A full rewrite-row request has exactly one site per physical node of its
source pattern. -/
theorem length_enumerateRewrite (language : LanguageDef)
    (rewriteIndex : Fin language.rewrites.length) :
    (enumerateRewrite language rewriteIndex).length =
      FocusedPatternOccurrence.physicalNodeCount
        language.rewrites[rewriteIndex].left := by
  simp [enumerateRewrite, FocusedPatternOccurrence.length_enumerate]

end DisplayedRewriteSite

namespace DisplayedSiteSelection

/-- The complete paper-style selection: every physical source occurrence of
every authored rewrite, retaining rewrite order and preorder within each
source pattern. -/
def complete (language : LanguageDef) : DisplayedSiteSelection language :=
  (List.ofFn fun index : Fin language.rewrites.length => index).flatMap
    (DisplayedRewriteSite.enumerateRewrite language)

/-- Exact number of generated contextual-modality sites in the complete
request. -/
def completeSiteCount (language : LanguageDef) : Nat :=
  ((List.ofFn fun index : Fin language.rewrites.length => index).map
    (fun rewriteIndex =>
      FocusedPatternOccurrence.physicalNodeCount
        language.rewrites[rewriteIndex].left)).sum

theorem length_complete (language : LanguageDef) :
    (complete language).length = completeSiteCount language := by
  simp [complete, completeSiteCount, List.length_flatMap,
    DisplayedRewriteSite.length_enumerateRewrite]

/-- Every well-formed displayed site occurs in the complete selection. -/
theorem mem_complete {language : LanguageDef}
    (site : DisplayedRewriteSite language) :
    site ∈ complete language := by
  unfold complete
  rw [List.mem_flatMap]
  refine ⟨site.rewriteIndex, ?_, DisplayedRewriteSite.mem_enumerateRewrite site⟩
  exact List.mem_ofFn.mpr ⟨site.rewriteIndex, rfl⟩

/-- Every sparse request is a logical sub-selection of the complete OSLF
request. -/
theorem covers_complete {language : LanguageDef}
    (selection : DisplayedSiteSelection language) :
    Covers selection (complete language) := by
  intro site _
  exact mem_complete site

/-- Structural transport sends the full source request into the full target
request.  Equality is intentionally not claimed: the target may contain
additional rewrites and sites. -/
theorem map_complete_covers
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    Covers
      (DisplayedRewriteSite.mapSelection morphism
        (complete source.language))
      (complete target.language) := by
  intro site _
  exact mem_complete site

end DisplayedSiteSelection

/-- The complete displayed language over one validated operational
language. -/
def DisplayedLanguage.complete (definition : ValidatedLanguageDef) :
    DisplayedLanguage :=
  .atSelection definition
    (DisplayedSiteSelection.complete definition.language)

/-- Every sparse request has its canonical inclusion into the full
paper-style request on the same language. -/
noncomputable def sparseToComplete (request : DisplayedLanguage) :
    request ⟶ DisplayedLanguage.complete request.definition :=
  selectionInclusion request.definition
    (DisplayedSiteSelection.covers_complete request.selectedSites)

/-! ## Positive and negative controls -/

namespace DisplayedRewriteSite.EnumerationCanary

open DisplayedRewriteSite.Canary

/-- The root and both equal-looking children are three physical
occurrences. -/
theorem repeated_source_has_three_occurrences :
    (FocusedPatternOccurrence.enumerate repeatedSourceRule.left).length = 3 := by
  simp [FocusedPatternOccurrence.enumerate, repeatedSourceRule]

theorem first_occurrence_is_complete :
    firstOccurrence ∈ DisplayedSiteSelection.complete language :=
  DisplayedSiteSelection.mem_complete firstOccurrence

theorem second_occurrence_is_complete :
    secondOccurrence ∈ DisplayedSiteSelection.complete language :=
  DisplayedSiteSelection.mem_complete secondOccurrence

/-- A one-site sparse request is strictly weaker than the complete request:
the second equal-looking occurrence cannot be recovered by syntax equality
of the focus. -/
theorem complete_not_covered_by_first :
    ¬ DisplayedSiteSelection.Covers
      (DisplayedSiteSelection.complete language) firstSelection := by
  intro coverage
  have secondInFirst := coverage secondOccurrence second_occurrence_is_complete
  have equality := List.mem_singleton.mp secondInFirst
  exact repeated_focus_occurrences_distinct
    (congrArg DisplayedRewriteSite.context equality.symm)

end DisplayedRewriteSite.EnumerationCanary

#print axioms FocusedPatternOccurrence.enumerate_sound
#print axioms FocusedPatternOccurrence.enumerate_complete
#print axioms FocusedPatternOccurrence.mem_enumerate_iff_selects
#print axioms FocusedPatternOccurrence.length_enumerate
#print axioms DisplayedRewriteSite.mem_enumerateRewrite
#print axioms DisplayedRewriteSite.length_enumerateRewrite
#print axioms DisplayedSiteSelection.mem_complete
#print axioms DisplayedSiteSelection.covers_complete
#print axioms DisplayedSiteSelection.map_complete_covers
#print axioms DisplayedSiteSelection.length_complete
#print axioms sparseToComplete
#print axioms DisplayedRewriteSite.EnumerationCanary.complete_not_covered_by_first

end Mettapedia.OSLF.Framework
