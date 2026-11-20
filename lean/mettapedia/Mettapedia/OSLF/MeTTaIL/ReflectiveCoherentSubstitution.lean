import Mathlib.Data.List.Perm.Basic
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Coherent reflective substitution

A reflective presentation compares names modulo its declared equations: the
quote-drop equation `@(*n) = n`, and unit, associativity and commutativity of
its parallel composition. `ReflectiveCanonical.canonicalEquivalent` decides
that equality. Substitution must respect it.

Reflective substitution first resolves every quotation whose payload is a
drop modulo the parallel unit and nesting (`ReflectiveSubstitution.resolveQuotes`)
and then substitutes structurally (`ReflectiveSubstitution.substituteResolved`).
This module proves that the composite respects the declared equations, for
every declaration and every action on bound indices:

* `canonicalize_members`: on resolved terms, canonicalization acts member by
  member on the declared parallel composition;
* `canonicalize_resolveQuotes`: resolution stays within the equations;
* `canonicalize_substituteResolved_resolveQuotes`: the canonical form of the
  result is computed from the canonical form of the body alone;
* `substituteReflective_respects`: hence equal terms substitute to equal
  results.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent

open Syntax Reflection Substitution ReflectiveSubstitution ReflectiveCanonical

variable (declaration : ReflectivePresentationDecl)

/-- A term the declared parallel composition keeps as a single member. -/
def IsMember (pattern : Pattern) : Prop :=
  pattern ≠ .apply declaration.parallelUnitConstructor [] ∧
    ∀ elements, pattern ≠ .collection declaration.parallelCollection elements none

mutual
  /-- No quotation's payload exposes a drop. -/
  def QuotesResolved : Pattern → Prop
    | .bvar _ => True
    | .fvar _ => True
    | .apply constructor arguments =>
        QuotesResolvedList arguments ∧
          ∀ payload, arguments = [payload] → constructor = declaration.quoteConstructor →
            exposedDrop? declaration payload = none
    | .lambda _ body => QuotesResolved body
    | .multiLambda _ _ body => QuotesResolved body
    | .subst body replacement => QuotesResolved body ∧ QuotesResolved replacement
    | .collection _ elements _ => QuotesResolvedList elements

  /-- Pointwise resolution for lists. -/
  def QuotesResolvedList : List Pattern → Prop
    | [] => True
    | pattern :: patterns => QuotesResolved pattern ∧ QuotesResolvedList patterns
end

variable {declaration}

theorem quotesResolvedList_iff (patterns : List Pattern) :
    QuotesResolvedList declaration patterns ↔ ∀ pattern ∈ patterns, QuotesResolved declaration pattern := by
  induction patterns with
  | nil => simp [QuotesResolvedList]
  | cons pattern patterns ih => simp [QuotesResolvedList, ih]

/-! ## The quote-drop step at one application -/

theorem finish_nil (label : String) :
    finishNormalizeReflectiveApply declaration label [] = .apply label [] := by
  unfold finishNormalizeReflectiveApply; split <;> rfl

theorem finish_long (label : String) (first second : Pattern) (rest : List Pattern) :
    finishNormalizeReflectiveApply declaration label (first :: second :: rest) =
      .apply label (first :: second :: rest) := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · rename_i same; simp at same
    · rfl
  · rfl

theorem finish_not_quote {label : String} (notQuote : label ≠ declaration.quoteConstructor)
    (arguments : List Pattern) :
    finishNormalizeReflectiveApply declaration label arguments = .apply label arguments := by
  unfold finishNormalizeReflectiveApply
  rw [if_neg (by simpa using notQuote)]

theorem finish_quote_plain {payload : Pattern}
    (notDrop : ∀ name, payload ≠ .apply declaration.dropConstructor [name]) :
    finishNormalizeReflectiveApply declaration declaration.quoteConstructor [payload] =
      .apply declaration.quoteConstructor [payload] := by
  unfold finishNormalizeReflectiveApply
  simp only [beq_self_eq_true, if_true]
  split
  · rename_i drop name same
    simp only [List.cons.injEq, and_true] at same
    split
    · rename_i dropped
      have dropEq : drop = declaration.dropConstructor := by simpa using dropped
      exact absurd (by rw [same, dropEq]) (notDrop name)
    · rfl
  · rfl

theorem finish_quote_drop (name : Pattern) :
    finishNormalizeReflectiveApply declaration declaration.quoteConstructor
      [.apply declaration.dropConstructor [name]] = name := by
  simp [finishNormalizeReflectiveApply]

/-! ## Members -/

theorem parallelLeaves_of_isMember {pattern : Pattern} (member : IsMember declaration pattern) :
    parallelLeaves declaration pattern = [pattern] := by
  rcases member with ⟨notUnit, notParallel⟩
  cases pattern with
  | apply constructor arguments =>
      cases arguments with
      | nil =>
          have different : constructor ≠ declaration.parallelUnitConstructor := by
            rintro rfl; exact notUnit rfl
          simp [parallelLeaves, different]
      | cons argument arguments => simp [parallelLeaves]
  | collection kind elements rest =>
      cases rest with
      | none =>
          have different : kind ≠ declaration.parallelCollection := by
            rintro rfl; exact notParallel elements rfl
          simp [parallelLeaves, different]
      | some rest => simp [parallelLeaves]
  | bvar index => simp [parallelLeaves]
  | fvar name => simp [parallelLeaves]
  | lambda binder body => simp [parallelLeaves]
  | multiLambda arity binders body => simp [parallelLeaves]
  | subst body replacement => simp [parallelLeaves]

theorem isMember_of_mem_parallelLeaves {pattern member : Pattern}
    (membership : member ∈ parallelLeaves declaration pattern) : IsMember declaration member := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; simp [IsMember]
  | hfvar name => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; simp [IsMember]
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            subst membership
            simp [IsMember, unit]
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership
          subst membership
          simp [IsMember]
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; simp [IsMember]
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; simp [IsMember]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; simp [IsMember]
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; simp [IsMember]
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            exact ih element elementMember membership
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            subst membership
            simp [IsMember, parallel]

theorem quotesResolved_of_mem_parallelLeaves {pattern member : Pattern}
    (resolved : QuotesResolved declaration pattern)
    (membership : member ∈ parallelLeaves declaration pattern) : QuotesResolved declaration member := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact resolved
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            have each := (quotesResolvedList_iff elements).mp resolved
            exact ih element elementMember (each element elementMember) membership
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            subst membership; exact resolved
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            subst membership; exact resolved
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact resolved
  | hbvar index => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact resolved
  | hfvar name => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact resolved
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact resolved
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact resolved
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact resolved

theorem exposedDrop?_eq_some_iff {payload name : Pattern} :
    exposedDrop? declaration payload = some name ↔
      parallelLeaves declaration payload = [.apply declaration.dropConstructor [name]] := by
  unfold exposedDrop?
  split
  · rename_i constructor argument leaves
    rw [leaves]
    by_cases dropped : constructor = declaration.dropConstructor
    · subst dropped; simp
    · simp [dropped]
  · rename_i notShaped
    simp only [reduceCtorEq, false_iff]
    intro leaves
    exact notShaped _ _ leaves

theorem parallelContents_singleton_of_isMember {pattern : Pattern}
    (member : IsMember declaration pattern) :
    parallelContents declaration [pattern] = [pattern] := by
  have splice : parallelSplice declaration pattern = [pattern] :=
    parallelSplice_eq_singleton_of_not_parallel declaration pattern member.2
  simp [parallelContents, splice, member.1]

theorem parallelContents_unit :
    parallelContents declaration [.apply declaration.parallelUnitConstructor []] = [] := by
  simpa [parallelContents] using parallelContents_unit_cons declaration []

theorem parallelContents_eq_flatMap (patterns : List Pattern) :
    parallelContents declaration patterns =
      patterns.flatMap fun pattern => parallelContents declaration [pattern] := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
      rw [show pattern :: patterns = [pattern] ++ patterns from rfl, parallelContents_append, ih]
      simp

/-! ## Canonical forms of resolved terms -/

private theorem canonicalize_ne_drop {payload : Pattern}
    (contents : (parallelContents declaration [canonicalize declaration payload]).Perm
      ((parallelLeaves declaration payload).map (canonicalize declaration)))
    (shapes : ∀ member ∈ parallelLeaves declaration payload,
      ∀ name, canonicalize declaration member = .apply declaration.dropConstructor [name] →
        ∃ argument, member = .apply declaration.dropConstructor [argument])
    (hidden : exposedDrop? declaration payload = none) (name : Pattern) :
    canonicalize declaration payload ≠ .apply declaration.dropConstructor [name] := by
  intro dropped
  rw [dropped, parallelContents_singleton_of_isMember (by simp [IsMember])] at contents
  obtain ⟨member, leaves, canonical⟩ :=
    List.map_eq_singleton_iff.mp (List.singleton_perm.mp contents).symm
  obtain ⟨argument, rfl⟩ := shapes member (by simp [leaves]) name canonical
  have exposed := exposedDrop?_eq_some_iff.mpr leaves
  rw [hidden] at exposed
  cases exposed

private theorem canonicalize_unary_of_members {constructor : String} {payload : Pattern}
    (contents : (parallelContents declaration [canonicalize declaration payload]).Perm
      ((parallelLeaves declaration payload).map (canonicalize declaration)))
    (shapes : ∀ member ∈ parallelLeaves declaration payload,
      ∀ name, canonicalize declaration member = .apply declaration.dropConstructor [name] →
        ∃ argument, member = .apply declaration.dropConstructor [argument])
    (hidden : constructor = declaration.quoteConstructor → exposedDrop? declaration payload = none) :
    canonicalize declaration (.apply constructor [payload]) =
      .apply constructor [canonicalize declaration payload] := by
  simp only [canonicalize, canonicalizeList]
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst quoted
    exact finish_quote_plain
      (canonicalize_ne_drop contents shapes (hidden rfl))
  · exact finish_not_quote quoted _

private theorem members_of_single {pattern : Pattern}
    (leaves : parallelLeaves declaration pattern = [pattern])
    (member : IsMember declaration (canonicalize declaration pattern))
    (shape : ∀ name, canonicalize declaration pattern = .apply declaration.dropConstructor [name] →
      ∃ argument, pattern = .apply declaration.dropConstructor [argument]) :
    (parallelContents declaration [canonicalize declaration pattern]).Perm
        ((parallelLeaves declaration pattern).map (canonicalize declaration)) ∧
      ∀ other ∈ parallelLeaves declaration pattern,
        IsMember declaration (canonicalize declaration other) ∧
          ∀ name, canonicalize declaration other = .apply declaration.dropConstructor [name] →
            ∃ argument, other = .apply declaration.dropConstructor [argument] := by
  rw [leaves, parallelContents_singleton_of_isMember member]
  refine ⟨by simp, ?_⟩
  intro other membership
  rw [List.mem_singleton] at membership
  subst membership
  exact ⟨member, shape⟩

/-- On a term whose quotations are resolved, canonicalization acts member by
member on the declared parallel composition: each member's canonical form is
again a member, and is a drop only for a drop. -/
theorem canonicalize_members {pattern : Pattern} (resolved : QuotesResolved declaration pattern) :
    (parallelContents declaration [canonicalize declaration pattern]).Perm
        ((parallelLeaves declaration pattern).map (canonicalize declaration)) ∧
      ∀ member ∈ parallelLeaves declaration pattern,
        IsMember declaration (canonicalize declaration member) ∧
          ∀ name, canonicalize declaration member = .apply declaration.dropConstructor [name] →
            ∃ argument, member = .apply declaration.dropConstructor [argument] := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      exact members_of_single rfl (by simp [canonicalize, IsMember]) (by simp [canonicalize])
  | hfvar name =>
      exact members_of_single rfl (by simp [canonicalize, IsMember]) (by simp [canonicalize])
  | hlambda binder body ih =>
      exact members_of_single rfl (by simp [canonicalize, IsMember]) (by simp [canonicalize])
  | hmultiLambda arity binders body ih =>
      exact members_of_single rfl (by simp [canonicalize, IsMember]) (by simp [canonicalize])
  | hsubst body replacement ihBody ihReplacement =>
      exact members_of_single rfl (by simp [canonicalize, IsMember]) (by simp [canonicalize])
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · subst unit
            rw [canonicalize_parallel_unit, parallelContents_unit]
            simp [parallelLeaves]
          · have canonical : canonicalize declaration (.apply constructor []) = .apply constructor [] := by
              simp [canonicalize, canonicalizeList, finish_nil]
            exact members_of_single (by simp [parallelLeaves, unit])
              (by rw [canonical]; simp [IsMember, unit]) (by simp [canonical])
      | cons payload rest =>
          cases rest with
          | nil =>
              have payloadResolved : QuotesResolved declaration payload := resolved.1.1
              have hidden : constructor = declaration.quoteConstructor →
                  exposedDrop? declaration payload = none :=
                resolved.2 payload rfl
              obtain ⟨contents, shapes⟩ := ih payload (by simp) payloadResolved
              have canonical := canonicalize_unary_of_members contents
                (fun member membership => (shapes member membership).2) hidden
              refine members_of_single (by simp [parallelLeaves])
                (by rw [canonical]; simp [IsMember]) ?_
              intro name dropped
              rw [canonical] at dropped
              simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at dropped
              exact ⟨payload, by rw [dropped.1]⟩
          | cons second more =>
              have canonical : canonicalize declaration (.apply constructor (payload :: second :: more)) =
                  .apply constructor (canonicalizeList declaration (payload :: second :: more)) := by
                simp only [canonicalize, canonicalizeList, finish_long]
              refine members_of_single (by simp [parallelLeaves])
                (by rw [canonical]; simp [IsMember, canonicalizeList]) ?_
              intro name dropped
              rw [canonical] at dropped
              simp [canonicalizeList] at dropped
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      cases rest with
      | some rest =>
          exact members_of_single (by simp [parallelLeaves])
            (by simp [canonicalize, IsMember]) (by simp [canonicalize])
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · subst parallel
            have leaves : parallelLeaves declaration
                (.collection declaration.parallelCollection elements none) =
                elements.flatMap (parallelLeaves declaration) := by
              simp [parallelLeaves, parallelLeavesList_eq_flatMap]
            rw [leaves]
            refine ⟨?_, ?_⟩
            · simp only [canonicalize, beq_self_eq_true, if_true]
              rw [parallelContents_collapse_normalized declaration
                (canonicalizeList_isCanonical declaration elements),
                normalizeParallelElements_eq_sort_parallelContents]
              refine (sortPatterns_perm _).trans ?_
              rw [parallelContents_eq_flatMap, canonicalizeList_eq_map, List.flatMap_map,
                List.map_flatMap]
              exact List.Perm.flatMap_left _ fun element membership =>
                (ih element membership (each element membership)).1
            · intro member membership
              obtain ⟨element, elementMember, membership⟩ := List.mem_flatMap.mp membership
              exact (ih element elementMember (each element elementMember)).2 member membership
          · have canonical : canonicalize declaration (.collection kind elements none) =
                .collection kind (canonicalizeList declaration elements) none := by
              simp [canonicalize, parallel]
            exact members_of_single (by simp [parallelLeaves, parallel])
              (by rw [canonical]; simp [IsMember, parallel]) (by simp [canonical])

/-- A resolved unary application keeps its constructor under canonicalization. -/
theorem canonicalize_unary_of_resolved {constructor : String} {payload : Pattern}
    (resolved : QuotesResolved declaration (.apply constructor [payload])) :
    canonicalize declaration (.apply constructor [payload]) =
      .apply constructor [canonicalize declaration payload] := by
  obtain ⟨contents, shapes⟩ := canonicalize_members resolved.1.1
  exact canonicalize_unary_of_members contents (fun member membership => (shapes member membership).2)
    (resolved.2 payload rfl)

/-- A resolved payload that exposes a drop has the canonical form of that drop. -/
theorem canonicalize_eq_of_exposedDrop {payload name : Pattern}
    (resolved : QuotesResolved declaration payload)
    (exposed : exposedDrop? declaration payload = some name) :
    canonicalize declaration payload =
      .apply declaration.dropConstructor [canonicalize declaration name] := by
  have leaves := exposedDrop?_eq_some_iff.mp exposed
  have dropResolved : QuotesResolved declaration (.apply declaration.dropConstructor [name]) :=
    quotesResolved_of_mem_parallelLeaves resolved (by simp [leaves])
  obtain ⟨contents, _⟩ := canonicalize_members resolved
  rw [leaves, List.map_singleton, canonicalize_unary_of_resolved dropResolved] at contents
  have sorted : PatternCode.sortPatterns (parallelContents declaration [canonicalize declaration payload]) =
      [.apply declaration.dropConstructor [canonicalize declaration name]] := by
    rw [PatternCode.sortPatterns_eq_of_perm contents]
    exact List.perm_singleton.mp (sortPatterns_perm _)
  rw [← collapse_normalize_singleton_of_isCanonical declaration
    (canonicalize_isCanonical declaration payload),
    normalizeParallelElements_eq_sort_parallelContents, sorted]
  rfl

/-! ## Resolution -/

/-- Resolution leaves no quotation whose payload exposes a drop. -/
theorem resolveQuotes_resolved (pattern : Pattern) :
    QuotesResolved declaration (resolveQuotes declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => trivial
  | hfvar name => trivial
  | hlambda binder body ih => exact ih
  | hmultiLambda arity binders body ih => exact ih
  | hsubst body replacement ihBody ihReplacement => exact ⟨ihBody, ihReplacement⟩
  | hcollection kind elements rest ih =>
      show QuotesResolvedList declaration (resolveQuotesList declaration elements)
      rw [resolveQuotesList_eq_map, quotesResolvedList_iff]
      intro pattern membership
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp membership
      exact ih original originalMember
  | happly constructor arguments ih =>
      have each : ∀ pattern ∈ arguments.map (resolveQuotes declaration),
          QuotesResolved declaration pattern := by
        intro pattern membership
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp membership
        exact ih original originalMember
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      generalize arguments.map (resolveQuotes declaration) = resolved at each
      match resolved, each with
      | [], _ =>
          simp only [finishResolveApply, QuotesResolved, QuotesResolvedList]
          exact ⟨trivial, by simp⟩
      | [payload], each =>
          have payloadResolved := each payload (by simp)
          simp only [finishResolveApply]
          by_cases quoted : constructor = declaration.quoteConstructor
          · simp only [quoted, if_true]
            split
            · rename_i name exposed
              have dropResolved : QuotesResolved declaration
                  (.apply declaration.dropConstructor [name]) :=
                quotesResolved_of_mem_parallelLeaves payloadResolved
                  (by rw [exposedDrop?_eq_some_iff.mp exposed]; simp)
              exact dropResolved.1.1
            · rename_i hidden
              simp only [QuotesResolved, QuotesResolvedList]
              exact ⟨⟨payloadResolved, trivial⟩, fun _ same _ => by cases same; exact hidden⟩
          · simp only [quoted, if_false, QuotesResolved, QuotesResolvedList]
            exact ⟨⟨payloadResolved, trivial⟩, fun _ _ same => same.elim⟩
      | first :: second :: rest, each =>
          simp only [finishResolveApply, QuotesResolved]
          exact ⟨(quotesResolvedList_iff _).mpr each, fun _ same => by simp at same⟩

/-- **Resolution stays within the declared equations.** -/
theorem canonicalize_resolveQuotes (pattern : Pattern) :
    canonicalize declaration (resolveQuotes declaration pattern) =
      canonicalize declaration pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => simp only [resolveQuotes, canonicalize, ih]
  | hmultiLambda arity binders body ih => simp only [resolveQuotes, canonicalize, ih]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [resolveQuotes, canonicalize, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      have mapped : (elements.map (resolveQuotes declaration)).map (canonicalize declaration) =
          elements.map (canonicalize declaration) := by
        rw [List.map_map]; exact List.map_congr_left fun pattern member => ih pattern member
      cases rest with
      | some rest =>
          simp only [resolveQuotes, canonicalize, resolveQuotesList_eq_map, canonicalizeList_eq_map,
            mapped]
      | none =>
          simp only [resolveQuotes, canonicalize, resolveQuotesList_eq_map, canonicalizeList_eq_map,
            mapped]
  | happly constructor arguments ih =>
      cases arguments with
      | nil => simp [resolveQuotes, resolveQuotesList, finishResolveApply]
      | cons payload rest =>
          have payloadIH := ih payload (by simp)
          cases rest with
          | nil =>
              simp only [resolveQuotes, resolveQuotesList, finishResolveApply]
              by_cases quoted : constructor = declaration.quoteConstructor
              · subst quoted
                simp only [if_true]
                split
                · rename_i name exposed
                  have dropped := canonicalize_eq_of_exposedDrop (resolveQuotes_resolved payload) exposed
                  rw [payloadIH] at dropped
                  simp only [canonicalize, canonicalizeList, dropped, finish_quote_drop]
                · simp only [canonicalize, canonicalizeList, payloadIH]
              · simp only [quoted, if_false, canonicalize, canonicalizeList, payloadIH]
          | cons second more =>
              have mapped : ((payload :: second :: more).map (resolveQuotes declaration)).map
                  (canonicalize declaration) = (payload :: second :: more).map (canonicalize declaration) := by
                rw [List.map_map]; exact List.map_congr_left fun pattern member => ih pattern member
              simp only [List.map_cons] at mapped
              simp only [resolveQuotes, resolveQuotesList_eq_map, List.map_cons, finishResolveApply,
                canonicalize, canonicalizeList_eq_map, mapped]

/-! ## Maps that respect the declared parallel composition -/

private theorem parallelContents_map_contents (operation : Pattern → Pattern)
    (unit : operation (.apply declaration.parallelUnitConstructor []) =
      .apply declaration.parallelUnitConstructor [])
    (parallel : ∀ elements, operation (.collection declaration.parallelCollection elements none) =
      collapseParallel declaration (normalizeParallelElements declaration (elements.map operation)))
    (canonical : ∀ pattern, IsCanonical declaration (operation pattern)) :
    ∀ {patterns : List Pattern}, IsCanonicalList declaration patterns →
      (parallelContents declaration ((parallelContents declaration patterns).map operation)).Perm
        (parallelContents declaration (patterns.map operation))
  | [], _ => by simp [parallelContents]
  | pattern :: patterns, patternsCanonical => by
      rw [show pattern :: patterns = [pattern] ++ patterns from rfl, parallelContents_append,
        List.map_append, parallelContents_append, List.map_append, parallelContents_append]
      refine List.Perm.append ?_
        (parallelContents_map_contents operation unit parallel canonical patternsCanonical.2)
      by_cases isUnit : pattern = .apply declaration.parallelUnitConstructor []
      · subst isUnit
        rw [parallelContents_unit, List.map_singleton, unit, parallelContents_unit]
        simp [parallelContents]
      · by_cases isParallel : ∃ elements, pattern = .collection declaration.parallelCollection elements none
        · obtain ⟨elements, rfl⟩ := isParallel
          have properties := patternsCanonical.1.2 ⟨rfl, rfl⟩
          have contents : parallelContents declaration
              [.collection declaration.parallelCollection elements none] = elements := by
            simp only [parallelContents, List.flatMap_cons, List.flatMap_nil, parallelSplice,
              beq_self_eq_true, if_true, List.append_nil]
            exact List.filter_eq_self.mpr fun element membership => by
              simpa using (properties.2.2 element membership).1
          have mappedCanonical : IsCanonicalList declaration (elements.map operation) :=
            isCanonicalList_of_forall declaration fun pattern membership => by
              obtain ⟨original, _, rfl⟩ := List.mem_map.mp membership
              exact canonical original
          rw [contents, List.map_singleton, parallel,
            parallelContents_collapse_normalized declaration mappedCanonical,
            normalizeParallelElements_eq_sort_parallelContents]
          exact (sortPatterns_perm _).symm
        · have member : IsMember declaration pattern :=
            ⟨isUnit, fun elements same => isParallel ⟨elements, same⟩⟩
          rw [parallelContents_singleton_of_isMember member]

theorem normalizeParallelElements_map_normalized (operation : Pattern → Pattern)
    (unit : operation (.apply declaration.parallelUnitConstructor []) =
      .apply declaration.parallelUnitConstructor [])
    (parallel : ∀ elements, operation (.collection declaration.parallelCollection elements none) =
      collapseParallel declaration (normalizeParallelElements declaration (elements.map operation)))
    (canonical : ∀ pattern, IsCanonical declaration (operation pattern))
    {patterns : List Pattern} (patternsCanonical : IsCanonicalList declaration patterns) :
    normalizeParallelElements declaration
        ((normalizeParallelElements declaration patterns).map operation) =
      normalizeParallelElements declaration (patterns.map operation) := by
  simp only [normalizeParallelElements_eq_sort_parallelContents]
  apply PatternCode.sortPatterns_eq_of_perm
  exact (parallelContents_perm declaration ((sortPatterns_perm _).map operation)).trans
    (parallelContents_map_contents operation unit parallel canonical patternsCanonical)

theorem map_collapseParallel (operation : Pattern → Pattern)
    (unit : operation (.apply declaration.parallelUnitConstructor []) =
      .apply declaration.parallelUnitConstructor [])
    (parallel : ∀ elements, operation (.collection declaration.parallelCollection elements none) =
      collapseParallel declaration (normalizeParallelElements declaration (elements.map operation)))
    (canonical : ∀ pattern, IsCanonical declaration (operation pattern)) :
    ∀ patterns : List Pattern, operation (collapseParallel declaration patterns) =
      collapseParallel declaration (normalizeParallelElements declaration (patterns.map operation))
  | [] => by
      rw [collapseParallel, unit]
      simp [normalizeParallelElements, collapseParallel, PatternCode.sortPatterns]
  | [pattern] => by
      rw [collapseParallel, List.map_singleton,
        collapse_normalize_singleton_of_isCanonical declaration (canonical pattern)]
  | first :: second :: rest => by
      rw [collapseParallel_eq_collection_of_length_ge_two declaration (by simp)]
      exact parallel _

/-! ## Coherence -/

theorem canonicalize_parallel_eq (patterns : List Pattern) :
    canonicalize declaration (.collection declaration.parallelCollection patterns none) =
      collapseParallel declaration
        (normalizeParallelElements declaration (patterns.map (canonicalize declaration))) := by
  simp only [canonicalize, beq_self_eq_true, if_true, canonicalizeList_eq_map]

/-- After canonicalization, binder elimination acts on the members of the
declared parallel composition one by one. -/
theorem canonicalize_substituteResolved_canonical_parallel (atIndex : Nat → Nat → Pattern) (depth : Nat)
    (elements : List Pattern) :
    canonicalize declaration (substituteResolved declaration atIndex depth
        (canonicalize declaration (.collection declaration.parallelCollection elements none))) =
      collapseParallel declaration (normalizeParallelElements declaration
        (elements.map fun pattern => canonicalize declaration
          (substituteResolved declaration atIndex depth (canonicalize declaration pattern)))) := by
  have unit : canonicalize declaration (substituteResolved declaration atIndex depth
        (.apply declaration.parallelUnitConstructor [])) =
      .apply declaration.parallelUnitConstructor [] := by
    rw [show substituteResolved declaration atIndex depth
        (.apply declaration.parallelUnitConstructor []) =
        .apply declaration.parallelUnitConstructor [] from rfl, canonicalize_parallel_unit]
  have parallel : ∀ patterns, canonicalize declaration (substituteResolved declaration atIndex depth
        (.collection declaration.parallelCollection patterns none)) =
      collapseParallel declaration (normalizeParallelElements declaration
        (patterns.map fun pattern => canonicalize declaration
          (substituteResolved declaration atIndex depth pattern))) := by
    intro patterns
    simp only [substituteResolved, substituteResolvedList_eq_map, canonicalize_parallel_eq,
      List.map_map, Function.comp_def]
  have collapsed := map_collapseParallel
    (operation := fun pattern => canonicalize declaration
      (substituteResolved declaration atIndex depth pattern))
    unit parallel (fun _ => canonicalize_isCanonical _ _)
    (normalizeParallelElements declaration (elements.map (canonicalize declaration)))
  have normalized := normalizeParallelElements_map_normalized
    (operation := fun pattern => canonicalize declaration
      (substituteResolved declaration atIndex depth pattern))
    unit parallel (fun _ => canonicalize_isCanonical _ _)
    (patterns := elements.map (canonicalize declaration))
    (by rw [← canonicalizeList_eq_map]; exact canonicalizeList_isCanonical declaration elements)
  rw [canonicalize_parallel_eq, collapsed, normalized, List.map_map, Function.comp_def]

theorem matchesBinder_canonicalize (depth : Nat) (pattern : Pattern) :
    matchesBinder declaration depth (canonicalize declaration pattern) =
      matchesBinder declaration depth pattern := by
  simp only [matchesBinder, ReflectiveCanonical.BinderHead.ofPattern_index_iff,
    canonicalize_idempotent]

/-- **Binder elimination on a resolved term sees only its canonical form.** -/
theorem canonicalize_substituteResolved (atIndex : Nat → Nat → Pattern) (depth : Nat) {body : Pattern}
    (resolved : QuotesResolved declaration body) :
    canonicalize declaration (substituteResolved declaration atIndex depth body) =
      canonicalize declaration
        (substituteResolved declaration atIndex depth (canonicalize declaration body)) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih =>
      simp only [substituteResolved, canonicalize]
      rw [ih (depth + 1) resolved]
  | hmultiLambda arity binders body ih =>
      simp only [substituteResolved, canonicalize]
      rw [ih (depth + arity) resolved]
  | hsubst body value ihBody ihValue =>
      simp only [substituteResolved, canonicalize]
      rw [ihBody (depth + 1) resolved.1, ihValue depth resolved.2]
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          simp [canonicalize, canonicalizeList, finish_nil, substituteResolved]
      | cons payload rest =>
          cases rest with
          | nil =>
              have payloadResolved : QuotesResolved declaration payload := resolved.1.1
              have payloadIH := ih payload (by simp) depth payloadResolved
              rw [canonicalize_unary_of_resolved resolved]
              by_cases quoted : constructor = declaration.quoteConstructor
              · subst quoted
                simp only [substituteResolved, if_true]
                rw [← canonicalize_unary_of_resolved resolved, canonicalize_idempotent]
              · by_cases dropped : constructor = declaration.dropConstructor
                · subst dropped
                  simp only [substituteResolved, quoted, if_false, if_true,
                    matchesBinder_canonicalize]
                  split
                  · rfl
                  · simp only [canonicalize, canonicalizeList, finish_not_quote quoted,
                      payloadIH]
                · simp only [substituteResolved, quoted, dropped, if_false, canonicalize,
                    canonicalizeList, finish_not_quote quoted, payloadIH]
          | cons second more =>
              have each := (quotesResolvedList_iff _).mp resolved.1
              have mapped : (payload :: second :: more).map
                  (fun pattern => canonicalize declaration
                    (substituteResolved declaration atIndex depth pattern)) =
                  (payload :: second :: more).map (fun pattern => canonicalize declaration
                    (substituteResolved declaration atIndex depth
                      (canonicalize declaration pattern))) :=
                List.map_congr_left fun pattern member => ih pattern member depth (each pattern member)
              simp only [List.map_cons] at mapped
              simp only [canonicalize, canonicalizeList_eq_map, List.map_cons,
                finish_long, substituteResolved, substituteResolvedList_eq_map,
                List.map_map, Function.comp_def, mapped]
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      have mapped : elements.map (fun pattern => canonicalize declaration
            (substituteResolved declaration atIndex depth pattern)) =
          elements.map (fun pattern => canonicalize declaration
            (substituteResolved declaration atIndex depth (canonicalize declaration pattern))) :=
        List.map_congr_left fun pattern member => ih pattern member depth (each pattern member)
      cases rest with
      | some rest =>
          simp only [substituteResolved, substituteResolvedList_eq_map, canonicalize,
            canonicalizeList_eq_map, List.map_map, Function.comp_def, mapped]
      | none =>
          by_cases isParallel : kind = declaration.parallelCollection
          · subst isParallel
            rw [canonicalize_substituteResolved_canonical_parallel, ← mapped]
            simp only [substituteResolved, substituteResolvedList_eq_map,
              canonicalize_parallel_eq, List.map_map, Function.comp_def]
          · have notParallel : (kind == declaration.parallelCollection) = false := by
              simpa using isParallel
            simp only [substituteResolved, substituteResolvedList_eq_map, canonicalize,
              notParallel, Bool.false_eq_true, if_false, canonicalizeList_eq_map, List.map_map,
              Function.comp_def, mapped]

/-- **Coherence.** Resolving quotations and then substituting structurally
yields a canonical form computed from the canonical form of the body alone,
for every declaration, index action and depth. -/
theorem canonicalize_substituteResolved_resolveQuotes (atIndex : Nat → Nat → Pattern) (depth : Nat)
    (body : Pattern) :
    canonicalize declaration
        (substituteResolved declaration atIndex depth (resolveQuotes declaration body)) =
      canonicalize declaration
        (substituteResolved declaration atIndex depth (canonicalize declaration body)) := by
  rw [canonicalize_substituteResolved atIndex depth (resolveQuotes_resolved body),
    canonicalize_resolveQuotes]

/-- **Reflective substitution respects the declared equations**: equal names
and processes substitute to equal results, at every depth and for every
replacement. -/
theorem substituteReflective_respects (depth : Nat) (replacementName : Pattern)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (substituteReflective declaration depth replacementName left)
      (substituteReflective declaration depth replacementName right) = true := by
  rw [canonicalEquivalent_eq_true_iff] at same ⊢
  simp only [substituteReflective]
  rw [canonicalize_substituteResolved_resolveQuotes, canonicalize_substituteResolved_resolveQuotes,
    same]

/-! ## Substitution under a declared quote scope respects the equations -/

/-- After canonicalization, the traversal acts on the members of the declared
parallel composition one by one. -/
theorem canonicalize_substituteViewed_canonical_parallel (insideQuote atIndex : Nat → Nat → Pattern)
    (depth : Nat) (elements : List Pattern) :
    canonicalize declaration (substituteViewed declaration insideQuote atIndex depth
        (canonicalize declaration (.collection declaration.parallelCollection elements none))) =
      collapseParallel declaration (normalizeParallelElements declaration
        (elements.map fun pattern => canonicalize declaration
          (substituteViewed declaration insideQuote atIndex depth (canonicalize declaration pattern)))) := by
  have unit : canonicalize declaration (substituteViewed declaration insideQuote atIndex depth
        (.apply declaration.parallelUnitConstructor [])) =
      .apply declaration.parallelUnitConstructor [] := by
    rw [show substituteViewed declaration insideQuote atIndex depth
        (.apply declaration.parallelUnitConstructor []) =
        .apply declaration.parallelUnitConstructor [] from rfl, canonicalize_parallel_unit]
  have parallel : ∀ patterns, canonicalize declaration (substituteViewed declaration insideQuote
        atIndex depth (.collection declaration.parallelCollection patterns none)) =
      collapseParallel declaration (normalizeParallelElements declaration
        (patterns.map fun pattern => canonicalize declaration
          (substituteViewed declaration insideQuote atIndex depth pattern))) := by
    intro patterns
    simp only [substituteViewed, substituteViewedList_eq_map, canonicalize_parallel_eq,
      List.map_map, Function.comp_def]
  have collapsed := map_collapseParallel
    (operation := fun pattern => canonicalize declaration
      (substituteViewed declaration insideQuote atIndex depth pattern))
    unit parallel (fun _ => canonicalize_isCanonical _ _)
    (normalizeParallelElements declaration (elements.map (canonicalize declaration)))
  have normalized := normalizeParallelElements_map_normalized
    (operation := fun pattern => canonicalize declaration
      (substituteViewed declaration insideQuote atIndex depth pattern))
    unit parallel (fun _ => canonicalize_isCanonical _ _)
    (patterns := elements.map (canonicalize declaration))
    (by rw [← canonicalizeList_eq_map]; exact canonicalizeList_isCanonical declaration elements)
  rw [canonicalize_parallel_eq, collapsed, normalized, List.map_map, Function.comp_def]

/-- **The traversal sees only the canonical form of a resolved body**, for
every pair of actions: entering a quotation preserves the equations because the
quote-drop equation is re-applied to the canonical form of the entered payload. -/
theorem canonicalize_substituteViewed (insideQuote : Nat → Nat → Pattern) {body : Pattern}
    (resolved : QuotesResolved declaration body) (atIndex : Nat → Nat → Pattern) (depth : Nat) :
    canonicalize declaration (substituteViewed declaration insideQuote atIndex depth body) =
      canonicalize declaration
        (substituteViewed declaration insideQuote atIndex depth (canonicalize declaration body)) := by
  induction body using Pattern.inductionOn generalizing atIndex depth with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih =>
      simp only [substituteViewed, canonicalize]
      rw [ih resolved atIndex (depth + 1)]
  | hmultiLambda arity binders body ih =>
      simp only [substituteViewed, canonicalize]
      rw [ih resolved atIndex (depth + arity)]
  | hsubst body value ihBody ihValue =>
      simp only [substituteViewed, canonicalize]
      rw [ihBody resolved.1 atIndex (depth + 1), ihValue resolved.2 atIndex depth]
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          simp [canonicalize, canonicalizeList, finish_nil, substituteViewed]
      | cons payload rest =>
          cases rest with
          | nil =>
              have payloadResolved : QuotesResolved declaration payload := resolved.1.1
              rw [canonicalize_unary_of_resolved resolved]
              by_cases isQuote : constructor = declaration.quoteConstructor
              · subst isQuote
                simp only [substituteViewed, if_true, canonicalize, canonicalizeList,
                  ih payload (by simp) payloadResolved insideQuote depth]
              · by_cases isDrop : constructor = declaration.dropConstructor
                · subst isDrop
                  simp only [substituteViewed, isQuote, if_false, if_true,
                    matchesBinder_canonicalize]
                  split
                  · rfl
                  · simp only [canonicalize, canonicalizeList, finish_not_quote isQuote,
                      ih payload (by simp) payloadResolved atIndex depth]
                · simp only [substituteViewed, isQuote, isDrop, if_false, canonicalize,
                    canonicalizeList, finish_not_quote isQuote,
                    ih payload (by simp) payloadResolved atIndex depth]
          | cons second more =>
              have each := (quotesResolvedList_iff _).mp resolved.1
              have mapped : (payload :: second :: more).map
                  (fun pattern => canonicalize declaration
                    (substituteViewed declaration insideQuote atIndex depth pattern)) =
                  (payload :: second :: more).map (fun pattern => canonicalize declaration
                    (substituteViewed declaration insideQuote atIndex depth
                      (canonicalize declaration pattern))) :=
                List.map_congr_left fun pattern member =>
                  ih pattern member (each pattern member) atIndex depth
              simp only [List.map_cons] at mapped
              simp only [canonicalize, canonicalizeList_eq_map, List.map_cons,
                finish_long, substituteViewed, substituteViewedList_eq_map,
                List.map_map, Function.comp_def, mapped]
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      have mapped : elements.map (fun pattern => canonicalize declaration
            (substituteViewed declaration insideQuote atIndex depth pattern)) =
          elements.map (fun pattern => canonicalize declaration
            (substituteViewed declaration insideQuote atIndex depth
              (canonicalize declaration pattern))) :=
        List.map_congr_left fun pattern member => ih pattern member (each pattern member) atIndex depth
      cases rest with
      | some rest =>
          simp only [substituteViewed, substituteViewedList_eq_map, canonicalize,
            canonicalizeList_eq_map, List.map_map, Function.comp_def, mapped]
      | none =>
          by_cases isParallel : kind = declaration.parallelCollection
          · subst isParallel
            rw [canonicalize_substituteViewed_canonical_parallel, ← mapped]
            simp only [substituteViewed, substituteViewedList_eq_map,
              canonicalize_parallel_eq, List.map_map, Function.comp_def]
          · have notParallel : (kind == declaration.parallelCollection) = false := by
              simpa using isParallel
            simp only [substituteViewed, substituteViewedList_eq_map, canonicalize,
              notParallel, Bool.false_eq_true, if_false, canonicalizeList_eq_map, List.map_map,
              Function.comp_def, mapped]

/-- Resolving first, the result's canonical form is computed from the body's
canonical form alone. -/
theorem canonicalize_substituteViewed_resolveQuotes (insideQuote atIndex : Nat → Nat → Pattern)
    (depth : Nat) (body : Pattern) :
    canonicalize declaration
        (substituteViewed declaration insideQuote atIndex depth (resolveQuotes declaration body)) =
      canonicalize declaration
        (substituteViewed declaration insideQuote atIndex depth (canonicalize declaration body)) := by
  rw [canonicalize_substituteViewed insideQuote (resolveQuotes_resolved body),
    canonicalize_resolveQuotes]

/-- **Every action pair respects the declared equations**: equivalent bodies
give equivalent results. -/
theorem substituteViewed_respects (insideQuote atIndex : Nat → Nat → Pattern) (depth : Nat)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration
        (substituteViewed declaration insideQuote atIndex depth (resolveQuotes declaration left))
        (substituteViewed declaration insideQuote atIndex depth (resolveQuotes declaration right)) =
      true := by
  rw [canonicalEquivalent_eq_true_iff] at same ⊢
  rw [canonicalize_substituteViewed_resolveQuotes, canonicalize_substituteViewed_resolveQuotes, same]

/-- **Substitution under every quote scope respects the declared equations.** -/
theorem substituteScoped_respects (scope : QuoteScope) (atIndex : Nat → Nat → Pattern) (depth : Nat)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (substituteScoped declaration scope atIndex depth left)
      (substituteScoped declaration scope atIndex depth right) = true := by
  cases scope with
  | closed =>
      rw [canonicalEquivalent_eq_true_iff] at same ⊢
      simp only [substituteScoped]
      rw [canonicalize_substituteResolved_resolveQuotes, canonicalize_substituteResolved_resolveQuotes,
        same]
  | reaching view => exact substituteViewed_respects (view.inside atIndex) atIndex depth same

/-- **The declared substitution respects the declared equations.** -/
theorem substituteDeclared_respects (depth : Nat) (replacementName : Pattern)
    {left right : Pattern} (same : canonicalEquivalent declaration left right = true) :
    canonicalEquivalent declaration (substituteDeclared declaration depth replacementName left)
      (substituteDeclared declaration depth replacementName right) = true :=
  substituteScoped_respects declaration.quoteScope _ depth same


/-! ## Resolved terms are fixed points -/

theorem normalizeReflectiveList_eq_map (patterns : List Pattern) :
    normalizeReflectiveList declaration patterns = patterns.map (normalizeReflective declaration) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [normalizeReflectiveList, ih]

/-- A term whose quotations are resolved is already in quote-drop normal form. -/
theorem normalizeReflective_of_resolved {pattern : Pattern}
    (resolved : QuotesResolved declaration pattern) :
    normalizeReflective declaration pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => simp only [normalizeReflective, ih resolved]
  | hmultiLambda arity binders body ih => simp only [normalizeReflective, ih resolved]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [normalizeReflective, ihBody resolved.1, ihReplacement resolved.2]
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      have mapped : normalizeReflectiveList declaration elements = elements := by
        rw [normalizeReflectiveList_eq_map]
        exact (List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)
      simp only [normalizeReflective, mapped]
  | happly constructor arguments ih =>
      have each := (quotesResolvedList_iff arguments).mp resolved.1
      have mapped : normalizeReflectiveList declaration arguments = arguments := by
        rw [normalizeReflectiveList_eq_map]
        exact (List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)
      simp only [normalizeReflective, mapped]
      match arguments with
      | [] => exact finish_nil constructor
      | first :: second :: rest => exact finish_long constructor _ _ _
      | [payload] =>
          by_cases quoted : constructor = declaration.quoteConstructor
          · subst quoted
            apply finish_quote_plain
            rintro name rfl
            have hidden := resolved.2 _ rfl rfl
            rw [show exposedDrop? declaration (.apply declaration.dropConstructor [name]) = some name from
              exposedDrop?_eq_some_iff.mpr (parallelLeaves_of_isMember (by simp [IsMember]))] at hidden
            cases hidden
          · exact finish_not_quote quoted _

/-- Resolution fixes a term whose quotations are resolved. -/
theorem resolveQuotes_of_resolved {pattern : Pattern}
    (resolved : QuotesResolved declaration pattern) :
    resolveQuotes declaration pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => simp only [resolveQuotes, ih resolved]
  | hmultiLambda arity binders body ih => simp only [resolveQuotes, ih resolved]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [resolveQuotes, ihBody resolved.1, ihReplacement resolved.2]
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      rw [(List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)]
  | happly constructor arguments ih =>
      have each := (quotesResolvedList_iff arguments).mp resolved.1
      have mapped : arguments.map (resolveQuotes declaration) = arguments :=
        (List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)
      simp only [resolveQuotes, resolveQuotesList_eq_map, mapped]
      match arguments, resolved with
      | [], _ => rfl
      | first :: second :: rest, _ => rfl
      | [payload], resolved =>
          simp only [finishResolveApply]
          by_cases quoted : constructor = declaration.quoteConstructor
          · simp only [quoted, if_true, resolved.2 payload rfl quoted]
          · simp [quoted]

/-! ## Scope -/

open ScopedPattern in
theorem isWellScopedAt_of_mem_parallelLeaves {pattern member : Pattern} {depth : Nat}
    (safe : pattern.isWellScopedAt depth = true)
    (membership : member ∈ parallelLeaves declaration pattern) :
    member.isWellScopedAt depth = true := by
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            exact ih element elementMember
              ((isWellScopedListAt_eq_true_iff _ _).mp safe element elementMember) membership
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            subst membership; exact safe
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            subst membership; exact safe
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hbvar index => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hfvar name => simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; subst membership; exact safe

open ScopedPattern in
/-- Resolving quotations introduces no dangling bound index. -/
theorem resolveQuotes_isWellScopedAt {pattern : Pattern} {depth : Nat}
    (safe : pattern.isWellScopedAt depth = true) :
    (resolveQuotes declaration pattern).isWellScopedAt depth = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => exact safe
  | hfvar name => rfl
  | hlambda binder body ih => exact ih safe
  | hmultiLambda arity binders body ih => exact ih safe
  | hsubst body replacement ihBody ihReplacement =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true, resolveQuotes] at safe ⊢
      exact ⟨ihBody safe.1, ihReplacement safe.2⟩
  | hcollection kind elements rest ih =>
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      show Pattern.isWellScopedListAt depth (resolveQuotesList declaration elements) = true
      rw [resolveQuotesList_eq_map, isWellScopedListAt_eq_true_iff]
      intro p member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (each original originalMember)
  | happly constructor arguments ih =>
      have each := (isWellScopedListAt_eq_true_iff _ _).mp safe
      have mappedSafe : ∀ p ∈ arguments.map (resolveQuotes declaration), p.isWellScopedAt depth = true := by
        intro p member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact ih original originalMember (each original originalMember)
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      generalize arguments.map (resolveQuotes declaration) = resolved at mappedSafe
      match resolved, mappedSafe with
      | [], _ => rfl
      | first :: second :: rest, mappedSafe =>
          show Pattern.isWellScopedListAt depth (first :: second :: rest) = true
          exact (isWellScopedListAt_eq_true_iff _ _).mpr mappedSafe
      | [payload], mappedSafe =>
          have payloadSafe := mappedSafe payload (by simp)
          have plain : (Pattern.apply constructor [payload]).isWellScopedAt depth = true := by
            simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using payloadSafe
          simp only [finishResolveApply]
          split
          · split
            · rename_i name exposed
              have dropSafe := isWellScopedAt_of_mem_parallelLeaves payloadSafe
                (by rw [exposedDrop?_eq_some_iff.mp exposed]; exact List.mem_singleton_self _)
              simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using dropSafe
            · exact plain
          · exact plain

/-- Substitution whose index action fixes every index below the current
depth fixes a term with no index at or above it. -/
theorem substituteResolved_of_isWellScopedAt (atIndex : Nat → Nat → Pattern)
    (below : ∀ level index, index < level → atIndex level index = .bvar index)
    {depth : Nat} {pattern : Pattern} (safe : pattern.isWellScopedAt depth = true) :
    substituteResolved declaration atIndex depth pattern = pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      exact below depth index (by simpa [Pattern.isWellScopedAt] using safe)
  | hfvar name => rfl
  | hlambda binder body ih => simp only [substituteResolved, ih safe]
  | hmultiLambda arity binders body ih => simp only [substituteResolved, ih safe]
  | hsubst body value ihBody ihValue =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe
      simp only [substituteResolved, ihBody safe.1, ihValue safe.2]
  | hcollection kind elements rest ih =>
      have each := (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp safe
      simp only [substituteResolved, substituteResolvedList_eq_map]
      rw [(List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)]
  | happly constructor arguments ih =>
      have each := (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp safe
      match arguments, each with
      | [], _ => rfl
      | first :: second :: rest, each =>
          simp only [substituteResolved, substituteResolvedList_eq_map]
          rw [(List.map_congr_left fun p m => ih p m (each p m)).trans (List.map_id' _)]
      | [payload], each =>
          have payloadSafe := each payload (by simp)
          have miss : matchesBinder declaration depth payload = false := by
            simp only [matchesBinder, decide_eq_false_iff_not,
              ReflectiveCanonical.BinderHead.ofPattern_index_iff]
            intro binder
            have canonicalSafe := canonicalize_scoped declaration payloadSafe
            rw [binder] at canonicalSafe
            simp [Pattern.isWellScopedAt] at canonicalSafe
          simp only [substituteResolved, miss, Bool.false_eq_true, if_false, ite_self,
            ih payload (by simp) payloadSafe]

/-- Two index actions that agree on every index in scope give the same
substitution. -/
theorem substituteResolved_congr {first second : Nat → Nat → Pattern} {depth : Nat}
    (agree : ∀ level index, depth ≤ level → index ≤ level → first level index = second level index)
    {pattern : Pattern} (safe : pattern.isWellScopedAt (depth + 1) = true) :
    substituteResolved declaration first depth pattern =
      substituteResolved declaration second depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      exact agree depth index le_rfl (by simpa [Pattern.isWellScopedAt, Nat.lt_succ_iff] using safe)
  | hfvar name => rfl
  | hlambda binder body ih =>
      simp only [substituteResolved]
      rw [ih (fun level index within below => agree level index (by omega) below)
        (by simpa [Pattern.isWellScopedAt] using safe)]
  | hmultiLambda arity binders body ih =>
      simp only [substituteResolved]
      rw [ih (fun level index within below => agree level index (by omega) below)
        (by simpa [Pattern.isWellScopedAt, Nat.add_right_comm] using safe)]
  | hsubst body value ihBody ihValue =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe
      simp only [substituteResolved]
      rw [ihBody (fun level index within below => agree level index (by omega) below) safe.1,
        ihValue agree safe.2]
  | hcollection kind elements rest ih =>
      have each := (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp safe
      simp only [substituteResolved, substituteResolvedList_eq_map]
      rw [List.map_congr_left fun p m => ih p m agree (each p m)]
  | happly constructor arguments ih =>
      have each := (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp safe
      match arguments, each with
      | [], _ => rfl
      | first :: second :: rest, each =>
          simp only [substituteResolved, substituteResolvedList_eq_map]
          rw [List.map_congr_left fun p m => ih p m agree (each p m)]
      | [payload], each =>
          simp only [substituteResolved, agree depth depth le_rfl le_rfl,
            ih payload (by simp) agree (each payload (by simp))]

theorem receive_cases (constructor : String) (name : Pattern) :
    receive declaration constructor name = .apply constructor [name] ∨
      ∃ process, name = .apply declaration.quoteConstructor [process] ∧
        receive declaration constructor name = process := by
  unfold receive
  split
  · rename_i quote process
    by_cases quoted : quote = declaration.quoteConstructor
    · subst quoted; exact .inr ⟨process, rfl, by simp⟩
    · exact .inl (by simp [quoted])
  · exact .inl rfl

theorem finish_cases (constructor : String) (arguments : List Pattern) :
    finishNormalizeReflectiveApply declaration constructor arguments = .apply constructor arguments ∨
      ∃ name, constructor = declaration.quoteConstructor ∧
        arguments = [.apply declaration.dropConstructor [name]] ∧
        finishNormalizeReflectiveApply declaration constructor arguments = name := by
  unfold finishNormalizeReflectiveApply
  split
  · rename_i quoted
    split
    · rename_i drop name
      split
      · rename_i dropped
        exact .inr ⟨name, by simpa using quoted,
          by rw [show drop = declaration.dropConstructor by simpa using dropped], rfl⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-- Resolution subsumes the literal quote-drop normal form: resolving a term
or its literal normal form gives the same result. -/
theorem resolveQuotes_normalizeReflective
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (pattern : Pattern) :
    resolveQuotes declaration (normalizeReflective declaration pattern) =
      resolveQuotes declaration pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => simp only [normalizeReflective, resolveQuotes, ih]
  | hmultiLambda arity binders body ih => simp only [normalizeReflective, resolveQuotes, ih]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [normalizeReflective, resolveQuotes, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [normalizeReflective, resolveQuotes, resolveQuotesList_eq_map,
        normalizeReflectiveList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun p m => ih p m
  | happly constructor arguments ih =>
      have mapped : (arguments.map (normalizeReflective declaration)).map (resolveQuotes declaration) =
          arguments.map (resolveQuotes declaration) := by
        rw [List.map_map]; exact List.map_congr_left fun p m => ih p m
      simp only [normalizeReflective, normalizeReflectiveList_eq_map]
      rcases finish_cases (declaration := declaration) constructor
          (arguments.map (normalizeReflective declaration)) with plain | ⟨name, quoted, single, result⟩
      · rw [plain]
        simp only [resolveQuotes, resolveQuotesList_eq_map, mapped]
      · rw [result]
        obtain ⟨payload, rfl, payloadNormal⟩ := List.map_eq_singleton_iff.mp single
        subst quoted
        have payloadIH := ih payload (by simp)
        rw [payloadNormal] at payloadIH
        have dropResolved : resolveQuotes declaration (.apply declaration.dropConstructor [name]) =
            .apply declaration.dropConstructor [resolveQuotes declaration name] := by
          simp [resolveQuotes, resolveQuotesList, finishResolveApply, distinct]
        rw [dropResolved] at payloadIH
        simp only [resolveQuotes, resolveQuotesList, finishResolveApply, if_true, ← payloadIH]
        rw [show exposedDrop? declaration (.apply declaration.dropConstructor [resolveQuotes declaration name]) =
            some (resolveQuotes declaration name) from
          exposedDrop?_eq_some_iff.mpr (parallelLeaves_of_isMember (by simp [IsMember]))]

/-! ## Quotations that expose a drop only literally -/

section Literal

variable (declaration)

/-- A quotation's payload exposes a drop only as that literal drop. -/
def exposesLiterally (payload : Pattern) : Bool :=
  match exposedDrop? declaration payload with
  | some name => decide (payload = .apply declaration.dropConstructor [name])
  | none => true

mutual
  /-- No quotation of a drop hides behind the declared parallel unit or
  nesting. -/
  def quotesLiteral : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply _ [] => true
    | .apply constructor [payload] =>
        (constructor != declaration.quoteConstructor || exposesLiterally declaration payload) &&
          quotesLiteral payload
    | .apply _ (first :: second :: rest) => quotesLiteralList (first :: second :: rest)
    | .lambda _ body => quotesLiteral body
    | .multiLambda _ _ body => quotesLiteral body
    | .subst body replacement => quotesLiteral body && quotesLiteral replacement
    | .collection _ elements _ => quotesLiteralList elements

  /-- List recursion for `quotesLiteral`. -/
  def quotesLiteralList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => quotesLiteral pattern && quotesLiteralList patterns
end


end Literal

theorem quotesLiteralList_iff (patterns : List Pattern) :
    quotesLiteralList declaration patterns = true ↔
      ∀ pattern ∈ patterns, quotesLiteral declaration pattern = true := by
  induction patterns with
  | nil => simp [quotesLiteralList]
  | cons pattern patterns ih => simp [quotesLiteralList, ih]

theorem quotesLiteral_args {constructor : String} {arguments : List Pattern}
    (literal : quotesLiteral declaration (.apply constructor arguments) = true) :
    ∀ argument ∈ arguments, quotesLiteral declaration argument = true := by
  match arguments, literal with
  | [], _ => simp
  | [payload], literal =>
      simp only [quotesLiteral, Bool.and_eq_true] at literal
      simpa using literal.2
  | first :: second :: rest, literal =>
      simp only [quotesLiteral] at literal
      exact (quotesLiteralList_iff _).mp literal

/-- A resolved term exposes drops only literally under its quotations. -/
theorem quotesLiteral_of_resolved {pattern : Pattern} (resolved : QuotesResolved declaration pattern) :
    quotesLiteral declaration pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => exact ih resolved
  | hmultiLambda arity binders body ih => exact ih resolved
  | hsubst body value ihBody ihValue =>
      simp only [quotesLiteral, Bool.and_eq_true]
      exact ⟨ihBody resolved.1, ihValue resolved.2⟩
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      exact (quotesLiteralList_iff elements).mpr fun p m => ih p m (each p m)
  | happly constructor arguments ih =>
      have each := (quotesResolvedList_iff arguments).mp resolved.1
      match arguments, resolved, each, ih with
      | [], _, _, _ => rfl
      | first :: second :: rest, _, each, ih =>
          exact (quotesLiteralList_iff _).mpr fun p m => ih p m (each p m)
      | [payload], resolved, each, ih =>
          simp only [quotesLiteral, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
          refine ⟨?_, ih payload (by simp) (each payload (by simp))⟩
          by_cases quoted : constructor = declaration.quoteConstructor
          · right
            simp [exposesLiterally, resolved.2 payload rfl quoted]
          · exact .inl quoted

/-- The literal quote-drop normal form stays within the declared equations. -/
theorem canonicalize_normalizeReflective
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (pattern : Pattern) :
    canonicalize declaration (normalizeReflective declaration pattern) =
      canonicalize declaration pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => simp only [normalizeReflective, canonicalize, ih]
  | hmultiLambda arity binders body ih => simp only [normalizeReflective, canonicalize, ih]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [normalizeReflective, canonicalize, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      have mapped : (elements.map (normalizeReflective declaration)).map (canonicalize declaration) =
          elements.map (canonicalize declaration) := by
        rw [List.map_map]; exact List.map_congr_left fun pattern member => ih pattern member
      cases rest with
      | some rest =>
          simp only [normalizeReflective, canonicalize, normalizeReflectiveList_eq_map,
            canonicalizeList_eq_map, mapped]
      | none =>
          simp only [normalizeReflective, canonicalize, normalizeReflectiveList_eq_map,
            canonicalizeList_eq_map, mapped]
  | happly constructor arguments ih =>
      have mapped : (arguments.map (normalizeReflective declaration)).map (canonicalize declaration) =
          arguments.map (canonicalize declaration) := by
        rw [List.map_map]; exact List.map_congr_left fun pattern member => ih pattern member
      simp only [normalizeReflective, normalizeReflectiveList_eq_map]
      rcases finish_cases (declaration := declaration) constructor
          (arguments.map (normalizeReflective declaration)) with plain | ⟨name, quoted, single, result⟩
      · rw [plain]
        simp only [canonicalize, canonicalizeList_eq_map]
        exact congrArg _ mapped
      · rw [result]
        obtain ⟨payload, rfl, payloadNormal⟩ := List.map_eq_singleton_iff.mp single
        subst quoted
        have payloadIH := ih payload (by simp)
        rw [payloadNormal] at payloadIH
        simp only [canonicalize, canonicalizeList, finish_not_quote distinct] at payloadIH ⊢
        rw [← payloadIH, finish_quote_drop]

/-! ## Equations at one application -/

theorem normalizeReflective_unary_of_ne_quote {constructor : String}
    (notQuote : constructor ≠ declaration.quoteConstructor) (payload : Pattern) :
    normalizeReflective declaration (.apply constructor [payload]) =
      .apply constructor [normalizeReflective declaration payload] := by
  simp only [normalizeReflective, normalizeReflectiveList, finish_not_quote notQuote]

theorem normalizeReflective_apply_long (constructor : String) (first second : Pattern)
    (rest : List Pattern) :
    normalizeReflective declaration (.apply constructor (first :: second :: rest)) =
      .apply constructor ((first :: second :: rest).map (normalizeReflective declaration)) := by
  simp only [normalizeReflective, normalizeReflectiveList_eq_map, List.map_cons, finish_long]

theorem substituteResolved_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (atIndex : Nat → Nat → Pattern) (depth : Nat) (payload : Pattern) :
    substituteResolved declaration atIndex depth (.apply declaration.dropConstructor [payload]) =
      if matchesBinder declaration depth payload then
        receive declaration declaration.dropConstructor (atIndex depth depth)
      else .apply declaration.dropConstructor [substituteResolved declaration atIndex depth payload] := by
  simp [substituteResolved, distinct]

theorem substituteResolved_unary_plain {constructor : String}
    (notQuote : constructor ≠ declaration.quoteConstructor)
    (notDrop : constructor ≠ declaration.dropConstructor)
    (atIndex : Nat → Nat → Pattern) (depth : Nat) (payload : Pattern) :
    substituteResolved declaration atIndex depth (.apply constructor [payload]) =
      .apply constructor [substituteResolved declaration atIndex depth payload] := by
  simp [substituteResolved, notQuote, notDrop]

theorem substituteResolved_apply_long (atIndex : Nat → Nat → Pattern) (depth : Nat)
    (constructor : String) (first second : Pattern) (rest : List Pattern) :
    substituteResolved declaration atIndex depth (.apply constructor (first :: second :: rest)) =
      .apply constructor ((first :: second :: rest).map (substituteResolved declaration atIndex depth)) := by
  simp only [substituteResolved, substituteResolvedList_eq_map]

end Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent
