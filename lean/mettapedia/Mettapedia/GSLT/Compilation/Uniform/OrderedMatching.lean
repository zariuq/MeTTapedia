import Mettapedia.OSLF.Framework.RuleInstanceSteps

/-!
# Exact matching of ordered vectors, a rest included

`Match.isMatchCorrectAux` stops at collections, because matching a bag may permute it.
A vector is ordered, so its match is exact, a rest included, on one condition: the
matched term is data, with no open rest of its own (`isData`). The matcher ignores a
rest of the term.

* `match_exact`: a match reconstructs the term under every extension of its bindings.
* `match_binds`: a match binds every variable and settles every rest as a vector.
* `match_complete`: an instance under a witness that settles the rests is matched.
* `match_data`, `instance_data`, `settled_of_data`: data binds data, an instance over
  data is data, and an instance that is data has settled its rests.
* `instance_agree`: an instance depends on the named variables alone.

Controls: a head and a tail are taken from a vector (`Controls.head_and_tail`), and a
term with an open rest is matched without being reconstructed
(`Controls.open_term_not_exact`), so `isData` is needed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.OrderedMatching

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.Framework.PredFiniteSufficient

/-! ## Bindings -/

/-- Every named variable has a value. -/
def Covers (bindings : Bindings) (names : List String) : Prop :=
  ∀ name ∈ names, ∃ value, bindings.find? (·.1 == name) = some (name, value)

theorem extends_refl (bindings : Bindings) : BindingsExtends bindings bindings :=
  fun _ _ found => found

theorem extends_trans {first second third : Bindings} (left : BindingsExtends first second)
    (right : BindingsExtends second third) : BindingsExtends first third :=
  fun name value found => right name value (left name value found)

theorem find_named {bindings : Bindings} {name : String} {entry : String × Pattern}
    (found : bindings.find? (·.1 == name) = some entry) : entry = (name, entry.2) := by
  have named : entry.1 = name := by simpa using List.find?_some found
  exact Prod.ext named rfl

/-- Merging adds no value for a name the right operand does not bind. -/
theorem merge_find_none {name : String} :
    ∀ {right left merged : Bindings}, mergeBindings left right = some merged →
      right.find? (·.1 == name) = none →
      merged.find? (·.1 == name) = left.find? (·.1 == name)
  | [], left, merged, ok, _ => by
      simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at ok
      rw [ok]
  | (key, value) :: rest, left, merged, ok, absent => by
      simp only [List.find?_cons] at absent
      cases same : key == name with
      | true => simp [same] at absent
      | false =>
        simp only [same] at absent
        simp only [mergeBindings, List.foldlM_cons, Option.bind_eq_bind] at ok
        cases held : left.find? (·.1 == key) with
        | none =>
          simp only [held, Option.bind_some] at ok
          rw [merge_find_none (left := (key, value) :: left) (right := rest) ok absent]
          simp [same]
        | some entry =>
          obtain ⟨_, existing⟩ := entry
          simp only [held] at ok
          split at ok
          · exact merge_find_none (left := left) (right := rest) ok absent
          · simp at ok

/-- A merge is below whatever is above both operands. -/
theorem extends_merge {left right merged upper : Bindings} (ok : mergeBindings left right = some merged)
    (leftBelow : BindingsExtends left upper) (rightBelow : BindingsExtends right upper) :
    BindingsExtends merged upper := by
  intro name value found
  cases inLeft : left.find? (·.1 == name) with
  | some entry =>
    rw [find_named inLeft] at inLeft
    have kept := mergeBindings_subsumed_left ok inLeft
    rw [found] at kept
    cases kept
    exact leftBelow name _ inLeft
  | none =>
    cases inRight : right.find? (·.1 == name) with
    | none =>
      rw [merge_find_none ok inRight, inLeft] at found
      cases found
    | some entry =>
      rw [find_named inRight] at inRight
      have kept := mergeBindings_subsumed_right ok inRight
      rw [found] at kept
      cases kept
      exact rightBelow name _ inRight

theorem covers_extends {first second : Bindings} {names : List String} (covered : Covers first names)
    (above : BindingsExtends first second) : Covers second names := fun name member =>
  (covered name member).imp fun value found => above name value found

theorem lookup_of_extends {first second : Bindings} {names : List String} (covered : Covers first names)
    (above : BindingsExtends first second) {name : String} (member : name ∈ names) :
    lookupOrFvar first name = lookupOrFvar second name := by
  obtain ⟨value, found⟩ := covered name member
  simp [lookupOrFvar, applyBindings, found, above name value found]

theorem lookup_of_valued {bindings : Bindings} {valuation : String → Pattern} {names : List String}
    (valued : BindingsValued bindings valuation) (covered : Covers bindings names) {name : String}
    (member : name ∈ names) : lookupOrFvar bindings name = valuation name := by
  obtain ⟨value, found⟩ := covered name member
  simpa [lookupOrFvar, applyBindings, found] using valued name value (List.mem_of_find?_eq_some found)

/-! ## The shapes -/

mutual
  /-- Variables, constructors and vectors, a rest allowed. -/
  def ordered : Pattern → Bool
    | .fvar _ => true
    | .bvar _ => true
    | .apply _ arguments => orderedList arguments
    | .collection .vec elements _ => orderedList elements
    | .collection _ _ _ => false
    | .lambda _ _ => false
    | .multiLambda _ _ _ => false
    | .subst _ _ => false

  def orderedList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => ordered pattern && orderedList patterns
end

mutual
  /-- **Data: terms of the canonical carrier.** No collection has an open rest, and no binder carries a display
  name (`Syntax.hasCanonicalBinderMetadata`): binding is by indices, so the carrier is the canonical section of the
  source's quotient by binder names. -/
  def isData : Pattern → Bool
    | .fvar _ => true
    | .bvar _ => true
    | .apply _ arguments => isDataList arguments
    | .collection _ elements rest => rest.isNone && isDataList elements
    | .lambda binder body => binder.isNone && isData body
    | .multiLambda _ binders body => binders.isEmpty && isData body
    | .subst body value => isData body && isData value

  def isDataList : List Pattern → Bool
    | [] => true
    | term :: terms => isData term && isDataList terms
end

mutual
  /-- The rest variables of an ordered pattern. -/
  def restNames : Pattern → List String
    | .apply _ arguments => restNamesList arguments
    | .collection _ elements rest => restNamesList elements ++ rest.toList
    | _ => []

  def restNamesList : List Pattern → List String
    | [] => []
    | pattern :: patterns => restNames pattern ++ restNamesList patterns
end

mutual
  /-- Every variable of a pattern, the rests and the names under binders included. -/
  def names : Pattern → List String
    | .fvar name => [name]
    | .bvar _ => []
    | .apply _ arguments => namesList arguments
    | .collection _ elements rest => namesList elements ++ rest.toList
    | .lambda _ body => names body
    | .multiLambda _ _ body => names body
    | .subst body value => names body ++ names value

  def namesList : List Pattern → List String
    | [] => []
    | pattern :: patterns => names pattern ++ namesList patterns
end

/-- Every named rest is bound to a closed vector. -/
def Settled (bindings : Bindings) (rests : List String) : Prop :=
  ∀ rest ∈ rests, ∃ tail, bindings.find? (·.1 == rest) = some (rest, .collection .vec tail none)

theorem Settled.extends_ {first second : Bindings} {rests : List String} (settled : Settled first rests)
    (above : BindingsExtends first second) : Settled second rests := fun rest member =>
  (settled rest member).imp fun _ found => above rest _ found

theorem isDataList_iff : ∀ {terms : List Pattern}, isDataList terms = true ↔ ∀ term ∈ terms, isData term = true
  | [] => by simp [isDataList]
  | term :: terms => by simp [isDataList, isDataList_iff (terms := terms)]

/-! ## A match is exact -/

mutual
  /-- **A match reconstructs data, under every extension of what it binds.** -/
  theorem match_exact : ∀ (pattern : Pattern) {term : Pattern} {found upper : Bindings},
      ordered pattern = true → isData term = true → MatchRel pattern term found →
      BindingsExtends found upper → applyBindings upper pattern = term
    | .fvar name, term, _, _, _, _, matched, above => by
        cases matched
        simp [applyBindings, above name term (by simp)]
    | .bvar _, _, _, _, _, _, matched, _ => by
        cases matched
        simp [applyBindings]
    | .apply _ arguments, _, _, _, shape, data, matched, above => by
        cases matched with
        | apply argumentsMatched _ =>
          simp only [ordered] at shape
          simp only [isData] at data
          simp [applyBindings, matchList_exact arguments shape data argumentsMatched above]
    | .collection .vec elements none, _, _, _, shape, data, matched, above => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vector elementsMatched =>
          simp only [ordered] at shape
          simp only [isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
          obtain ⟨rfl, data⟩ := data
          simp [applyBindings, matchList_exact elements shape data elementsMatched above]
    | .collection .vec elements (some rest), .collection kind terms _, found, upper, shape, data, matched, above => by
        obtain rfl : kind = CollType.vec := by cases matched <;> rfl
        obtain ⟨leading, trailing, before, rfl, elementsMatched, merged⟩ := matchRel_vectorRest_iff_split.mp matched
        simp only [ordered] at shape
        simp only [isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
        obtain ⟨rfl, data⟩ := data
        have front : isDataList leading = true :=
          isDataList_iff.mpr fun term member => isDataList_iff.mp data term (List.mem_append_left _ member)
        have bound := above rest _
          (mergeBindings_subsumed_right merged (x := rest) (List.find?_cons_of_pos (by simp)))
        simp [applyBindings, bound, matchList_exact elements shape front elementsMatched
          fun name value held => above name value (mergeBindings_subsumed_left merged held)]
    | .collection .vec _ (some _), .fvar _, _, _, _, _, matched, _ => nomatch matched
    | .collection .vec _ (some _), .bvar _, _, _, _, _, matched, _ => nomatch matched
    | .collection .vec _ (some _), .apply _ _, _, _, _, _, matched, _ => nomatch matched
    | .collection .vec _ (some _), .lambda _ _, _, _, _, _, matched, _ => nomatch matched
    | .collection .vec _ (some _), .multiLambda _ _ _, _, _, _, _, matched, _ => nomatch matched
    | .collection .vec _ (some _), .subst _ _, _, _, _, _, matched, _ => nomatch matched
    | .collection .hashBag _ _, _, _, _, shape, _, _, _ => by simp [ordered] at shape
    | .collection .hashSet _ _, _, _, _, shape, _, _, _ => by simp [ordered] at shape
    | .lambda _ _, _, _, _, shape, _, _, _ => by simp [ordered] at shape
    | .multiLambda _ _ _, _, _, _, shape, _, _, _ => by simp [ordered] at shape
    | .subst _ _, _, _, _, shape, _, _, _ => by simp [ordered] at shape

  theorem matchList_exact : ∀ (patterns : List Pattern) {terms : List Pattern} {found upper : Bindings},
      orderedList patterns = true → isDataList terms = true → MatchArgsRel patterns terms found →
      BindingsExtends found upper → patterns.map (applyBindings upper) = terms
    | [], _, _, _, _, _, matched, _ => by
        cases matched
        rfl
    | pattern :: patterns, _, _, _, shape, data, matched, above => by
        cases matched with
        | cons head tail merged =>
          simp only [orderedList, Bool.and_eq_true] at shape
          simp only [isDataList, Bool.and_eq_true] at data
          rw [List.map_cons,
            match_exact pattern shape.1 data.1 head
              fun name value held => above name value (mergeBindings_subsumed_left merged held),
            matchList_exact patterns shape.2 data.2 tail
              fun name value held => above name value (mergeBindings_subsumed_right merged held)]
end

/-! ## A match binds -/

mutual
  /-- **A match binds every variable, and settles every rest as a vector.** -/
  theorem match_binds : ∀ (pattern : Pattern) {term : Pattern} {found : Bindings},
      ordered pattern = true → MatchRel pattern term found →
      Covers found (names pattern) ∧ Settled found (restNames pattern)
    | .fvar name, term, _, _, matched => by
        cases matched
        simp [names, restNames, Covers, Settled]
    | .bvar _, _, _, _, _ => by simp [names, restNames, Covers, Settled]
    | .apply _ arguments, _, _, shape, matched => by
        cases matched with
        | apply argumentsMatched _ =>
          simp only [ordered] at shape
          simpa only [names, restNames] using matchList_binds arguments shape argumentsMatched
    | .collection .vec elements none, _, _, shape, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vector elementsMatched =>
          simp only [ordered] at shape
          simpa [names, restNames] using matchList_binds elements shape elementsMatched
    | .collection .vec elements (some rest), _, found, shape, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vectorRest elementsMatched merged =>
          simp only [ordered] at shape
          obtain ⟨covered, settled⟩ := matchList_binds elements shape elementsMatched
          have below := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
          have bound := mergeBindings_subsumed_right merged (x := rest) (List.find?_cons_of_pos (by simp))
          constructor
          · intro name member
            simp only [names, Option.toList_some, List.mem_append, List.mem_singleton] at member
            rcases member with inElements | rfl
            · exact covers_extends covered below name inElements
            · exact ⟨_, bound⟩
          · intro name member
            simp only [restNames, Option.toList_some, List.mem_append, List.mem_singleton] at member
            rcases member with inElements | rfl
            · exact settled.extends_ below name inElements
            · exact ⟨_, bound⟩
    | .collection .hashBag _ _, _, _, shape, _ => by simp [ordered] at shape
    | .collection .hashSet _ _, _, _, shape, _ => by simp [ordered] at shape
    | .lambda _ _, _, _, shape, _ => by simp [ordered] at shape
    | .multiLambda _ _ _, _, _, shape, _ => by simp [ordered] at shape
    | .subst _ _, _, _, shape, _ => by simp [ordered] at shape

  theorem matchList_binds : ∀ (patterns : List Pattern) {terms : List Pattern} {found : Bindings},
      orderedList patterns = true → MatchArgsRel patterns terms found →
      Covers found (namesList patterns) ∧ Settled found (restNamesList patterns)
    | [], _, _, _, _ => by simp [namesList, restNamesList, Covers, Settled]
    | pattern :: patterns, _, _, shape, matched => by
        cases matched with
        | cons head tail merged =>
          simp only [orderedList, Bool.and_eq_true] at shape
          obtain ⟨firstCovered, firstSettled⟩ := match_binds pattern shape.1 head
          obtain ⟨othersCovered, othersSettled⟩ := matchList_binds patterns shape.2 tail
          have left := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
          have right := fun name value held => mergeBindings_subsumed_right merged (x := name) (v := value) held
          constructor
          · intro name member
            simp only [namesList, List.mem_append] at member
            rcases member with first | later
            · exact covers_extends firstCovered left name first
            · exact covers_extends othersCovered right name later
          · intro name member
            simp only [restNamesList, List.mem_append] at member
            rcases member with first | later
            · exact firstSettled.extends_ left name first
            · exact othersSettled.extends_ right name later
end

/-! ## An instance is matched -/

mutual
  /-- **An instance is matched, by bindings that agree with the witness.** -/
  theorem match_complete (witness : Bindings) : ∀ (pattern : Pattern),
      ordered pattern = true → Settled witness (restNames pattern) →
      ∃ found, MatchRel pattern (applyBindings witness pattern) found ∧
        BindingsValued found (lookupOrFvar witness)
    | .fvar name, _, _ => by
        refine ⟨_, .fvar, fun key value member => ?_⟩
        simp only [List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        rfl
    | .bvar _, _, _ => ⟨[], by simpa [applyBindings] using MatchRel.bvar, fun _ _ member => nomatch member⟩
    | .apply label arguments, shape, settled => by
        simp only [ordered] at shape
        simp only [restNames] at settled
        obtain ⟨found, matched, valued⟩ := matchList_complete witness arguments shape settled
        exact ⟨found, by simpa [applyBindings] using MatchRel.apply (c := label) matched matched.length_eq, valued⟩
    | .collection .vec elements none, shape, settled => by
        simp only [ordered] at shape
        simp only [restNames, Option.toList_none, List.append_nil] at settled
        obtain ⟨found, matched, valued⟩ := matchList_complete witness elements shape settled
        exact ⟨found, by simpa [applyBindings] using MatchRel.vector (rest₂ := none) matched, valued⟩
    | .collection .vec elements (some rest), shape, settled => by
        simp only [ordered] at shape
        obtain ⟨tail, bound⟩ := settled rest (by simp [restNames])
        obtain ⟨front, matched, valued⟩ := matchList_complete witness elements shape
          fun name member => settled name (by simp [restNames, member])
        have tailValued : BindingsValued [(rest, Pattern.collection .vec tail none)] (lookupOrFvar witness) := by
          intro key value member
          simp only [List.mem_singleton, Prod.mk.injEq] at member
          obtain ⟨rfl, rfl⟩ := member
          simp [lookupOrFvar, applyBindings, bound]
        obtain ⟨found, merged, foundValued⟩ := mergeBindings_some_of_valued front _ _ valued tailValued
        refine ⟨found, ?_, foundValued⟩
        simp only [applyBindings, bound, beq_self_eq_true, ↓reduceIte]
        exact matchRel_vectorRest_iff_split.mpr ⟨_, tail, front, rfl, matched, merged⟩
    | .collection .hashBag _ _, shape, _ => by simp [ordered] at shape
    | .collection .hashSet _ _, shape, _ => by simp [ordered] at shape
    | .lambda _ _, shape, _ => by simp [ordered] at shape
    | .multiLambda _ _ _, shape, _ => by simp [ordered] at shape
    | .subst _ _, shape, _ => by simp [ordered] at shape

  theorem matchList_complete (witness : Bindings) : ∀ (patterns : List Pattern),
      orderedList patterns = true → Settled witness (restNamesList patterns) →
      ∃ found, MatchArgsRel patterns (patterns.map (applyBindings witness)) found ∧
        BindingsValued found (lookupOrFvar witness)
    | [], _, _ => ⟨[], .nil, fun _ _ member => nomatch member⟩
    | pattern :: patterns, shape, settled => by
        simp only [orderedList, Bool.and_eq_true] at shape
        obtain ⟨head, headMatched, headValued⟩ := match_complete witness pattern shape.1
          fun name member => settled name (by simp [restNamesList, member])
        obtain ⟨tail, tailMatched, tailValued⟩ := matchList_complete witness patterns shape.2
          fun name member => settled name (by simp [restNamesList, member])
        obtain ⟨found, merged, valued⟩ := mergeBindings_some_of_valued head tail _ headValued tailValued
        exact ⟨found, .cons headMatched tailMatched merged, valued⟩
end

/-! ## Data -/

theorem orderedList_iff : ∀ {patterns : List Pattern},
    orderedList patterns = true ↔ ∀ pattern ∈ patterns, ordered pattern = true
  | [] => by simp [orderedList]
  | pattern :: patterns => by simp [orderedList, orderedList_iff (patterns := patterns)]

/-- Every bound value is data. -/
def DataOn (bindings : Bindings) : Prop :=
  ∀ name value, bindings.find? (·.1 == name) = some (name, value) → isData value = true

theorem DataOn.merge {left right merged : Bindings} (ok : mergeBindings left right = some merged)
    (first : DataOn left) (second : DataOn right) : DataOn merged := by
  intro name value found
  cases inRight : right.find? (·.1 == name) with
  | none => exact first name value (by rw [← merge_find_none ok inRight]; exact found)
  | some entry =>
    rw [find_named inRight] at inRight
    have kept := mergeBindings_subsumed_right ok inRight
    rw [found] at kept
    cases kept
    exact second name _ inRight

theorem dataOn_single {key : String} {value : Pattern} (data : isData value = true) : DataOn [(key, value)] := by
  intro name other found
  have member := List.mem_of_find?_eq_some found
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  rw [member.2]
  exact data

mutual
  /-- **A match of data binds data.** -/
  theorem match_data : ∀ (pattern : Pattern) {term : Pattern} {found : Bindings},
      ordered pattern = true → isData term = true → MatchRel pattern term found → DataOn found
    | .fvar _, _, _, _, data, matched => by
        cases matched
        exact dataOn_single data
    | .bvar _, _, _, _, _, matched => by
        cases matched
        intro _ _ found
        simp at found
    | .apply _ arguments, _, _, shape, data, matched => by
        cases matched with
        | apply argumentsMatched _ =>
          simp only [ordered] at shape
          simp only [isData] at data
          exact matchList_data arguments shape data argumentsMatched
    | .collection .vec elements none, _, _, shape, data, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vector elementsMatched =>
          simp only [ordered] at shape
          simp only [isData, Bool.and_eq_true] at data
          exact matchList_data elements shape data.2 elementsMatched
    | .collection .vec elements (some rest), _, _, shape, data, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vectorRest elementsMatched merged =>
          simp only [ordered] at shape
          simp only [isData, Bool.and_eq_true] at data
          have every := isDataList_iff.mp data.2
          refine DataOn.merge merged (matchList_data elements shape
            (isDataList_iff.mpr fun term member => every term (List.mem_of_mem_take member)) elementsMatched)
            (dataOn_single ?_)
          simp only [isData, Option.isNone_none, Bool.true_and]
          exact isDataList_iff.mpr fun term member => every term (List.mem_of_mem_drop member)
    | .collection .hashBag _ _, _, _, shape, _, _ => by simp [ordered] at shape
    | .collection .hashSet _ _, _, _, shape, _, _ => by simp [ordered] at shape
    | .lambda _ _, _, _, shape, _, _ => by simp [ordered] at shape
    | .multiLambda _ _ _, _, _, shape, _, _ => by simp [ordered] at shape
    | .subst _ _, _, _, shape, _, _ => by simp [ordered] at shape

  theorem matchList_data : ∀ (patterns : List Pattern) {terms : List Pattern} {found : Bindings},
      orderedList patterns = true → isDataList terms = true → MatchArgsRel patterns terms found → DataOn found
    | [], _, _, _, _, matched => by
        cases matched
        intro _ _ found
        simp at found
    | pattern :: patterns, _, _, shape, data, matched => by
        cases matched with
        | cons head tail merged =>
          simp only [orderedList, Bool.and_eq_true] at shape
          simp only [isDataList, Bool.and_eq_true] at data
          exact DataOn.merge merged (match_data pattern shape.1 data.1 head)
            (matchList_data patterns shape.2 data.2 tail)
end

mutual
  /-- **Data under data**: with the rests settled, an instance is data. -/
  theorem instance_data {bindings : Bindings} (values : DataOn bindings) : ∀ (pattern : Pattern),
      ordered pattern = true → Settled bindings (restNames pattern) →
      isData (applyBindings bindings pattern) = true
    | .fvar name, _, _ => by
        cases found : bindings.find? (·.1 == name) with
        | none => simp [applyBindings, found, isData]
        | some entry =>
          rw [find_named found] at found
          simpa [applyBindings, found] using values name _ found
    | .bvar _, _, _ => by simp [applyBindings, isData]
    | .apply _ arguments, shape, settled => by
        simp only [ordered] at shape
        simp only [restNames] at settled
        simpa [applyBindings, isData] using instanceList_data values arguments shape settled
    | .collection .vec elements none, shape, settled => by
        simp only [ordered] at shape
        simp only [restNames, Option.toList_none, List.append_nil] at settled
        simpa [applyBindings, isData] using instanceList_data values elements shape settled
    | .collection .vec elements (some rest), shape, settled => by
        simp only [ordered] at shape
        obtain ⟨tail, bound⟩ := settled rest (by simp [restNames])
        have front := isDataList_iff.mp (instanceList_data values elements shape
          fun name member => settled name (by simp [restNames, member]))
        have back : isDataList tail = true := by simpa [isData] using values rest _ bound
        simp only [applyBindings, bound, beq_self_eq_true, ↓reduceIte, isData, Option.isNone_none, Bool.true_and]
        refine isDataList_iff.mpr fun term member => ?_
        rcases List.mem_append.mp member with inFront | inBack
        · exact front term inFront
        · exact isDataList_iff.mp back term inBack
    | .collection .hashBag _ _, shape, _ => by simp [ordered] at shape
    | .collection .hashSet _ _, shape, _ => by simp [ordered] at shape
    | .lambda _ _, shape, _ => by simp [ordered] at shape
    | .multiLambda _ _ _, shape, _ => by simp [ordered] at shape
    | .subst _ _, shape, _ => by simp [ordered] at shape

  theorem instanceList_data {bindings : Bindings} (values : DataOn bindings) : ∀ (patterns : List Pattern),
      orderedList patterns = true → Settled bindings (restNamesList patterns) →
      isDataList (patterns.map (applyBindings bindings)) = true
    | [], _, _ => by simp [isDataList]
    | pattern :: patterns, shape, settled => by
        simp only [orderedList, Bool.and_eq_true] at shape
        simp only [List.map_cons, isDataList, Bool.and_eq_true]
        exact ⟨instance_data values pattern shape.1 fun name member => settled name (by simp [restNamesList, member]),
          instanceList_data values patterns shape.2 fun name member => settled name (by simp [restNamesList, member])⟩
end

mutual
  /-- **An instance depends on the named variables alone.** -/
  theorem instance_agree {first second : Bindings} : ∀ (pattern : Pattern), ordered pattern = true →
      (∀ name ∈ names pattern, lookupOrFvar first name = lookupOrFvar second name) →
      applyBindings first pattern = applyBindings second pattern
    | .fvar name, _, agree => agree name (by simp [names])
    | .bvar _, _, _ => by simp [applyBindings]
    | .apply _ arguments, shape, agree => by
        simp only [ordered] at shape
        simp only [names] at agree
        simp [applyBindings, instanceList_agree arguments shape agree]
    | .collection .vec elements none, shape, agree => by
        simp only [ordered] at shape
        simp only [names, Option.toList_none, List.append_nil] at agree
        simp [applyBindings, instanceList_agree elements shape agree]
    | .collection .vec elements (some rest), shape, agree => by
        simp only [ordered] at shape
        have front := instanceList_agree (first := first) (second := second) elements shape
          fun name member => agree name (by simp [names, member])
        have last := agree rest (by simp [names])
        simp only [lookupOrFvar, applyBindings] at last
        simp only [applyBindings, front]
        cases inFirst : first.find? (·.1 == rest) with
        | none =>
          cases inSecond : second.find? (·.1 == rest) with
          | none => simp
          | some entry =>
            obtain ⟨_, value⟩ := entry
            simp only [inFirst, inSecond] at last
            subst last
            simp
        | some entry =>
          obtain ⟨_, value⟩ := entry
          cases inSecond : second.find? (·.1 == rest) with
          | none =>
            simp only [inFirst, inSecond] at last
            subst last
            simp
          | some other =>
            obtain ⟨_, valueThere⟩ := other
            simp only [inFirst, inSecond] at last
            subst last
            cases value with
            | collection _ _ openRest => cases openRest <;> simp
            | _ => simp
    | .collection .hashBag _ _, shape, _ => by simp [ordered] at shape
    | .collection .hashSet _ _, shape, _ => by simp [ordered] at shape
    | .lambda _ _, shape, _ => by simp [ordered] at shape
    | .multiLambda _ _ _, shape, _ => by simp [ordered] at shape
    | .subst _ _, shape, _ => by simp [ordered] at shape

  theorem instanceList_agree {first second : Bindings} : ∀ (patterns : List Pattern), orderedList patterns = true →
      (∀ name ∈ namesList patterns, lookupOrFvar first name = lookupOrFvar second name) →
      patterns.map (applyBindings first) = patterns.map (applyBindings second)
    | [], _, _ => rfl
    | pattern :: patterns, shape, agree => by
        simp only [orderedList, Bool.and_eq_true] at shape
        rw [List.map_cons, List.map_cons,
          instance_agree pattern shape.1 fun name member => agree name (by simp [namesList, member]),
          instanceList_agree patterns shape.2 fun name member => agree name (by simp [namesList, member])]
end

mutual
  /-- **An instance that is data settles its rests.** -/
  theorem settled_of_data {bindings : Bindings} : ∀ (pattern : Pattern), ordered pattern = true →
      isData (applyBindings bindings pattern) = true → Settled bindings (restNames pattern)
    | .fvar _, _, _ => by simp [restNames, Settled]
    | .bvar _, _, _ => by simp [restNames, Settled]
    | .apply _ arguments, shape, data => by
        simp only [ordered] at shape
        simp only [applyBindings, isData] at data
        simpa only [restNames] using settledList_of_data arguments shape data
    | .collection .vec elements none, shape, data => by
        simp only [ordered] at shape
        simp [applyBindings, isData] at data
        simpa [restNames] using settledList_of_data elements shape data
    | .collection .vec elements (some rest), shape, data => by
        simp only [ordered] at shape
        cases found : bindings.find? (·.1 == rest) with
        | none => simp [applyBindings, found, isData] at data
        | some entry =>
          obtain ⟨key, value⟩ := entry
          obtain rfl : key = rest := by simpa using List.find?_some found
          cases value with
          | collection kind items openRest =>
            cases openRest with
            | some _ => simp [applyBindings, found, isData] at data
            | none =>
              by_cases same : kind = CollType.vec
              · subst same
                simp [applyBindings, found, isData] at data
                intro name member
                simp only [restNames, Option.toList_some, List.mem_append, List.mem_singleton] at member
                rcases member with before | rfl
                · exact settledList_of_data elements shape (isDataList_iff.mpr fun term inFront =>
                    isDataList_iff.mp data term (List.mem_append_left _ inFront)) name before
                · exact ⟨items, found⟩
              · simp [applyBindings, found, isData, same] at data
          | _ => simp [applyBindings, found, isData] at data
    | .collection .hashBag _ _, shape, _ => by simp [ordered] at shape
    | .collection .hashSet _ _, shape, _ => by simp [ordered] at shape
    | .lambda _ _, shape, _ => by simp [ordered] at shape
    | .multiLambda _ _ _, shape, _ => by simp [ordered] at shape
    | .subst _ _, shape, _ => by simp [ordered] at shape

  theorem settledList_of_data {bindings : Bindings} : ∀ (patterns : List Pattern), orderedList patterns = true →
      isDataList (patterns.map (applyBindings bindings)) = true → Settled bindings (restNamesList patterns)
    | [], _, _ => by simp [restNamesList, Settled]
    | pattern :: patterns, shape, data => by
        simp only [orderedList, Bool.and_eq_true] at shape
        simp only [List.map_cons, isDataList, Bool.and_eq_true] at data
        intro name member
        simp only [restNamesList, List.mem_append] at member
        rcases member with here | later
        · exact settled_of_data pattern shape.1 data.1 name here
        · exact settledList_of_data patterns shape.2 data.2 name later
end

/-! ## Controls -/

namespace Controls

def headTail : Pattern := .collection .vec [.fvar "head"] (some "tail")

def first : Pattern := .apply "A" []

def second : Pattern := .apply "B" []

/-- **Positive**: the head, and the tail as a vector. -/
theorem head_and_tail (found : Bindings)
    (matched : MatchRel headTail (.collection .vec [first, second] none) found) :
    applyBindings found headTail = .collection .vec [first, second] none :=
  match_exact headTail (by simp [headTail, ordered, orderedList])
    (by simp [first, second, isData, isDataList]) matched (extends_refl found)

/-- **Negative**: an open term is matched and not reconstructed. -/
theorem open_term_not_exact :
    ∃ found, MatchRel headTail (.collection .vec [first] (some "more")) found ∧
      applyBindings found headTail ≠ .collection .vec [first] (some "more") := by
  refine ⟨[("tail", .collection .vec [] none), ("head", first)], matchRel_vectorRest_iff_split.mpr
    ⟨[first], [], [("head", first)], rfl, .cons .fvar .nil rfl, ?_⟩, ?_⟩
  · simp [mergeBindings]
  · simp [headTail, applyBindings]

end Controls

#print axioms match_exact
#print axioms match_binds
#print axioms match_complete
#print axioms match_data
#print axioms instance_data
#print axioms instance_agree
#print axioms settled_of_data
#print axioms Controls.head_and_tail
#print axioms Controls.open_term_not_exact

end Mettapedia.GSLT.Compilation.Uniform.OrderedMatching
