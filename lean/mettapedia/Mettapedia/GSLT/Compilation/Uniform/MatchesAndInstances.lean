import Mettapedia.GSLT.Compilation.Uniform.OrderedMatching

/-!
# Facts of the source's matcher

The source matches a pattern against a term structurally (`MatchRel`): a binder's body against a binder's body, its
name ignored; an explicit substitution against an explicit substitution. Vector rests are bound to closed vectors
and bag and set rests to closed collections of their kind (`Settled`, `BagSettled`). At the source:

* a match binds every name and settles every rest (`match_binds`);
* a match binds each name once (`match_functional`);
* a match of data binds data (`match_data`).

The plain instance of a pattern (`applyBindings`) evaluates an explicit substitution, so its facts are for patterns
without one (`noExplicitSubst`):

* an instance depends only on the values of the names (`instance_agree`);
* an instance under data whose rests are settled is data (`instance_data`);
* an instance is matched, by bindings the instantiation values (`match_complete`): each element of a bag or a set
  is picked first, from where the instance put it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.MatchesAndInstances

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open OrderedMatching (names namesList Covers covers_extends Settled isData isDataList isDataList_iff DataOn
  dataOn_single extends_trans find_named)
open Mettapedia.OSLF.MeTTaIL.Substitution (noExplicitSubst allNoExplicitSubst)

mutual
  /-- The rest names of a pattern's vectors. -/
  def vectorRests : Pattern → List String
    | .apply _ arguments => vectorRestsList arguments
    | .collection .vec elements rest => vectorRestsList elements ++ rest.toList
    | .collection _ elements _ => vectorRestsList elements
    | .lambda _ body => vectorRests body
    | .multiLambda _ _ body => vectorRests body
    | .subst body value => vectorRests body ++ vectorRests value
    | _ => []

  def vectorRestsList : List Pattern → List String
    | [] => []
    | pattern :: patterns => vectorRests pattern ++ vectorRestsList patterns
end

mutual
  /-- The rest names of a pattern's bags and sets, with their kinds. -/
  def bagRests : Pattern → List (String × CollType)
    | .apply _ arguments => bagRestsList arguments
    | .collection .vec elements _ => bagRestsList elements
    | .collection kind elements rest => bagRestsList elements ++ (rest.map (·, kind)).toList
    | .lambda _ body => bagRests body
    | .multiLambda _ _ body => bagRests body
    | .subst body value => bagRests body ++ bagRests value
    | _ => []

  def bagRestsList : List Pattern → List (String × CollType)
    | [] => []
    | pattern :: patterns => bagRests pattern ++ bagRestsList patterns
end

mutual
  theorem vectorRests_names : ∀ (pattern : Pattern) {name : String}, name ∈ vectorRests pattern → name ∈ names pattern
    | .apply _ arguments, _, inside => by
        simp only [vectorRests, names] at inside ⊢
        exact vectorRestsList_names arguments inside
    | .collection .vec elements rest, _, inside => by
        simp only [vectorRests, names, List.mem_append] at inside ⊢
        rcases inside with inElements | inRest
        · exact .inl (vectorRestsList_names elements inElements)
        · exact .inr inRest
    | .collection .hashBag elements rest, _, inside => by
        simp only [vectorRests, names, List.mem_append] at inside ⊢
        exact .inl (vectorRestsList_names elements inside)
    | .collection .hashSet elements rest, _, inside => by
        simp only [vectorRests, names, List.mem_append] at inside ⊢
        exact .inl (vectorRestsList_names elements inside)
    | .fvar _, _, inside => by simp [vectorRests] at inside
    | .bvar _, _, inside => by simp [vectorRests] at inside
    | .lambda _ body, _, inside => by
        simp only [vectorRests, names] at inside ⊢
        exact vectorRests_names body inside
    | .multiLambda _ _ body, _, inside => by
        simp only [vectorRests, names] at inside ⊢
        exact vectorRests_names body inside
    | .subst body value, _, inside => by
        simp only [vectorRests, names, List.mem_append] at inside ⊢
        rcases inside with inBody | inValue
        · exact .inl (vectorRests_names body inBody)
        · exact .inr (vectorRests_names value inValue)

  theorem vectorRestsList_names : ∀ (patterns : List Pattern) {name : String},
      name ∈ vectorRestsList patterns → name ∈ namesList patterns
    | [], _, inside => by simp [vectorRestsList] at inside
    | pattern :: patterns, _, inside => by
        simp only [vectorRestsList, namesList, List.mem_append] at inside ⊢
        rcases inside with here | later
        · exact .inl (vectorRests_names pattern here)
        · exact .inr (vectorRestsList_names patterns later)
end

mutual
  theorem bagRests_names : ∀ (pattern : Pattern) {pair : String × CollType}, pair ∈ bagRests pattern →
      pair.1 ∈ names pattern
    | .apply _ arguments, _, inside => by
        simp only [bagRests, names] at inside ⊢
        exact bagRestsList_names arguments inside
    | .collection .vec elements rest, _, inside => by
        simp only [bagRests, names, List.mem_append] at inside ⊢
        exact .inl (bagRestsList_names elements inside)
    | .collection .hashBag elements rest, _, inside => by
        simp only [bagRests, names, List.mem_append] at inside ⊢
        rcases inside with inElements | inRest
        · exact .inl (bagRestsList_names elements inElements)
        · cases rest <;> simp_all
    | .collection .hashSet elements rest, _, inside => by
        simp only [bagRests, names, List.mem_append] at inside ⊢
        rcases inside with inElements | inRest
        · exact .inl (bagRestsList_names elements inElements)
        · cases rest <;> simp_all
    | .fvar _, _, inside => by simp [bagRests] at inside
    | .bvar _, _, inside => by simp [bagRests] at inside
    | .lambda _ body, _, inside => by
        simp only [bagRests, names] at inside ⊢
        exact bagRests_names body inside
    | .multiLambda _ _ body, _, inside => by
        simp only [bagRests, names] at inside ⊢
        exact bagRests_names body inside
    | .subst body value, _, inside => by
        simp only [bagRests, names, List.mem_append] at inside ⊢
        rcases inside with inBody | inValue
        · exact .inl (bagRests_names body inBody)
        · exact .inr (bagRests_names value inValue)

  theorem bagRestsList_names : ∀ (patterns : List Pattern) {pair : String × CollType},
      pair ∈ bagRestsList patterns → pair.1 ∈ namesList patterns
    | [], _, inside => by simp [bagRestsList] at inside
    | pattern :: patterns, _, inside => by
        simp only [bagRestsList, namesList, List.mem_append] at inside ⊢
        rcases inside with here | later
        · exact .inl (bagRests_names pattern here)
        · exact .inr (bagRestsList_names patterns later)
end

/-- **Every bag or set rest is bound to a closed collection of its kind.** -/
def BagSettled (bindings : Bindings) (pairs : List (String × CollType)) : Prop :=
  ∀ pair ∈ pairs, ∃ tail, bindings.find? (·.1 == pair.1) = some (pair.1, .collection pair.2 tail none)

theorem BagSettled.extends_ {first second : Bindings} {pairs : List (String × CollType)}
    (settled : BagSettled first pairs) (above : BindingsExtends first second) : BagSettled second pairs :=
  fun pair member => (settled pair member).imp fun _ found => above _ _ found

/-! ## Patterns without binders have no explicit substitution -/

mutual
  theorem noExplicitSubst_of_binderFree : ∀ {pattern : Pattern}, binderFree pattern = true →
      noExplicitSubst pattern = true
    | .fvar _, _ => rfl
    | .bvar _, _ => rfl
    | .apply _ arguments, free => by
        simp only [binderFree] at free
        simpa [noExplicitSubst] using allNoExplicitSubst_of_binderFreeList (patterns := arguments) free
    | .collection _ elements _, free => by
        simp only [binderFree] at free
        simpa [noExplicitSubst] using allNoExplicitSubst_of_binderFreeList (patterns := elements) free
    | .lambda _ _, free => by simp [binderFree] at free
    | .multiLambda _ _ _, free => by simp [binderFree] at free
    | .subst _ _, free => by simp [binderFree] at free

  theorem allNoExplicitSubst_of_binderFreeList : ∀ {patterns : List Pattern}, binderFreeList patterns = true →
      allNoExplicitSubst patterns = true
    | [], _ => rfl
    | pattern :: patterns, free => by
        simp only [binderFreeList, Bool.and_eq_true] at free
        simp [allNoExplicitSubst, noExplicitSubst_of_binderFree free.1, allNoExplicitSubst_of_binderFreeList free.2]
end

/-! ## Patterns without binders carry no binder names -/

mutual
  theorem canonical_of_binderFree : ∀ {pattern : Pattern}, binderFree pattern = true →
      pattern.hasCanonicalBinderMetadata = true
    | .fvar _, _ => rfl
    | .bvar _, _ => rfl
    | .apply _ arguments, free => by
        simp only [binderFree] at free
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalList_of_binderFreeList (patterns := arguments) free
    | .collection _ elements _, free => by
        simp only [binderFree] at free
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalList_of_binderFreeList (patterns := elements) free
    | .lambda _ _, free => by simp [binderFree] at free
    | .multiLambda _ _ _, free => by simp [binderFree] at free
    | .subst _ _, free => by simp [binderFree] at free

  theorem canonicalList_of_binderFreeList : ∀ {patterns : List Pattern}, binderFreeList patterns = true →
      Pattern.hasCanonicalBinderMetadataList patterns = true
    | [], _ => rfl
    | pattern :: patterns, free => by
        simp only [binderFreeList, Bool.and_eq_true] at free
        simp [Pattern.hasCanonicalBinderMetadataList, canonical_of_binderFree free.1,
          canonicalList_of_binderFreeList free.2]
end

/-! ## A match binds -/

theorem single_bound {name : String} {value : Pattern} :
    ([(name, value)] : Bindings).find? (·.1 == name) = some (name, value) := by simp

mutual
  /-- **A match binds every name and settles every rest.** -/
  theorem match_binds : ∀ (pattern : Pattern) {term : Pattern} {found : Bindings},
      MatchRel pattern term found →
      Covers found (names pattern) ∧ Settled found (vectorRests pattern) ∧ BagSettled found (bagRests pattern)
    | .fvar name, term, _, matched => by
        cases matched
        refine ⟨fun other member => ?_, by simp [vectorRests, Settled], by simp [bagRests, BagSettled]⟩
        simp only [names, List.mem_singleton] at member
        subst member
        exact ⟨term, single_bound⟩
    | .bvar _, _, _, _ => ⟨by simp [names, Covers], by simp [vectorRests, Settled], by simp [bagRests, BagSettled]⟩
    | .apply _ arguments, _, _, matched => by
        cases matched with
        | apply argumentsMatched _ =>
          simpa only [names, vectorRests, bagRests] using matchList_binds arguments argumentsMatched
    | .collection .vec elements none, _, _, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vector elementsMatched =>
          simpa [names, vectorRests, bagRests] using matchList_binds elements elementsMatched
    | .collection .vec elements (some rest), _, found, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vectorRest elementsMatched merged =>
          obtain ⟨covered, settled, bagSettled⟩ := matchList_binds elements elementsMatched
          have below := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
          have bound := mergeBindings_subsumed_right merged (x := rest) single_bound
          refine ⟨fun name member => ?_, fun name member => ?_, ?_⟩
          · simp only [names, Option.toList_some, List.mem_append, List.mem_singleton] at member
            rcases member with inElements | rfl
            · exact covers_extends covered below name inElements
            · exact ⟨_, bound⟩
          · simp only [vectorRests, Option.toList_some, List.mem_append, List.mem_singleton] at member
            rcases member with inElements | rfl
            · exact settled.extends_ below name inElements
            · exact ⟨_, bound⟩
          · simpa only [bagRests] using bagSettled.extends_ below
    | .collection .hashBag elements rest, _, _, matched => by
        cases matched with
        | collection _ bagMatched =>
          simpa only [names, vectorRests, bagRests] using bag_binds elements bagMatched
    | .collection .hashSet elements rest, _, _, matched => by
        cases matched with
        | collection _ bagMatched =>
          simpa only [names, vectorRests, bagRests] using bag_binds elements bagMatched
    | .lambda _ body, _, _, matched => by
        cases matched with
        | lambda bodyMatched => simpa only [names, vectorRests, bagRests] using match_binds body bodyMatched
    | .multiLambda _ _ body, _, _, matched => by
        cases matched with
        | multiLambda bodyMatched => simpa only [names, vectorRests, bagRests] using match_binds body bodyMatched
    | .subst body value, _, _, matched => by
        cases matched with
        | subst bodyMatched valueMatched merged =>
          obtain ⟨bodyCovered, bodySettled, bodyBags⟩ := match_binds body bodyMatched
          obtain ⟨valueCovered, valueSettled, valueBags⟩ := match_binds value valueMatched
          have left := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
          have right := fun name value held => mergeBindings_subsumed_right merged (x := name) (v := value) held
          refine ⟨fun name member => ?_, fun name member => ?_, fun pair member => ?_⟩
          · simp only [names, List.mem_append] at member
            rcases member with first | later
            · exact covers_extends bodyCovered left name first
            · exact covers_extends valueCovered right name later
          · simp only [vectorRests, List.mem_append] at member
            rcases member with first | later
            · exact bodySettled.extends_ left name first
            · exact valueSettled.extends_ right name later
          · simp only [bagRests, List.mem_append] at member
            rcases member with first | later
            · exact bodyBags.extends_ left pair first
            · exact valueBags.extends_ right pair later

  theorem matchList_binds : ∀ (patterns : List Pattern) {terms : List Pattern} {found : Bindings},
      MatchArgsRel patterns terms found →
      Covers found (namesList patterns) ∧ Settled found (vectorRestsList patterns) ∧
        BagSettled found (bagRestsList patterns)
    | [], _, _, _ => ⟨by simp [namesList, Covers], by simp [vectorRestsList, Settled],
        by simp [bagRestsList, BagSettled]⟩
    | pattern :: patterns, _, _, matched => by
        cases matched with
        | cons head tail merged =>
          obtain ⟨firstCovered, firstSettled, firstBags⟩ := match_binds pattern head
          obtain ⟨othersCovered, othersSettled, othersBags⟩ := matchList_binds patterns tail
          have left := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
          have right := fun name value held => mergeBindings_subsumed_right merged (x := name) (v := value) held
          refine ⟨fun name member => ?_, fun name member => ?_, fun pair member => ?_⟩
          · simp only [namesList, List.mem_append] at member
            rcases member with first | later
            · exact covers_extends firstCovered left name first
            · exact covers_extends othersCovered right name later
          · simp only [vectorRestsList, List.mem_append] at member
            rcases member with first | later
            · exact firstSettled.extends_ left name first
            · exact othersSettled.extends_ right name later
          · simp only [bagRestsList, List.mem_append] at member
            rcases member with first | later
            · exact firstBags.extends_ left pair first
            · exact othersBags.extends_ right pair later

  theorem bag_binds : ∀ (patterns : List Pattern) {rest : Option String} {kind : CollType} {terms : List Pattern}
      {found : Bindings}, MatchBagRel patterns rest kind terms found →
      Covers found (namesList patterns ++ rest.toList) ∧ Settled found (vectorRestsList patterns) ∧
        BagSettled found (bagRestsList patterns ++ (rest.map (·, kind)).toList)
    | [], none, _, _, _, matched => by
        cases matched
        exact ⟨by simp [namesList, Covers], by simp [vectorRestsList, Settled], by simp [bagRestsList, BagSettled]⟩
    | [], some rest, kind, terms, _, matched => by
        cases matched
        refine ⟨fun name member => ?_, by simp [vectorRestsList, Settled], fun pair member => ?_⟩
        · simp only [namesList, Option.toList_some, List.nil_append, List.mem_singleton] at member
          subst member
          exact ⟨_, single_bound⟩
        · simp only [bagRestsList, Option.map_some, Option.toList_some, List.nil_append, List.mem_singleton] at member
          subst member
          exact ⟨terms, single_bound⟩
    | pattern :: patterns, rest, kind, terms, _, matched => by
        cases matched with
        | cons index bound head tail merged =>
          obtain ⟨firstCovered, firstSettled, firstBags⟩ := match_binds pattern head
          obtain ⟨othersCovered, othersSettled, othersBags⟩ := bag_binds patterns tail
          have left := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
          have right := fun name value held => mergeBindings_subsumed_right merged (x := name) (v := value) held
          refine ⟨fun name member => ?_, fun name member => ?_, fun pair member => ?_⟩
          · simp only [namesList, List.append_assoc, List.mem_append] at member
            rcases member with first | later
            · exact covers_extends firstCovered left name first
            · exact covers_extends othersCovered right name (List.mem_append.mpr later)
          · simp only [vectorRestsList, List.mem_append] at member
            rcases member with first | later
            · exact firstSettled.extends_ left name first
            · exact othersSettled.extends_ right name later
          · simp only [bagRestsList, List.append_assoc, List.mem_append] at member
            rcases member with first | later
            · exact firstBags.extends_ left pair first
            · exact othersBags.extends_ right pair (List.mem_append.mpr later)
end

/-! ## A match binds each name once -/

theorem foldlM_merge_mem (b2 : Bindings) : ∀ (acc bs : Bindings),
    List.foldlM (fun acc' pair =>
      match acc'.find? (·.1 == pair.1) with
      | none => some (pair :: acc')
      | some (_, existing) => if existing == pair.2 then some acc' else none) acc b2 = some bs →
    ∀ {x : String} {v : Pattern}, (x, v) ∈ bs → (x, v) ∈ acc ∨ (x, v) ∈ b2 := by
  induction b2 with
  | nil =>
    intro acc bs hfold x v inside
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
    subst hfold
    exact .inl inside
  | cons pair tl ih =>
    intro acc bs hfold x v inside
    obtain ⟨name, val⟩ := pair
    simp only [List.foldlM_cons] at hfold
    dsimp only [Bind.bind, Option.bind] at hfold
    cases hn : acc.find? (fun p => p.1 == (name, val).1) with
    | none =>
      simp only [hn] at hfold
      rcases ih _ _ hfold inside with inAcc | inTail
      · rcases List.mem_cons.mp inAcc with same | inOld
        · rw [same]
          exact .inr List.mem_cons_self
        · exact .inl inOld
      · exact .inr (List.mem_cons_of_mem _ inTail)
    | some p =>
      obtain ⟨s, e⟩ := p
      simp only [hn] at hfold
      cases heq : (e == (name, val).2)
      · simp only [heq] at hfold
        simp at hfold
      · simp only [heq] at hfold
        rcases ih _ _ hfold inside with inAcc | inTail
        · exact .inl inAcc
        · exact .inr (List.mem_cons_of_mem _ inTail)

/-- **A merge holds only the entries of its two sides.** -/
theorem mem_of_mergeBindings {left right merged : Bindings} (ok : mergeBindings left right = some merged)
    {x : String} {v : Pattern} (inside : (x, v) ∈ merged) : (x, v) ∈ left ∨ (x, v) ∈ right :=
  foldlM_merge_mem right left merged ok inside

/-- **Bindings that find each of their entries**: every name is bound once. -/
def Functional (bindings : Bindings) : Prop :=
  ∀ x v, (x, v) ∈ bindings → bindings.find? (·.1 == x) = some (x, v)

theorem Functional.merge {left right merged : Bindings} (ok : mergeBindings left right = some merged)
    (first : Functional left) (second : Functional right) : Functional merged := fun x v inside =>
  (mem_of_mergeBindings ok inside).elim (fun inLeft => mergeBindings_subsumed_left ok (first x v inLeft))
    fun inRight => mergeBindings_subsumed_right ok (second x v inRight)

theorem functional_single (name : String) (value : Pattern) : Functional [(name, value)] := by
  intro x v inside
  simp only [List.mem_singleton, Prod.mk.injEq] at inside
  obtain ⟨rfl, rfl⟩ := inside
  simp

theorem functional_nil : Functional [] := fun _ _ inside => absurd inside List.not_mem_nil

mutual
  /-- **A match binds each name once, and only names of the pattern.** -/
  theorem match_functional : ∀ (pattern : Pattern) {term : Pattern} {found : Bindings},
      MatchRel pattern term found →
      Functional found ∧ ∀ x v, (x, v) ∈ found → x ∈ names pattern
    | .fvar name, _, _, matched => by
        cases matched
        refine ⟨functional_single _ _, fun x v inside => ?_⟩
        simp only [List.mem_singleton, Prod.mk.injEq] at inside
        simp [names, inside.1]
    | .bvar _, _, _, matched => by
        cases matched
        exact ⟨functional_nil, fun _ _ inside => absurd inside List.not_mem_nil⟩
    | .apply _ arguments, _, _, matched => by
        cases matched with
        | apply argumentsMatched _ =>
          simpa only [names] using matchList_functional arguments argumentsMatched
    | .collection .vec elements none, _, _, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vector elementsMatched =>
          obtain ⟨functional, keys⟩ := matchList_functional elements elementsMatched
          exact ⟨functional, fun x v inside => by simpa [names] using keys x v inside⟩
    | .collection .vec elements (some rest), _, _, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vectorRest elementsMatched merged =>
          obtain ⟨functional, keys⟩ := matchList_functional elements elementsMatched
          refine ⟨functional.merge merged (functional_single _ _), fun x v inside => ?_⟩
          rcases mem_of_mergeBindings merged inside with inElements | inRest
          · simp [names, keys x v inElements]
          · simp only [List.mem_singleton, Prod.mk.injEq] at inRest
            simp [names, inRest.1]
    | .collection .hashBag elements rest, _, _, matched => by
        cases matched with
        | collection _ bagMatched =>
          obtain ⟨functional, keys⟩ := bag_functional elements bagMatched
          exact ⟨functional, fun x v inside => by simpa [names] using keys x v inside⟩
    | .collection .hashSet elements rest, _, _, matched => by
        cases matched with
        | collection _ bagMatched =>
          obtain ⟨functional, keys⟩ := bag_functional elements bagMatched
          exact ⟨functional, fun x v inside => by simpa [names] using keys x v inside⟩
    | .lambda _ body, _, _, matched => by
        cases matched with
        | lambda bodyMatched => simpa only [names] using match_functional body bodyMatched
    | .multiLambda _ _ body, _, _, matched => by
        cases matched with
        | multiLambda bodyMatched => simpa only [names] using match_functional body bodyMatched
    | .subst body value, _, _, matched => by
        cases matched with
        | subst bodyMatched valueMatched merged =>
          obtain ⟨bodyFunctional, bodyKeys⟩ := match_functional body bodyMatched
          obtain ⟨valueFunctional, valueKeys⟩ := match_functional value valueMatched
          refine ⟨bodyFunctional.merge merged valueFunctional, fun x v inside => ?_⟩
          rcases mem_of_mergeBindings merged inside with inBody | inValue
          · simp [names, bodyKeys x v inBody]
          · simp [names, valueKeys x v inValue]

  theorem matchList_functional : ∀ (patterns : List Pattern) {terms : List Pattern} {found : Bindings},
      MatchArgsRel patterns terms found →
      Functional found ∧ ∀ x v, (x, v) ∈ found → x ∈ namesList patterns
    | [], _, _, matched => by
        cases matched
        exact ⟨functional_nil, fun _ _ inside => absurd inside List.not_mem_nil⟩
    | pattern :: patterns, _, _, matched => by
        cases matched with
        | cons head tail merged =>
          obtain ⟨headFunctional, headKeys⟩ := match_functional pattern head
          obtain ⟨tailFunctional, tailKeys⟩ := matchList_functional patterns tail
          refine ⟨headFunctional.merge merged tailFunctional, fun x v inside => ?_⟩
          rcases mem_of_mergeBindings merged inside with inHead | inTail
          · simp [namesList, headKeys x v inHead]
          · simp [namesList, tailKeys x v inTail]

  theorem bag_functional : ∀ (patterns : List Pattern) {rest : Option String} {kind : CollType}
      {terms : List Pattern} {found : Bindings},
      MatchBagRel patterns rest kind terms found →
      Functional found ∧ ∀ x v, (x, v) ∈ found → x ∈ namesList patterns ++ rest.toList
    | [], none, _, _, _, matched => by
        cases matched
        exact ⟨functional_nil, fun _ _ inside => absurd inside List.not_mem_nil⟩
    | [], some rest, _, _, _, matched => by
        cases matched
        refine ⟨functional_single _ _, fun x v inside => ?_⟩
        simp only [List.mem_singleton, Prod.mk.injEq] at inside
        simp [inside.1]
    | pattern :: patterns, _, _, _, _, matched => by
        cases matched with
        | cons index bound head tail merged =>
          obtain ⟨headFunctional, headKeys⟩ := match_functional pattern head
          obtain ⟨tailFunctional, tailKeys⟩ := bag_functional patterns tail
          refine ⟨headFunctional.merge merged tailFunctional, fun x v inside => ?_⟩
          rcases mem_of_mergeBindings merged inside with inHead | inTail
          · simp [namesList, headKeys x v inHead]
          · have later := tailKeys x v inTail
            simp only [List.mem_append] at later
            simp only [namesList, List.mem_append]
            tauto
end

/-- **Bindings that bind each name once, only names of the pattern, are valued by any bindings that agree on the
pattern's names.** -/
theorem valued_of_agree {found final : Bindings} {pattern : Pattern} (functional : Functional found)
    (keys : ∀ x v, (x, v) ∈ found → x ∈ names pattern)
    (agree : ∀ name ∈ names pattern, lookupOrFvar found name = lookupOrFvar final name) :
    BindingsValued found (lookupOrFvar final) := by
  intro x v inside
  rw [← agree x (keys x v inside)]
  simp [lookupOrFvar, applyBindings, functional x v inside]

/-! ## A match of data binds data -/

mutual
  theorem match_data : ∀ (pattern : Pattern) {term : Pattern} {found : Bindings},
      isData term = true → MatchRel pattern term found → DataOn found
    | .fvar _, _, _, data, matched => by
        cases matched
        exact dataOn_single data
    | .bvar _, _, _, _, matched => by
        cases matched
        intro _ _ found
        simp at found
    | .apply _ arguments, _, _, data, matched => by
        cases matched with
        | apply argumentsMatched _ =>
          simp only [OrderedMatching.isData] at data
          exact matchList_data arguments data argumentsMatched
    | .collection .vec elements none, _, _, data, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vector elementsMatched =>
          simp only [OrderedMatching.isData, Bool.and_eq_true] at data
          exact matchList_data elements data.2 elementsMatched
    | .collection .vec elements (some rest), _, _, data, matched => by
        cases matched with
        | collection notVector _ => exact absurd rfl notVector
        | vectorRest elementsMatched merged =>
          simp only [OrderedMatching.isData, Bool.and_eq_true] at data
          have every := isDataList_iff.mp data.2
          refine OrderedMatching.DataOn.merge merged (matchList_data elements
            (isDataList_iff.mpr fun term member => every term (List.mem_of_mem_take member)) elementsMatched)
            (dataOn_single ?_)
          simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and]
          exact isDataList_iff.mpr fun term member => every term (List.mem_of_mem_drop member)
    | .collection .hashBag elements rest, _, _, data, matched => by
        cases matched with
        | collection _ bagMatched =>
          simp only [OrderedMatching.isData, Bool.and_eq_true] at data
          exact bag_data elements data.2 bagMatched
    | .collection .hashSet elements rest, _, _, data, matched => by
        cases matched with
        | collection _ bagMatched =>
          simp only [OrderedMatching.isData, Bool.and_eq_true] at data
          exact bag_data elements data.2 bagMatched
    | .lambda _ body, _, _, data, matched => by
        cases matched with
        | lambda bodyMatched =>
          simp only [OrderedMatching.isData, Bool.and_eq_true] at data
          exact match_data body data.2 bodyMatched
    | .multiLambda _ _ body, _, _, data, matched => by
        cases matched with
        | multiLambda bodyMatched =>
          simp only [OrderedMatching.isData, Bool.and_eq_true] at data
          exact match_data body data.2 bodyMatched
    | .subst body value, _, _, data, matched => by
        cases matched with
        | subst bodyMatched valueMatched merged =>
          simp only [OrderedMatching.isData, Bool.and_eq_true] at data
          exact OrderedMatching.DataOn.merge merged (match_data body data.1 bodyMatched)
            (match_data value data.2 valueMatched)

  theorem matchList_data : ∀ (patterns : List Pattern) {terms : List Pattern} {found : Bindings},
      isDataList terms = true → MatchArgsRel patterns terms found → DataOn found
    | [], _, _, _, matched => by
        cases matched
        intro _ _ found
        simp at found
    | pattern :: patterns, _, _, data, matched => by
        cases matched with
        | cons head tail merged =>
          simp only [OrderedMatching.isDataList, Bool.and_eq_true] at data
          exact OrderedMatching.DataOn.merge merged (match_data pattern data.1 head)
            (matchList_data patterns data.2 tail)

  theorem bag_data : ∀ (patterns : List Pattern) {rest : Option String} {kind : CollType} {terms : List Pattern}
      {found : Bindings}, isDataList terms = true →
      MatchBagRel patterns rest kind terms found → DataOn found
    | [], none, _, _, _, _, matched => by
        cases matched
        intro _ _ found
        simp at found
    | [], some _, _, _, _, data, matched => by
        cases matched
        exact dataOn_single (by simpa [OrderedMatching.isData] using data)
    | pattern :: patterns, _, _, terms, _, data, matched => by
        cases matched with
        | cons index bound head tail merged =>
          have every := isDataList_iff.mp data
          exact OrderedMatching.DataOn.merge merged
            (match_data pattern (every _ (List.getElem_mem bound)) head)
            (bag_data patterns (isDataList_iff.mpr fun term member =>
              every term (List.mem_of_mem_eraseIdx member)) tail)
end

/-! ## An instance depends on the names -/

mutual
  /-- **An instance depends on the names alone.** -/
  theorem instance_agree {first second : Bindings} : ∀ (pattern : Pattern), noExplicitSubst pattern = true →
      (∀ name ∈ names pattern, lookupOrFvar first name = lookupOrFvar second name) →
      applyBindings first pattern = applyBindings second pattern
    | .fvar name, _, agree => agree name (by simp [names])
    | .bvar _, _, _ => by simp [applyBindings]
    | .apply _ arguments, shape, agree => by
        simp only [noExplicitSubst] at shape
        simp only [names] at agree
        simp [applyBindings, instanceList_agree arguments shape agree]
    | .collection kind elements none, shape, agree => by
        simp only [noExplicitSubst] at shape
        simp only [names, Option.toList_none, List.append_nil] at agree
        simp [applyBindings, instanceList_agree elements shape agree]
    | .collection kind elements (some rest), shape, agree => by
        simp only [noExplicitSubst] at shape
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
    | .lambda _ body, shape, agree => by
        simp only [noExplicitSubst] at shape
        simp only [names] at agree
        simp [applyBindings, instance_agree body shape agree]
    | .multiLambda _ _ body, shape, agree => by
        simp only [noExplicitSubst] at shape
        simp only [names] at agree
        simp [applyBindings, instance_agree body shape agree]
    | .subst _ _, shape, _ => by simp [noExplicitSubst] at shape

  theorem instanceList_agree {first second : Bindings} : ∀ (patterns : List Pattern), allNoExplicitSubst patterns = true →
      (∀ name ∈ namesList patterns, lookupOrFvar first name = lookupOrFvar second name) →
      patterns.map (applyBindings first) = patterns.map (applyBindings second)
    | [], _, _ => rfl
    | pattern :: patterns, shape, agree => by
        simp only [allNoExplicitSubst, Bool.and_eq_true] at shape
        rw [List.map_cons, List.map_cons,
          instance_agree pattern shape.1 fun name member => agree name (by simp [namesList, member]),
          instanceList_agree patterns shape.2 fun name member => agree name (by simp [namesList, member])]
end

/-- A rest settled for its kind is spliced into the instance of its collection. -/
theorem applyBindings_collection_rest {bindings : Bindings} {kind : CollType} {elements : List Pattern}
    {rest : String} {tail : List Pattern} (bound : bindings.find? (·.1 == rest) = some (rest, .collection kind tail none)) :
    applyBindings bindings (.collection kind elements (some rest)) =
      .collection kind (elements.map (applyBindings bindings) ++ tail) none := by
  simp [applyBindings, bound]

mutual
  /-- **An instance under data whose rests are settled is data**, when the pattern's own binders carry no names. -/
  theorem instance_data {bindings : Bindings} (values : DataOn bindings) : ∀ (pattern : Pattern),
      noExplicitSubst pattern = true → pattern.hasCanonicalBinderMetadata = true →
      Settled bindings (vectorRests pattern) → BagSettled bindings (bagRests pattern) →
      isData (applyBindings bindings pattern) = true
    | .fvar name, _, _, _, _ => by
        cases found : bindings.find? (·.1 == name) with
        | none => simp [applyBindings, found, OrderedMatching.isData]
        | some entry =>
          rw [find_named found] at found
          simpa [applyBindings, found] using values name _ found
    | .bvar _, _, _, _, _ => by simp [applyBindings, OrderedMatching.isData]
    | .apply _ arguments, shape, canonical, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simp only [vectorRests] at settled
        simp only [bagRests] at bags
        simpa [applyBindings, OrderedMatching.isData] using
          instanceList_data values arguments shape canonical settled bags
    | .collection kind elements none, shape, canonical, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        have front := instanceList_data values elements shape canonical
          (fun name member => settled name (by cases kind <;> simp [vectorRests, member]))
          (fun pair member => bags pair (by cases kind <;> simp [bagRests, member]))
        simpa [applyBindings, OrderedMatching.isData] using front
    | .collection kind elements (some rest), shape, canonical, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        have front := isDataList_iff.mp (instanceList_data values elements shape canonical
          (fun name member => settled name (by cases kind <;> simp [vectorRests, member]))
          (fun pair member => bags pair (by cases kind <;> simp [bagRests, member])))
        obtain ⟨tail, bound⟩ : ∃ tail, bindings.find? (·.1 == rest) = some (rest, .collection kind tail none) := by
          cases kind with
          | vec => exact settled rest (by simp [vectorRests])
          | hashBag => exact bags (rest, .hashBag) (by simp [bagRests])
          | hashSet => exact bags (rest, .hashSet) (by simp [bagRests])
        have back : isDataList tail = true := by simpa [OrderedMatching.isData] using values rest _ bound
        rw [applyBindings_collection_rest bound]
        simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and]
        refine isDataList_iff.mpr fun term member => ?_
        rcases List.mem_append.mp member with inFront | inBack
        · obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp inFront
          exact front _ (List.mem_map_of_mem inElements)
        · exact isDataList_iff.mp back term inBack
    | .lambda _ body, shape, canonical, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, Option.isNone_iff_eq_none] at canonical
        obtain ⟨rfl, canonical⟩ := canonical
        simp only [vectorRests] at settled
        simp only [bagRests] at bags
        simpa [applyBindings, OrderedMatching.isData] using instance_data values body shape canonical settled bags
    | .multiLambda _ _ body, shape, canonical, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, List.isEmpty_iff] at canonical
        obtain ⟨rfl, canonical⟩ := canonical
        simp only [vectorRests] at settled
        simp only [bagRests] at bags
        simpa [applyBindings, OrderedMatching.isData] using instance_data values body shape canonical settled bags
    | .subst _ _, shape, _, _, _ => by simp [noExplicitSubst] at shape

  theorem instanceList_data {bindings : Bindings} (values : DataOn bindings) : ∀ (patterns : List Pattern),
      allNoExplicitSubst patterns = true → Pattern.hasCanonicalBinderMetadataList patterns = true →
      Settled bindings (vectorRestsList patterns) →
      BagSettled bindings (bagRestsList patterns) → isDataList (patterns.map (applyBindings bindings)) = true
    | [], _, _, _, _ => by simp [OrderedMatching.isDataList]
    | pattern :: patterns, shape, canonical, settled, bags => by
        simp only [allNoExplicitSubst, Bool.and_eq_true] at shape
        simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
        simp only [List.map_cons, OrderedMatching.isDataList, Bool.and_eq_true]
        exact ⟨instance_data values pattern shape.1 canonical.1
            (fun name member => settled name (by simp [vectorRestsList, member]))
            (fun pair member => bags pair (by simp [bagRestsList, member])),
          instanceList_data values patterns shape.2 canonical.2
            (fun name member => settled name (by simp [vectorRestsList, member]))
            (fun pair member => bags pair (by simp [bagRestsList, member]))⟩
end

/-- What a bag's or set's rest leaves: nothing without a rest, else the collection its name is bound to. -/
def RestValue (witness : Bindings) (kind : CollType) (tail : List Pattern) : Option String → Prop
  | none => tail = []
  | some name => lookupOrFvar witness name = .collection kind tail none

/-- The instance of a bag or set pattern: its elements' instances beside what its rest is bound to. -/
theorem bag_instance (witness : Bindings) (kind : CollType) (elements : List Pattern) (rest : Option String)
    (bags : ∀ pair ∈ (rest.map (·, kind)).toList, ∃ tail,
      witness.find? (·.1 == pair.1) = some (pair.1, .collection pair.2 tail none)) :
    ∃ tail, applyBindings witness (.collection kind elements rest) =
        .collection kind (elements.map (applyBindings witness) ++ tail) none ∧ RestValue witness kind tail rest := by
  cases rest with
  | none => exact ⟨[], by simp [applyBindings], rfl⟩
  | some name =>
      obtain ⟨tail, bound⟩ := bags (name, kind) (by simp)
      exact ⟨tail, applyBindings_collection_rest bound, by simp [RestValue, lookupOrFvar, applyBindings, bound]⟩

mutual
  /-- **An instance is matched, by bindings that the instantiation values.** -/
  theorem match_complete (witness : Bindings) : ∀ (pattern : Pattern),
      noExplicitSubst pattern = true → Settled witness (vectorRests pattern) → BagSettled witness (bagRests pattern) →
      ∃ found, MatchRel pattern (applyBindings witness pattern) found ∧ BindingsValued found (lookupOrFvar witness)
    | .fvar name, _, _, _ => by
        refine ⟨_, .fvar, fun key value member => ?_⟩
        simp only [List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        rfl
    | .bvar _, _, _, _ => ⟨[], by simpa [applyBindings] using MatchRel.bvar, fun _ _ member => nomatch member⟩
    | .apply label arguments, shape, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [vectorRests] at settled
        simp only [bagRests] at bags
        obtain ⟨found, matched, valued⟩ := matchList_complete witness arguments shape settled bags
        exact ⟨found, by simpa [applyBindings] using MatchRel.apply (c := label) matched matched.length_eq, valued⟩
    | .collection .vec elements none, shape, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [vectorRests, Option.toList_none, List.append_nil] at settled
        simp only [bagRests] at bags
        obtain ⟨found, matched, valued⟩ := matchList_complete witness elements shape settled bags
        exact ⟨found, by simpa [applyBindings] using MatchRel.vector (rest₂ := none) matched, valued⟩
    | .collection .vec elements (some rest), shape, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [bagRests] at bags
        obtain ⟨tail, bound⟩ := settled rest (by simp [vectorRests])
        obtain ⟨front, matched, valued⟩ := matchList_complete witness elements shape
          (fun name member => settled name (by simp [vectorRests, member])) bags
        have tailValued : BindingsValued [(rest, Pattern.collection .vec tail none)] (lookupOrFvar witness) := by
          intro key value member
          simp only [List.mem_singleton, Prod.mk.injEq] at member
          obtain ⟨rfl, rfl⟩ := member
          simp [lookupOrFvar, applyBindings, bound]
        obtain ⟨found, merged, foundValued⟩ := mergeBindings_some_of_valued front _ _ valued tailValued
        refine ⟨found, ?_, foundValued⟩
        rw [applyBindings_collection_rest bound]
        exact matchRel_vectorRest_iff_split.mpr ⟨_, tail, front, rfl, matched, merged⟩
    | .collection .hashBag elements rest, shape, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [vectorRests] at settled
        obtain ⟨tail, instanceIs, restOk⟩ := bag_instance witness .hashBag elements rest
          (fun pair member => bags pair (by simp [bagRests, member]))
        obtain ⟨found, matched, valued⟩ := bagList_complete witness elements shape settled
          (fun pair member => bags pair (by simp [bagRests, member])) restOk
        exact ⟨found, by rw [instanceIs]; exact .collection (by decide) matched, valued⟩
    | .collection .hashSet elements rest, shape, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [vectorRests] at settled
        obtain ⟨tail, instanceIs, restOk⟩ := bag_instance witness .hashSet elements rest
          (fun pair member => bags pair (by simp [bagRests, member]))
        obtain ⟨found, matched, valued⟩ := bagList_complete witness elements shape settled
          (fun pair member => bags pair (by simp [bagRests, member])) restOk
        exact ⟨found, by rw [instanceIs]; exact .collection (by decide) matched, valued⟩
    | .lambda binder body, shape, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [vectorRests] at settled
        simp only [bagRests] at bags
        obtain ⟨found, matched, valued⟩ := match_complete witness body shape settled bags
        exact ⟨found, by simpa [applyBindings] using MatchRel.lambda (_nm := binder) (_nm' := binder) matched, valued⟩
    | .multiLambda arity binders body, shape, settled, bags => by
        simp only [noExplicitSubst] at shape
        simp only [vectorRests] at settled
        simp only [bagRests] at bags
        obtain ⟨found, matched, valued⟩ := match_complete witness body shape settled bags
        exact ⟨found, by simpa [applyBindings] using
          MatchRel.multiLambda (n := arity) (_nms := binders) (_nms' := binders) matched, valued⟩
    | .subst _ _, shape, _, _ => by simp [noExplicitSubst] at shape

  theorem matchList_complete (witness : Bindings) : ∀ (patterns : List Pattern),
      allNoExplicitSubst patterns = true → Settled witness (vectorRestsList patterns) →
      BagSettled witness (bagRestsList patterns) →
      ∃ found, MatchArgsRel patterns (patterns.map (applyBindings witness)) found ∧
        BindingsValued found (lookupOrFvar witness)
    | [], _, _, _ => ⟨[], .nil, fun _ _ member => nomatch member⟩
    | pattern :: patterns, shape, settled, bags => by
        simp only [allNoExplicitSubst, Bool.and_eq_true] at shape
        obtain ⟨head, headMatched, headValued⟩ := match_complete witness pattern shape.1
          (fun name member => settled name (by simp [vectorRestsList, member]))
          (fun pair member => bags pair (by simp [bagRestsList, member]))
        obtain ⟨tail, tailMatched, tailValued⟩ := matchList_complete witness patterns shape.2
          (fun name member => settled name (by simp [vectorRestsList, member]))
          (fun pair member => bags pair (by simp [bagRestsList, member]))
        obtain ⟨found, merged, valued⟩ := mergeBindings_some_of_valued head tail _ headValued tailValued
        exact ⟨found, .cons headMatched tailMatched merged, valued⟩

  /-- **The instances of a bag's or set's elements beside the rest are matched**, each picked first. -/
  theorem bagList_complete (witness : Bindings) : ∀ (patterns : List Pattern) {rest : Option String}
      {kind : CollType} {tail : List Pattern}, allNoExplicitSubst patterns = true →
      Settled witness (vectorRestsList patterns) → BagSettled witness (bagRestsList patterns) →
      RestValue witness kind tail rest →
      ∃ found, MatchBagRel patterns rest kind (patterns.map (applyBindings witness) ++ tail) found ∧
        BindingsValued found (lookupOrFvar witness)
    | [], none, _, _, _, _, _, empty => by
        simp only [RestValue] at empty
        subst empty
        exact ⟨[], .nilNoRest, fun _ _ member => nomatch member⟩
    | [], some name, kind, tail, _, _, _, bound => by
        simp only [RestValue] at bound
        refine ⟨_, .nilRest, fun key value member => ?_⟩
        simp only [List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact bound.symm
    | pattern :: patterns, rest, kind, tail, shape, settled, bags, restOk => by
        simp only [allNoExplicitSubst, Bool.and_eq_true] at shape
        obtain ⟨head, headMatched, headValued⟩ := match_complete witness pattern shape.1
          (fun name member => settled name (by simp [vectorRestsList, member]))
          (fun pair member => bags pair (by simp [bagRestsList, member]))
        obtain ⟨others, othersMatched, othersValued⟩ := bagList_complete witness patterns shape.2
          (fun name member => settled name (by simp [vectorRestsList, member]))
          (fun pair member => bags pair (by simp [bagRestsList, member])) restOk
        obtain ⟨found, merged, valued⟩ := mergeBindings_some_of_valued head others _ headValued othersValued
        refine ⟨found, .cons 0 (by simp) (by simpa using headMatched) (by simpa using othersMatched) merged, valued⟩
end
