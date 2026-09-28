import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# Substitution invents no operation labels

Several questions about a generated presentation turn on the same thing: a term
built by substitution cannot be headed by an operation that occurred nowhere in
what was substituted.

**This is not the first statement of that in the tree, and the earlier one is
better developed.**  `GSLT/LanguageDef/ConstructorSupport.lean` carries the same
metatheory in `Prop`-valued containment form over the same `Pattern`, `Bindings`
and `MatchRel` — including the `subst` binder elimination and the collection-rest
splice — and adds a permutation and erase theory, an alphabet monotonicity law, a
`mapPattern` homomorphism, a decision procedure with an exactness proof, and
typing bridges.  `Syntax.constructorRefs` is a third collector, carrying arities.

What this module adds, and the reason it exists, is the **Engine and premise
layer**, which the earlier development does not reach: what a relation query can
introduce, what a premise's own patterns carry, and the `matchPattern` form that
an inversion over the executable matcher can consume.  The `Pattern`-level facts
below are restated in `List`-valued form because that layer needed them in that
shape; they should be derived from `ConstructorSupport` rather than maintained as
a second proof stack over the same inductions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.OccurringLabels

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine

/-! ## The labels occurring in a pattern -/

mutual

/-- Every operation label occurring anywhere in a pattern. -/
def labels : Pattern → List String
  | .bvar _ => []
  | .fvar _ => []
  | .apply constructor args => constructor :: labelsList args
  | .lambda _ body => labels body
  | .multiLambda _ _ body => labels body
  | .subst body replacement => labels body ++ labels replacement
  | .collection _ elements _ => labelsList elements

/-- The labels occurring in a list of patterns. -/
def labelsList : List Pattern → List String
  | [] => []
  | pattern :: rest => labels pattern ++ labelsList rest

end

@[simp] theorem labels_bvar (index : Nat) : labels (.bvar index) = [] := rfl
@[simp] theorem labels_fvar (name : String) : labels (.fvar name) = [] := rfl

@[simp] theorem labels_apply (constructor : String) (args : List Pattern) :
    labels (.apply constructor args) = constructor :: labelsList args := rfl

@[simp] theorem labels_lambda (name : Option String) (body : Pattern) :
    labels (.lambda name body) = labels body := rfl

@[simp] theorem labels_multiLambda (arity : Nat) (names : List String) (body : Pattern) :
    labels (.multiLambda arity names body) = labels body := rfl

@[simp] theorem labels_subst (body replacement : Pattern) :
    labels (.subst body replacement) = labels body ++ labels replacement := rfl

@[simp] theorem labels_collection (kind : CollType) (elements : List Pattern)
    (rest : Option String) :
    labels (.collection kind elements rest) = labelsList elements := rfl

@[simp] theorem labelsList_nil : labelsList [] = [] := rfl

@[simp] theorem labelsList_cons (pattern : Pattern) (rest : List Pattern) :
    labelsList (pattern :: rest) = labels pattern ++ labelsList rest := rfl

theorem labelsList_append (first second : List Pattern) :
    labelsList (first ++ second) = labelsList first ++ labelsList second := by
  induction first with
  | nil => simp
  | cons head tail ih => simp [ih, List.append_assoc]

/-- A label of an element is a label of the list it belongs to. -/
theorem mem_labelsList_of_mem {pattern : Pattern} {patterns : List Pattern}
    (member : pattern ∈ patterns) {label : String} (occurs : label ∈ labels pattern) :
    label ∈ labelsList patterns := by
  induction patterns with
  | nil => exact absurd member (List.not_mem_nil)
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | inTail
      · exact List.mem_append_left _ occurs
      · exact List.mem_append_right _ (ih inTail)

/-- A list of metavariables carries no operation label. -/
@[simp] theorem labelsList_fvars (names : List String) :
    labelsList (names.map Pattern.fvar) = [] := by
  induction names with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-! ## Lifting indices changes no label -/

mutual

theorem labels_liftBVars (cutoff shift : Nat) :
    ∀ pattern : Pattern, labels (liftBVars cutoff shift pattern) = labels pattern
  | .bvar index => by
      by_cases high : index ≥ cutoff <;> simp [liftBVars, high]
  | .fvar _ => by simp [liftBVars]
  | .apply _ args => by
      simp only [liftBVars, Substitution.liftBVarsList_eq_map, labels_apply,
        List.cons.injEq, true_and]
      exact labelsList_liftBVars cutoff shift args
  | .lambda _ body => by
      simp only [liftBVars, labels_lambda]
      exact labels_liftBVars (cutoff + 1) shift body
  | .multiLambda arity _ body => by
      simp only [liftBVars, labels_multiLambda]
      exact labels_liftBVars (cutoff + arity) shift body
  | .subst body replacement => by
      simp only [liftBVars, labels_subst]
      rw [labels_liftBVars (cutoff + 1) shift body, labels_liftBVars cutoff shift replacement]
  | .collection _ elements _ => by
      simp only [liftBVars, Substitution.liftBVarsList_eq_map, labels_collection]
      exact labelsList_liftBVars cutoff shift elements

theorem labelsList_liftBVars (cutoff shift : Nat) :
    ∀ patterns : List Pattern,
      labelsList (patterns.map (liftBVars cutoff shift)) = labelsList patterns
  | [] => rfl
  | pattern :: rest => by
      simp only [List.map_cons, labelsList_cons]
      rw [labels_liftBVars cutoff shift pattern, labelsList_liftBVars cutoff shift rest]

end

/-! ## Eliminating a bound level introduces only what it substitutes -/

mutual

theorem labels_instantiateBVarAt (depth : Nat) (replacement : Pattern) :
    ∀ body : Pattern,
      labels (instantiateBVarAt depth replacement body) ⊆ labels body ++ labels replacement
  | .bvar index => by
      rcases Nat.lt_or_ge index depth with low | high
      · simp [instantiateBVarAt, low]
      · rcases Nat.eq_or_lt_of_le high with equal | greater
        · have shape : index = depth := equal.symm
          simp only [instantiateBVarAt, if_neg (Nat.not_lt.mpr high), if_pos shape,
            labels_bvar, List.nil_append]
          exact (labels_liftBVars 0 depth replacement) ▸ List.Subset.refl _
        · have notEqual : ¬ index = depth := (Nat.ne_of_gt greater)
          simp [instantiateBVarAt, Nat.not_lt.mpr high, notEqual]
  | .fvar _ => by simp [instantiateBVarAt]
  | .apply constructor args => by
      simp only [instantiateBVarAt, labels_apply]
      intro label member
      rcases List.mem_cons.mp member with rfl | inArgs
      · exact List.mem_append_left _ (List.mem_cons_self ..)
      · rcases List.mem_append.mp (labelsList_instantiateBVarAt depth replacement args inArgs)
          with inList | inReplacement
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ inList)
        · exact List.mem_append_right _ inReplacement
  | .lambda _ body => by
      simp only [instantiateBVarAt, labels_lambda]
      exact labels_instantiateBVarAt (depth + 1) replacement body
  | .multiLambda arity _ body => by
      simp only [instantiateBVarAt, labels_multiLambda]
      exact labels_instantiateBVarAt (depth + arity) replacement body
  | .subst body nested => by
      simp only [instantiateBVarAt, labels_subst]
      intro label member
      rcases List.mem_append.mp member with inBody | inNested
      · rcases List.mem_append.mp
          (labels_instantiateBVarAt (depth + 1) replacement body inBody) with here | there
        · exact List.mem_append_left _ (List.mem_append_left _ here)
        · exact List.mem_append_right _ there
      · rcases List.mem_append.mp
          (labels_instantiateBVarAt depth replacement nested inNested) with here | there
        · exact List.mem_append_left _ (List.mem_append_right _ here)
        · exact List.mem_append_right _ there
  | .collection _ elements _ => by
      simp only [instantiateBVarAt, labels_collection]
      exact labelsList_instantiateBVarAt depth replacement elements

theorem labelsList_instantiateBVarAt (depth : Nat) (replacement : Pattern) :
    ∀ patterns : List Pattern,
      labelsList (patterns.map (instantiateBVarAt depth replacement))
        ⊆ labelsList patterns ++ labels replacement
  | [] => by simp
  | pattern :: rest => by
      simp only [List.map_cons, labelsList_cons]
      intro label member
      rcases List.mem_append.mp member with inHead | inTail
      · rcases List.mem_append.mp
          (labels_instantiateBVarAt depth replacement pattern inHead) with here | there
        · exact List.mem_append_left _ (List.mem_append_left _ here)
        · exact List.mem_append_right _ there
      · rcases List.mem_append.mp
          (labelsList_instantiateBVarAt depth replacement rest inTail) with here | there
        · exact List.mem_append_left _ (List.mem_append_right _ here)
        · exact List.mem_append_right _ there

end

theorem labels_instantiateBVar (replacement body : Pattern) :
    labels (instantiateBVar replacement body) ⊆ labels body ++ labels replacement :=
  labels_instantiateBVarAt 0 replacement body

/-! ## Applying bindings introduces only what it substitutes

The statement with content.  `applyBindings` is not plain structural recursion:
the `subst` case eliminates a binder, and the `collection` case splices a bound
collection's elements into the rest position.  Both are where a label could in
principle appear from nowhere, and neither does. -/

/-- The labels occurring in the values a binding list substitutes. -/
def bindingLabels : Bindings → List String
  | [] => []
  | (_, value) :: rest => labels value ++ bindingLabels rest

theorem mem_bindingLabels_of_mem {name : String} {value : Pattern} {bindings : Bindings}
    (member : (name, value) ∈ bindings) {label : String} (occurs : label ∈ labels value) :
    label ∈ bindingLabels bindings := by
  induction bindings with
  | nil => exact absurd member (List.not_mem_nil)
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | inTail
      · exact List.mem_append_left _ occurs
      · exact List.mem_append_right _ (ih inTail)

/-- The value a lookup returns is one of the bound values. -/
theorem mem_bindingLabels_of_find? {bindings : Bindings} {name : String}
    {entry : String × Pattern}
    (found : bindings.find? (fun pair => pair.1 == name) = some entry)
    {label : String} (occurs : label ∈ labels entry.2) :
    label ∈ bindingLabels bindings :=
  mem_bindingLabels_of_mem (name := entry.1) (value := entry.2)
    (by simpa using List.mem_of_find?_eq_some found) occurs

mutual

theorem labels_applyBindings (bindings : Bindings) :
    ∀ pattern : Pattern,
      labels (applyBindings bindings pattern) ⊆ labels pattern ++ bindingLabels bindings
  | .bvar _ => by simp [applyBindings]
  | .fvar name => by
      rcases found : bindings.find? (fun pair => pair.1 == name) with _ | entry
      · simp [applyBindings, found]
      · intro label occurs
        simp only [applyBindings, found] at occurs
        exact List.mem_append_right _ (mem_bindingLabels_of_find? found occurs)
  | .apply constructor args => by
      simp only [applyBindings, labels_apply]
      intro label member
      rcases List.mem_cons.mp member with rfl | inArgs
      · exact List.mem_append_left _ (List.mem_cons_self ..)
      · rcases List.mem_append.mp (labelsList_applyBindings bindings args inArgs)
          with inList | inBindings
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ inList)
        · exact List.mem_append_right _ inBindings
  | .lambda _ body => by
      simp only [applyBindings, labels_lambda]
      exact labels_applyBindings bindings body
  | .multiLambda _ _ body => by
      simp only [applyBindings, labels_multiLambda]
      exact labels_applyBindings bindings body
  | .subst body replacement => by
      simp only [applyBindings]
      intro label occurs
      rcases List.mem_append.mp
        (labels_instantiateBVar _ _ occurs) with inBody | inReplacement
      · rcases List.mem_append.mp (labels_applyBindings bindings body inBody)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_left _ here)
        · exact List.mem_append_right _ there
      · rcases List.mem_append.mp (labels_applyBindings bindings replacement inReplacement)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_right _ here)
        · exact List.mem_append_right _ there
  | .collection kind elements rest => by
      intro label occurs
      rw [applyBindings.eq_def] at occurs
      simp only [labels_collection, labelsList_append] at occurs
      rcases List.mem_append.mp occurs with inElements | inRest
      · rcases List.mem_append.mp (labelsList_applyBindings bindings elements inElements)
          with here | there
        · exact List.mem_append_left _ here
        · exact List.mem_append_right _ there
      · refine List.mem_append_right _ ?_
        rcases rest with _ | restVar
        · simp at inRest
        · rcases found : bindings.find? (fun pair => pair.1 == restVar) with _ | entry
          · simp [found] at inRest
          · rcases entry with ⟨entryName, entryValue⟩
            rcases entryValue with _ | _ | _ | _ | _ | _ | ⟨boundKind, boundElements, boundRest⟩
            all_goals simp only [found] at inRest
            all_goals try simp at inRest
            rcases boundRest with _ | boundRestVar
            · by_cases sameKind : boundKind = kind
              · simp only [sameKind, if_pos] at inRest
                exact mem_bindingLabels_of_find? found
                  (by simpa [labels_collection] using inRest)
              · simp only [if_neg sameKind] at inRest
                simp at inRest
            · simp at inRest

theorem labelsList_applyBindings (bindings : Bindings) :
    ∀ patterns : List Pattern,
      labelsList (patterns.map (applyBindings bindings))
        ⊆ labelsList patterns ++ bindingLabels bindings
  | [] => by simp
  | pattern :: rest => by
      simp only [List.map_cons, labelsList_cons]
      intro label member
      rcases List.mem_append.mp member with inHead | inTail
      · rcases List.mem_append.mp (labels_applyBindings bindings pattern inHead)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_left _ here)
        · exact List.mem_append_right _ there
      · rcases List.mem_append.mp (labelsList_applyBindings bindings rest inTail)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_right _ here)
        · exact List.mem_append_right _ there

end

mutual
theorem labels_applyBindingsScoped (lhs : Pattern) (bindings : Bindings) :
    ∀ (d : Nat) (pattern : Pattern),
      labels (Match.applyBindingsScoped lhs bindings d pattern)
        ⊆ labels pattern ++ bindingLabels bindings
  | _, .bvar _ => by simp [Match.applyBindingsScoped]
  | _, .fvar name => by
      rcases found : bindings.find? (fun pair => pair.1 == name) with _ | entry
      · simp [Match.applyBindingsScoped, found]
      · intro label occurs
        simp only [Match.applyBindingsScoped, found] at occurs
        rcases hcap : Match.captureDepth name 0 lhs with _ | dc
        · rw [hcap] at occurs
          exact List.mem_append_right _ (mem_bindingLabels_of_find? found occurs)
        · rw [hcap, labels_liftBVars] at occurs
          exact List.mem_append_right _ (mem_bindingLabels_of_find? found occurs)
  | _, .apply constructor args => by
      simp only [Match.applyBindingsScoped, labels_apply]
      intro label member
      rcases List.mem_cons.mp member with rfl | inArgs
      · exact List.mem_append_left _ (List.mem_cons_self ..)
      · rcases List.mem_append.mp (labelsList_applyBindingsScoped lhs bindings _ args inArgs)
          with inList | inBindings
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ inList)
        · exact List.mem_append_right _ inBindings
  | _, .lambda _ body => by
      simp only [Match.applyBindingsScoped, labels_lambda]
      exact labels_applyBindingsScoped lhs bindings _ body
  | _, .multiLambda _ _ body => by
      simp only [Match.applyBindingsScoped, labels_multiLambda]
      exact labels_applyBindingsScoped lhs bindings _ body
  | _, .subst body replacement => by
      simp only [Match.applyBindingsScoped]
      intro label occurs
      rcases List.mem_append.mp
        (labels_instantiateBVar _ _ occurs) with inBody | inReplacement
      · rcases List.mem_append.mp (labels_applyBindingsScoped lhs bindings _ body inBody)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_left _ here)
        · exact List.mem_append_right _ there
      · rcases List.mem_append.mp (labels_applyBindingsScoped lhs bindings _ replacement inReplacement)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_right _ here)
        · exact List.mem_append_right _ there
  | _, .collection kind elements rest => by
      intro label occurs
      rw [Match.applyBindingsScoped.eq_def] at occurs
      simp only [labels_collection, labelsList_append] at occurs
      rcases List.mem_append.mp occurs with inElements | inRest
      · rcases List.mem_append.mp (labelsList_applyBindingsScoped lhs bindings _ elements inElements)
          with here | there
        · exact List.mem_append_left _ here
        · exact List.mem_append_right _ there
      · refine List.mem_append_right _ ?_
        simp only [Mettapedia.OSLF.MeTTaIL.Match.restSplice] at inRest
        rcases rest with _ | restVar
        · simp at inRest
        · rcases found : bindings.find? (fun pair => pair.1 == restVar) with _ | entry
          · simp [found] at inRest
          · rcases entry with ⟨entryName, entryValue⟩
            rcases entryValue with _ | _ | _ | _ | _ | _ | ⟨boundKind, boundElements, boundRest⟩
            all_goals simp only [found] at inRest
            all_goals try simp at inRest
            rcases boundRest with _ | boundRestVar
            · by_cases sameKind : boundKind = kind
              · simp only [sameKind, if_pos] at inRest
                rcases hcap : Mettapedia.OSLF.MeTTaIL.Match.captureDepth restVar 0 lhs
                  with _ | dc
                · rw [hcap] at inRest
                  exact mem_bindingLabels_of_find? found
                    (by simpa [labels_collection] using inRest)
                · rw [hcap, labelsList_liftBVars] at inRest
                  exact mem_bindingLabels_of_find? found
                    (by simpa [labels_collection] using inRest)
              · simp only [if_neg sameKind] at inRest
                simp at inRest
            · simp at inRest

theorem labelsList_applyBindingsScoped (lhs : Pattern) (bindings : Bindings) :
    ∀ (d : Nat) (patterns : List Pattern),
      labelsList (Match.applyBindingsScopedList lhs bindings d patterns)
        ⊆ labelsList patterns ++ bindingLabels bindings
  | _, [] => by simp [Match.applyBindingsScopedList]
  | _, pattern :: rest => by
      simp only [Match.applyBindingsScopedList, labelsList_cons]
      intro label member
      rcases List.mem_append.mp member with inHead | inTail
      · rcases List.mem_append.mp (labels_applyBindingsScoped lhs bindings _ pattern inHead)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_left _ here)
        · exact List.mem_append_right _ there
      · rcases List.mem_append.mp (labelsList_applyBindingsScoped lhs bindings _ rest inTail)
          with here | there
        · exact List.mem_append_left _ (List.mem_append_right _ here)
        · exact List.mem_append_right _ there
end



/-- Depth-aligned rule firing introduces no labels beyond the right-hand side's own
and those carried by the bindings. -/
theorem labels_applyRuleBindings (rule : RewriteRule) (bindings : Bindings) :
    labels (Match.applyRuleBindings rule bindings)
      ⊆ labels rule.right ++ bindingLabels bindings :=
  labels_applyBindingsScoped rule.left bindings 0 rule.right

/-! ## Matching binds only what it matched

The companion to the previous section.  Substitution introduces no label that was
not in the pattern or in the values; matching produces no value whose labels were
not in the term.  Together they say a step's target carries only labels of the
rule and of the source. -/

/-- Labels are monotone in the list. -/
theorem labelsList_mono {first second : List Pattern} (contained : first ⊆ second) :
    labelsList first ⊆ labelsList second := by
  intro label member
  induction first with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_append.mp member with inHead | inTail
      · exact mem_labelsList_of_mem (contained (List.mem_cons_self ..)) inHead
      · exact ih (fun _ m => contained (List.mem_cons_of_mem _ m)) inTail

/-- **Merging introduces nothing.**  Every entry of a merge comes from one of the
two lists, so its labels do too. -/
theorem bindingLabels_mergeBindings :
    ∀ (accumulator extra : Bindings) {result : Bindings},
      mergeBindings accumulator extra = some result →
      bindingLabels result ⊆ bindingLabels accumulator ++ bindingLabels extra
  | accumulator, [], result, merged => by
      have same : result = accumulator := by
        simpa [mergeBindings] using merged.symm
      subst same
      simp [bindingLabels]
  | accumulator, (name, value) :: rest, result, merged => by
      simp only [mergeBindings, List.foldlM_cons] at merged
      rcases found : accumulator.find? (fun pair => pair.1 == name) with _ | entry
      · rw [found] at merged
        have tail := bindingLabels_mergeBindings ((name, value) :: accumulator) rest merged
        intro label member
        rcases List.mem_append.mp (tail member) with inAcc | inRest
        · rcases List.mem_append.mp inAcc with inValue | inOriginal
          · exact List.mem_append_right _ (List.mem_append_left _ inValue)
          · exact List.mem_append_left _ inOriginal
        · exact List.mem_append_right _ (List.mem_append_right _ inRest)
      · rw [found] at merged
        rcases entry with ⟨entryName, existing⟩
        by_cases same : existing == value
        · simp only [same, if_pos] at merged
          have tail := bindingLabels_mergeBindings accumulator rest merged
          intro label member
          rcases List.mem_append.mp (tail member) with inAcc | inRest
          · exact List.mem_append_left _ inAcc
          · exact List.mem_append_right _ (List.mem_append_right _ inRest)
        · simp only [same] at merged
          exact absurd merged (by simp)

mutual

/-- **Matching binds only labels of the term.**  A metavariable is bound to a
subterm, and every other case passes the obligation down; the sibling merges
introduce nothing, and a bag's rest variable is bound to the elements that were
left. -/
theorem bindingLabels_matchRel :
    ∀ {pattern term : Pattern} {bindings : Bindings},
      MatchRel pattern term bindings → bindingLabels bindings ⊆ labels term
  | _, _, _, .fvar => by intro label member; simpa [bindingLabels] using member
  | _, _, _, .bvar => by simp [bindingLabels]
  | _, _, _, .apply argumentsMatch _ => by
      intro label member
      exact List.mem_cons_of_mem _ (bindingLabelsList_matchArgsRel argumentsMatch member)
  | .lambda _ bodyPat, .lambda _ bodyConcrete, _, .lambda bodyMatch =>
      bindingLabels_matchRel (pattern := bodyPat) (term := bodyConcrete) bodyMatch
  | .multiLambda _ _ bodyPat, .multiLambda _ _ bodyConcrete, _, .multiLambda bodyMatch =>
      bindingLabels_matchRel (pattern := bodyPat) (term := bodyConcrete) bodyMatch
  | _, _, _, .collection _ bagMatch => bindingLabels_matchBagRel bagMatch
  | _, _, _, .vector argumentsMatch => bindingLabelsList_matchArgsRel argumentsMatch
  | _, _, _, .vectorRest prefixMatch merged => by
      intro label member
      rcases List.mem_append.mp (bindingLabels_mergeBindings _ _ merged member)
        with inPrefix | inSuffix
      · exact labelsList_mono (fun _ m => List.mem_of_mem_take m)
          (bindingLabelsList_matchArgsRel prefixMatch inPrefix)
      · exact labelsList_mono (fun _ m => List.mem_of_mem_drop m)
          (by simpa [bindingLabels] using inSuffix)
  | _, _, _, .subst bodyMatch replacementMatch merged => by
      intro label member
      rcases List.mem_append.mp (bindingLabels_mergeBindings _ _ merged member)
        with inBody | inReplacement
      · exact List.mem_append_left _ (bindingLabels_matchRel bodyMatch inBody)
      · exact List.mem_append_right _ (bindingLabels_matchRel replacementMatch inReplacement)

theorem bindingLabelsList_matchArgsRel :
    ∀ {patterns terms : List Pattern} {bindings : Bindings},
      MatchArgsRel patterns terms bindings → bindingLabels bindings ⊆ labelsList terms
  | _, _, _, .nil => by simp [bindingLabels]
  | _, _, _, .cons headMatch tailMatch merged => by
      intro label member
      rcases List.mem_append.mp (bindingLabels_mergeBindings _ _ merged member)
        with inHead | inTail
      · exact List.mem_append_left _ (bindingLabels_matchRel headMatch inHead)
      · exact List.mem_append_right _ (bindingLabelsList_matchArgsRel tailMatch inTail)

theorem bindingLabels_matchBagRel :
    ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType}
      {terms : List Pattern} {bindings : Bindings},
      MatchBagRel patterns rest kind terms bindings →
      bindingLabels bindings ⊆ labelsList terms
  | _, _, _, _, _, .nilNoRest => by simp [bindingLabels]
  | _, _, _, _, _, .nilRest => by
      intro label member
      simpa [bindingLabels] using member
  | _, _, _, terms, _, .cons index bounded headMatch restMatch merged => by
      intro label member
      rcases List.mem_append.mp (bindingLabels_mergeBindings _ _ merged member)
        with inHead | inRest
      · exact mem_labelsList_of_mem (List.getElem_mem bounded)
          (bindingLabels_matchRel (term := terms[index]) headMatch inHead)
      · exact labelsList_mono (fun _ m => List.mem_of_mem_eraseIdx m)
          (bindingLabels_matchBagRel (terms := terms.eraseIdx index) restMatch inRest)

end

/-- **So a match binds only labels of the term it matched**, in the form the
matcher is written in. -/
theorem bindingLabels_matchPattern {pattern term : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern pattern term) :
    bindingLabels bindings ⊆ labels term :=
  bindingLabels_matchRel (matchPattern_iff_matchRel.mp matched)

/-- The labels occurring in a premise's own patterns. -/
def premiseLabels : Premise → List String
  | .freshness condition => labels condition.term
  | .congruence source target => labels source ++ labels target
  | .scopedStep step => labels step.source ++ labels step.target
  | .relationQuery _ arguments => labelsList arguments
  | .forAll _ _ body => premiseLabels body

/-! ## The relation layer introduces only its tuples

A `relationQuery` premise is the one place a rule can acquire material from
outside the term it matched.  What it acquires is bounded by the tuple it matched
against, and the three steps of that are here, so the condition a presentation
must meet is a statement about its relation tuples and nothing more. -/

/-- One relation argument binds only labels of the value it read. -/
theorem bindingLabels_matchRelationArgument (bindings : Bindings)
    (argument value : Pattern) {result : Bindings}
    (member : result ∈ matchRelationArgument bindings argument value) :
    bindingLabels result ⊆ labels value := by
  cases argument with
  | fvar name =>
      simp only [matchRelationArgument] at member
      rcases found : bindings.lookup name with _ | existing
      · rw [found] at member
        simp only [List.mem_singleton] at member
        subst member
        simp [bindingLabels]
      · rw [found] at member
        by_cases same : existing = value
        · simp only [same, if_pos, List.mem_singleton] at member
          subst member
          simp [bindingLabels]
        · simp [same] at member
  | bvar _ => exact bindingLabels_matchPattern member
  | apply _ _ => exact bindingLabels_matchPattern member
  | lambda _ _ => exact bindingLabels_matchPattern member
  | multiLambda _ _ _ => exact bindingLabels_matchPattern member
  | subst _ _ => exact bindingLabels_matchPattern member
  | collection _ _ _ => exact bindingLabels_matchPattern member

/-- A relation row binds only labels of the row. -/
theorem bindingLabels_matchRelationArgs :
    ∀ (seed : Bindings) (arguments tuple : List Pattern) {result : Bindings},
      result ∈ matchRelationArgs seed arguments tuple →
      bindingLabels result ⊆ labelsList tuple
  | _, [], [], _, member => by
      simp only [matchRelationArgs, List.mem_singleton] at member
      subst member
      simp [bindingLabels]
  | _, [], _ :: _, _, member => by simp [matchRelationArgs] at member
  | _, _ :: _, [], _, member => by simp [matchRelationArgs] at member
  | seed, argument :: arguments, value :: values, result, member => by
      simp only [matchRelationArgs, List.mem_flatMap] at member
      obtain ⟨headBindings, headMember, rest⟩ := member
      rcases extended : mergeBindings seed headBindings with _ | extendedBindings
      · rw [extended] at rest; simp at rest
      · rw [extended] at rest
        simp only [List.mem_filterMap] at rest
        obtain ⟨tailBindings, tailMember, merged⟩ := rest
        intro label occurs
        rcases List.mem_append.mp
          (bindingLabels_mergeBindings _ _ merged occurs) with inHead | inTail
        · exact List.mem_append_left _
            (bindingLabels_matchRelationArgument seed argument value headMember inHead)
        · exact List.mem_append_right _
            (bindingLabels_matchRelationArgs extendedBindings arguments values
              tailMember inTail)

/-- **The built-in relations echo the query's own arguments.**  So they introduce
no label the query did not already carry. -/
theorem labelsList_builtinRelationTuples (lang : LanguageDef) (relation : String)
    (arguments : List Pattern) {tuple : List Pattern}
    (member : tuple ∈ builtinRelationTuples lang relation arguments) :
    labelsList tuple ⊆ labelsList arguments := by
  unfold builtinRelationTuples at member
  split at member
  · rename_i lhs rhs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    intro label occurs
    rcases member with rfl | rfl
    · simp only [labelsList_cons, labelsList_nil, List.append_nil] at occurs ⊢
      rcases List.mem_append.mp occurs with here | there
      · exact List.mem_append_left _ here
      · exact List.mem_append_left _ there
    · simp only [labelsList_cons, labelsList_nil, List.append_nil] at occurs ⊢
      rcases List.mem_append.mp occurs with here | there
      · exact List.mem_append_right _ here
      · exact List.mem_append_right _ there
  · simp at member

/-- **So a relation query introduces only what its tuple carried.**  The tuple is
named, so a presentation's obligation is a statement about the rows its relations
can produce. -/
theorem bindingLabels_relationQueryStep (env : RelationEnv) (lang : LanguageDef)
    (bindings : Bindings) (relation : String) (arguments : List Pattern)
    {result : Bindings}
    (member : result ∈ relationQueryStep env lang bindings relation arguments) :
    ∃ tuple ∈ builtinRelationTuples lang relation
          (arguments.map (applyBindings bindings))
        ++ env.tuples relation (arguments.map (applyBindings bindings)),
      bindingLabels result ⊆ bindingLabels bindings ++ labelsList tuple := by
  simp only [relationQueryStep, List.mem_flatMap] at member
  obtain ⟨tuple, tupleMember, rest⟩ := member
  simp only [List.mem_filterMap] at rest
  obtain ⟨premiseBindings, premiseMember, merged⟩ := rest
  refine ⟨tuple, tupleMember, ?_⟩
  intro label occurs
  rcases List.mem_append.mp
    (bindingLabels_mergeBindings _ _ merged occurs) with inSeed | inPremise
  · exact List.mem_append_left _ inSeed
  · exact List.mem_append_right _
      (bindingLabels_matchRelationArgs bindings arguments tuple premiseMember inPremise)

/-! ## Both signs, on the two cases that carry the content

The `subst` and `collection` cases are where a label could appear from nowhere.
Each is checked in both directions: a label that was substituted does occur, and
one that was not does not. -/

namespace Examples

/-- Substituting into an explicit binder carries the replacement's label in. -/
example :
    labels (applyBindings [("x", .apply "P" [])] (.subst (.bvar 0) (.fvar "x")))
      = ["P"] := by decide +kernel

/-- And introduces nothing else: a label bound to an unused variable stays out. -/
example :
    labels (applyBindings [("y", .apply "Q" [])] (.subst (.bvar 0) (.apply "P" [])))
      = ["P"] := by decide +kernel

/-- Splicing a bound collection into a rest position carries its labels in. -/
example :
    labels (applyBindings [("rest", .collection .hashBag [.apply "R" []] none)]
        (.collection .hashBag [.apply "S" []] (some "rest")))
      = ["S", "R"] := by decide +kernel

/-- And a rest variable bound to a collection of the *wrong* kind splices
nothing, so its labels stay out. -/
example :
    labels (applyBindings [("rest", .collection .vec [.apply "R" []] none)]
        (.collection .hashBag [.apply "S" []] (some "rest")))
      = ["S"] := by decide +kernel

end Examples

end Mettapedia.OSLF.MeTTaIL.OccurringLabels
