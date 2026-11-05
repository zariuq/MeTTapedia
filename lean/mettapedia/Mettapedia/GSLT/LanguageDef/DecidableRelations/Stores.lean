import Mettapedia.GSLT.LanguageDef.DecidableRelations.Core

/-!
# Stores that decide their relations

A store answers relation queries. A relation environment returns, for a relation and its instantiated arguments, the
tuples a premise may match. A **certified store** decides a relation in a region: on every argument tuple of the
region it answers either the relation or its complement, never both.

**Any decision procedure is a certified store** (`ofDecision`). It answers the relation with the query itself where
the procedure says yes, and the complement where it says no (`ofDecision_complemented`).

The region is first-order ground arguments, constructor applications all the way down (`FirstOrder`). There,
answering is exact: a first-order pattern matches exactly the term equal to it (`matchPattern_firstOrder`), so a query
is answered exactly by the tuples equal to it (`answers_iff`).

A **closed fact store** is the decision procedure of membership in finitely many ground tuples (`factStore`): the
relation holds of exactly the stored tuples, and its complement of every other first-order tuple
(`factStore_answers_iff`, `factStore_answers_complement_iff`). This is the closed-world reading of the store, proved
rather than assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

/-! ## First-order ground terms -/

/-- **A first-order ground term**: constructor applications all the way down. -/
inductive FirstOrder : Pattern → Prop
  | apply {constructor : String} {arguments : List Pattern} :
      (∀ argument ∈ arguments, FirstOrder argument) → FirstOrder (.apply constructor arguments)

mutual
/-- Whether a pattern is a first-order ground term (`isFirstOrder_iff`). -/
def isFirstOrder : Pattern → Bool
  | .apply _ arguments => isFirstOrderList arguments
  | _ => false

/-- Whether every pattern of a list is a first-order ground term. -/
def isFirstOrderList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => isFirstOrder pattern && isFirstOrderList patterns
end

theorem isFirstOrderList_iff : ∀ {patterns : List Pattern},
    isFirstOrderList patterns = true ↔ ∀ pattern ∈ patterns, isFirstOrder pattern = true
  | [] => by simp [isFirstOrderList]
  | pattern :: patterns => by simp [isFirstOrderList, isFirstOrderList_iff]

/-- **The check decides first-order ground terms.** -/
theorem isFirstOrder_iff (pattern : Pattern) : isFirstOrder pattern = true ↔ FirstOrder pattern := by
  constructor
  · induction pattern using Pattern.inductionOn with
    | happly constructor arguments inner =>
      intro checked
      simp only [isFirstOrder, isFirstOrderList_iff] at checked
      exact .apply fun argument member => inner argument member (checked argument member)
    | hbvar => simp [isFirstOrder]
    | hfvar => simp [isFirstOrder]
    | hlambda => simp [isFirstOrder]
    | hmultiLambda => simp [isFirstOrder]
    | hsubst => simp [isFirstOrder]
    | hcollection => simp [isFirstOrder]
  · intro first
    induction first with
    | @apply constructor arguments _ inner =>
      simp only [isFirstOrder, isFirstOrderList_iff]
      exact inner

theorem isFirstOrderList_iff_firstOrder {patterns : List Pattern} :
    isFirstOrderList patterns = true ↔ ∀ pattern ∈ patterns, FirstOrder pattern := by
  rw [isFirstOrderList_iff]
  exact forall₂_congr fun pattern _ => isFirstOrder_iff pattern

/-- Bindings leave a first-order ground term unchanged. -/
theorem applyBindings_firstOrder (bindings : Bindings) {term : Pattern} (first : FirstOrder term) :
    applyBindings bindings term = term := by
  induction first with
  | @apply constructor arguments _ unchanged =>
      simp only [applyBindings]
      congr 1
      conv => rhs; rw [← List.map_id arguments]
      exact List.map_congr_left unchanged

/-- Merging nothing into nothing gives nothing. -/
theorem mergeBindings_nil_nil : mergeBindings [] [] = some [] := rfl

/-- Merging nothing into bindings keeps them. -/
theorem mergeBindings_nil_right (bindings : Bindings) : mergeBindings bindings [] = some bindings := rfl

mutual
  /-- **A first-order pattern matches exactly the term equal to it.** -/
  theorem matchPattern_firstOrder : ∀ {pattern : Pattern}, FirstOrder pattern → ∀ term : Pattern,
      matchPattern pattern term = if pattern = term then [[]] else []
    | .apply constructor arguments, .apply members, term => by
        cases term with
        | apply other values =>
            have list := matchArgs_firstOrder members values
            by_cases same : constructor = other ∧ arguments.length = values.length
            · obtain ⟨rfl, lengths⟩ := same
              simp only [matchPattern, beq_self_eq_true, lengths, Bool.and_self, if_true, list]
              by_cases equal : arguments = values
              · subst equal; simp
              · simp [equal]
            · have notEqual : Pattern.apply constructor arguments ≠ .apply other values := by
                intro equal
                cases equal
                exact same ⟨rfl, rfl⟩
              rw [if_neg notEqual]
              simp only [matchPattern]
              split
              · rename_i condition
                simp only [Bool.and_eq_true, beq_iff_eq] at condition
                exact absurd condition same
              · rfl
        | fvar _ => simp [matchPattern]
        | bvar _ => simp [matchPattern]
        | lambda _ _ => simp [matchPattern]
        | multiLambda _ _ _ => simp [matchPattern]
        | subst _ _ => simp [matchPattern]
        | collection _ _ _ => simp [matchPattern]

  /-- First-order patterns match exactly the list equal to them. -/
  theorem matchArgs_firstOrder : ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, FirstOrder pattern) →
      ∀ terms : List Pattern, matchArgs patterns terms = if patterns = terms then [[]] else []
    | [], _, [] => by simp [matchArgs]
    | [], _, _ :: _ => by simp [matchArgs]
    | _ :: _, _, [] => by simp [matchArgs]
    | pattern :: patterns, first, term :: terms => by
        have head := matchPattern_firstOrder (first pattern (List.mem_cons_self ..)) term
        have tail := matchArgs_firstOrder (fun other member => first other (List.mem_cons_of_mem _ member)) terms
        simp only [matchArgs, head, tail]
        by_cases headEqual : pattern = term
        · subst headEqual
          by_cases tailEqual : patterns = terms
          · subst tailEqual; simp [mergeBindings_nil_nil]
          · simp [tailEqual]
        · simp [headEqual]
end

/-- A query of first-order arguments matches exactly the tuple equal to it, from any bindings. -/
theorem matchRelationArgs_firstOrder (seed : Bindings) : ∀ {arguments : List Pattern},
    (∀ argument ∈ arguments, FirstOrder argument) → ∀ values : List Pattern,
      matchRelationArgs seed arguments values = if arguments = values then [[]] else []
  | [], _, [] => by simp [matchRelationArgs]
  | [], _, _ :: _ => by simp [matchRelationArgs]
  | _ :: _, _, [] => by simp [matchRelationArgs]
  | argument :: arguments, first, value :: values => by
      have tail := matchRelationArgs_firstOrder seed
        (fun other member => first other (List.mem_cons_of_mem _ member)) values
      have head : matchRelationArgument seed argument value = if argument = value then [[]] else [] := by
        cases first argument (List.mem_cons_self ..) with
        | apply members => exact matchPattern_firstOrder (.apply members) value
      simp only [matchRelationArgs, head]
      by_cases headEqual : argument = value
      · subst headEqual
        simp only [if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, mergeBindings_nil_right, tail]
        by_cases tailEqual : arguments = values
        · subst tailEqual; simp [mergeBindings_nil_nil]
        · simp [tailEqual]
      · simp [headEqual]

/-- **A query of first-order arguments is answered exactly by the tuples equal to it**, among the built-in tuples
and the store's. -/
theorem answers_iff {relEnv : RelationEnv} {language : LanguageDef} {relation : String} {arguments : List Pattern}
    (first : ∀ argument ∈ arguments, FirstOrder argument) :
    Answers relEnv language relation arguments ↔
      arguments ∈ builtinRelationTuples language relation arguments ++ relEnv.tuples relation arguments := by
  have instantiated : arguments.map (applyBindings []) = arguments := by
    conv => rhs; rw [← List.map_id arguments]
    exact List.map_congr_left fun argument member => applyBindings_firstOrder [] (first argument member)
  simp only [Answers, relationQueryStep, instantiated, ne_eq, List.flatMap_eq_nil_iff, not_forall, exists_prop]
  constructor
  · rintro ⟨tuple, member, nonempty⟩
    rw [matchRelationArgs_firstOrder [] first tuple] at nonempty
    by_cases equal : arguments = tuple
    · subst equal; exact member
    · simp [equal] at nonempty
  · intro member
    refine ⟨arguments, member, ?_⟩
    rw [matchRelationArgs_firstOrder [] first arguments]
    simp [mergeBindings_nil_nil]

/-! ## Decision procedures as stores -/

/-- **A decision procedure as a store**: it answers `relation` with the query itself where `decide` says yes, and
`complement` where it says no. -/
def ofDecision (relation complement : String) (decide : List Pattern → Bool) : RelationEnv where
  tuples name arguments :=
    if name = relation then (if decide arguments then [arguments] else [])
    else if name = complement then (if decide arguments then [] else [arguments])
    else []

/-- The built-in relations are `eq` alone. -/
theorem builtinRelationTuples_eq_nil {language : LanguageDef} {relation : String} (notEq : relation ≠ "eq")
    (arguments : List Pattern) : builtinRelationTuples language relation arguments = [] := by
  unfold builtinRelationTuples
  split
  · rename_i lhs rhs; exact absurd rfl notEq
  · rfl

variable {relation complement : String} {decide : List Pattern → Bool} {language : LanguageDef}

/-- The store answers the relation exactly where the procedure says yes. -/
theorem ofDecision_answers_iff (notEq : relation ≠ "eq") {arguments : List Pattern}
    (first : ∀ argument ∈ arguments, FirstOrder argument) :
    Answers (ofDecision relation complement decide) language relation arguments ↔ decide arguments = true := by
  rw [answers_iff first, builtinRelationTuples_eq_nil notEq]
  by_cases verdict : decide arguments = true <;> simp [ofDecision, verdict]

/-- The store answers the complement exactly where the procedure says no. -/
theorem ofDecision_answers_complement_iff (complementNotEq : complement ≠ "eq") (distinct : complement ≠ relation)
    {arguments : List Pattern} (first : ∀ argument ∈ arguments, FirstOrder argument) :
    Answers (ofDecision relation complement decide) language complement arguments ↔ decide arguments = false := by
  rw [answers_iff first, builtinRelationTuples_eq_nil complementNotEq]
  by_cases verdict : decide arguments = true <;> simp [ofDecision, verdict, distinct]

/-- **A decision procedure is a certified store**: on first-order arguments it decides its relation, with its
complement. -/
theorem ofDecision_complemented (notEq : relation ≠ "eq") (complementNotEq : complement ≠ "eq")
    (distinct : complement ≠ relation) :
    Complemented (Answers (ofDecision relation complement decide) language relation)
      (Answers (ofDecision relation complement decide) language complement)
      (fun arguments => ∀ argument ∈ arguments, FirstOrder argument) where
  disjoint arguments first held failed := by
    rw [ofDecision_answers_iff notEq first] at held
    rw [ofDecision_answers_complement_iff complementNotEq distinct first] at failed
    simp [held] at failed
  exhaustive arguments first := by
    cases verdict : decide arguments
    · exact .inr ((ofDecision_answers_complement_iff complementNotEq distinct first).mpr verdict)
    · exact .inl ((ofDecision_answers_iff notEq first).mpr verdict)

/-! ## Closed fact stores -/

/-- **A closed fact store**: finitely many ground tuples, and no others. -/
def factStore (relation complement : String) (stored : List (List Pattern)) : RelationEnv :=
  ofDecision relation complement fun arguments => stored.contains arguments

/-- The relation holds of exactly the stored tuples. -/
theorem factStore_answers_iff (notEq : relation ≠ "eq") {stored : List (List Pattern)} {arguments : List Pattern}
    (first : ∀ argument ∈ arguments, FirstOrder argument) :
    Answers (factStore relation complement stored) language relation arguments ↔ arguments ∈ stored := by
  rw [factStore, ofDecision_answers_iff notEq first, List.contains_iff_mem]

/-- **The closed world of the store**: the complement holds of every first-order tuple not stored. -/
theorem factStore_answers_complement_iff (complementNotEq : complement ≠ "eq") (distinct : complement ≠ relation)
    {stored : List (List Pattern)} {arguments : List Pattern} (first : ∀ argument ∈ arguments, FirstOrder argument) :
    Answers (factStore relation complement stored) language complement arguments ↔ arguments ∉ stored := by
  rw [factStore, ofDecision_answers_complement_iff complementNotEq distinct first]
  simp

end Mettapedia.GSLT.LanguageDef.DecidableRelations
