import Mettapedia.GSLT.Compilation.Uniform.TypingClauses
import Mettapedia.GSLT.Compilation.Uniform.CollectionMatching
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# The laws of collections, as clauses

A presentation derives laws from its collection carriers and from its collection algebras (`DerivedInstance`): bags
and sets are unordered, sets drop duplicates, and an algebra flattens nested collections, reads a singleton as its
element and absorbs its unit. Each law is compiled to clauses that derive exactly its instances, in both directions
(`derives_law_iff`). The typing clauses decide the collection type or the sort that each law asks of its terms.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.CollectionLaws

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode collectionCode_injective)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines (unknowns)
open RuleSyntax.ComputedConditions (Relations)
open RootRewritesOnTheStep (symTerm appTerm encode encodeList labelCode optionRow encode_injective)
open DemandTransformation (Goal Clause Moded goalHolds goalInputs goalUnknowns DerivesAt Derives derives_of_clause pick
  moded_of_inputsBound InputsBound)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType ElementsHaveType CollectionTypedAt CollectionTypeOccurs
  FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance SortedAt AlgebraRule)
open OrderedMatching (isData isDataList isDataList_iff)
open CollectionMatching (pickRelation pickClauses pick_sound pick_complete)
open TypingClauses (typedRelation typeRowTerm typeCodes TypedProgram typed_iff)
open PatternRows (encodeList_nil_inv encodeList_cons_inv encode_closed_inv)
open UnificationClauses (unit)

/-! ## Rows of collections and of constants -/

/-- The row pattern of a collection of a kind with no rest, from the row pattern of its elements. -/
def closedTerm (kind : CollType) (elements : Tm) : Tm :=
  appTerm (symTerm 6) (appTerm (symTerm (collectionCode kind)) (appTerm elements (symTerm 0)))

/-- The row pattern of a constructor applied to no arguments. -/
def constantTerm (label : String) : Tm := appTerm (symTerm 2) (appTerm (symTerm (labelCode label)) (symTerm 0))

@[simp] theorem inst_closedTerm (θ : ℕ → Expr) (kind : CollType) (elements : Tm) :
    inst θ (closedTerm kind elements) =
      .app (.sym 6) (.app (.sym (collectionCode kind)) (.app (inst θ elements) (.sym 0))) := by
  simp [closedTerm]

@[simp] theorem inst_constantTerm (θ : ℕ → Expr) (label : String) :
    inst θ (constantTerm label) = encode (.apply label []) := by
  simp [constantTerm, encode, encodeList]

@[simp] theorem unknowns_closedTerm (kind : CollType) (elements : Tm) :
    unknowns (closedTerm kind elements) = unknowns elements := by
  simp [closedTerm]

@[simp] theorem unknowns_constantTerm (label : String) : unknowns (constantTerm label) = [] := by
  simp [constantTerm]

theorem encode_closed (kind : CollType) (elements : List Pattern) :
    encode (.collection kind elements none) =
      .app (.sym 6) (.app (.sym (collectionCode kind)) (.app (encodeList elements) (.sym 0))) := rfl

/-! ## Lists: permuting, appending, splitting -/

/-- The relation of the permutations of a list. -/
def permuteRelation : ℕ := 25

/-- The relation of appending two lists. -/
def appendRelation : ℕ := 26

/-- The relation of the splits of a list in two. -/
def splitRelation : ℕ := 27

def permuteNil : Clause := { relation := permuteRelation, input := symTerm 0, output := symTerm 0, body := [] }

def permuteCons : Clause :=
  { relation := permuteRelation, input := .var 0, output := appTerm (.var 1) (.var 3),
    body := [.ask pickRelation (.var 0) (appTerm (.var 1) (.var 2)), .ask permuteRelation (.var 2) (.var 3)] }

def appendNil : Clause :=
  { relation := appendRelation, input := appTerm (symTerm 0) (.var 0), output := .var 0, body := [] }

def appendCons : Clause :=
  { relation := appendRelation, input := appTerm (appTerm (.var 0) (.var 1)) (.var 2),
    output := appTerm (.var 0) (.var 3), body := [.ask appendRelation (appTerm (.var 1) (.var 2)) (.var 3)] }

def splitHere : Clause :=
  { relation := splitRelation, input := .var 0, output := appTerm (symTerm 0) (.var 0), body := [] }

def splitLater : Clause :=
  { relation := splitRelation, input := appTerm (.var 0) (.var 1),
    output := appTerm (appTerm (.var 0) (.var 2)) (.var 3),
    body := [.ask splitRelation (.var 1) (appTerm (.var 2) (.var 3))] }

/-- The clauses of lists. -/
def listClauses : List Clause := [permuteNil, permuteCons, appendNil, appendCons, splitHere, splitLater]

theorem listClauses_moded : ∀ c ∈ listClauses, Moded c := by
  intro c inside
  simp only [listClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl <;> exact DemandTransformation.moded_of_check (by decide)

theorem listClauses_relation {c : Clause} (inside : c ∈ listClauses) :
    permuteRelation ≤ c.relation ∧ c.relation ≤ splitRelation := by
  simp only [listClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section Lists

variable {R : Relations} {program : List Clause}

theorem listClause_of (only : ∀ c ∈ program, permuteRelation ≤ c.relation → c.relation ≤ splitRelation →
      c ∈ listClauses)
    {c : Clause} (member : c ∈ program) {r : ℕ} (isR : c.relation = r) (low : permuteRelation ≤ r)
    (high : r ≤ splitRelation) : c ∈ listClauses :=
  only c member (isR ▸ low) (isR ▸ high)

/-- **A derived permutation of a list is a permutation of it.** -/
theorem permute_sound
    (only : ∀ c ∈ program, permuteRelation ≤ c.relation → c.relation ≤ splitRelation → c ∈ listClauses)
    (onlyPicks : ∀ c ∈ program, c.relation = pickRelation → c ∈ pickClauses) :
    ∀ (depth : ℕ) (xs : List Pattern) (w : Expr), DerivesAt R program depth permuteRelation (encodeList xs) w →
      ∃ ys, w = encodeList ys ∧ xs.Perm ys
  | 0, _, _, derived => derived.elim
  | depth + 1, xs, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := listClause_of only member isR (le_refl _) (by decide)
      simp only [listClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [permuteNil, RootRewritesOnTheStep.inst_symTerm] at input output
        rw [encodeList_nil_inv input, ← output]
        exact ⟨[], rfl, .nil⟩
      · simp only [permuteCons, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at input output
        have picked := goals _ List.mem_cons_self
        have rest := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, input] at picked rest
        obtain ⟨i, bound, pickedIs⟩ := pick_sound onlyPicks depth picked
        simp only [Expr.app.injEq] at pickedIs
        rw [pickedIs.2] at rest
        obtain ⟨ys, ysIs, perm⟩ := permute_sound only onlyPicks depth _ _ rest
        refine ⟨xs[i] :: ys, ?_, ?_⟩
        · rw [← output, pickedIs.1, ysIs]
          rfl
        · exact (List.getElem_cons_eraseIdx_perm bound).symm.trans (perm.cons _)

/-- **A derived append of two lists is their append.** -/
theorem append_sound
    (only : ∀ c ∈ program, permuteRelation ≤ c.relation → c.relation ≤ splitRelation → c ∈ listClauses) :
    ∀ (depth : ℕ) (xs ys : List Pattern) (w : Expr),
      DerivesAt R program depth appendRelation (.app (encodeList xs) (encodeList ys)) w → w = encodeList (xs ++ ys)
  | 0, _, _, _, derived => derived.elim
  | depth + 1, xs, ys, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := listClause_of only member isR (by decide) (by decide)
      simp only [listClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [appendNil, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨xsIs, ysIs⟩ := input
        rw [encodeList_nil_inv xsIs, ← output, ysIs]
        rfl
      · simp only [appendCons, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input output
        obtain ⟨xsIs, ysIs⟩ := input
        obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv xsIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, restIs,
          ysIs] at asked
        rw [← output, xIs, append_sound only depth rest ys _ asked]
        rfl

/-- **A derived split of a list is two lists that append to it.** -/
theorem split_sound
    (only : ∀ c ∈ program, permuteRelation ≤ c.relation → c.relation ≤ splitRelation → c ∈ listClauses) :
    ∀ (depth : ℕ) (xs : List Pattern) (w : Expr), DerivesAt R program depth splitRelation (encodeList xs) w →
      ∃ before after, xs = before ++ after ∧ w = .app (encodeList before) (encodeList after)
  | 0, _, _, derived => derived.elim
  | depth + 1, xs, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := listClause_of only member isR (by decide) (le_refl _)
      simp only [listClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [splitHere, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown] at input output
        exact ⟨[], xs, rfl, by rw [← output, input]; rfl⟩
      · simp only [splitLater, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at input output
        obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv input
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, restIs] at asked
        obtain ⟨before, after, rfl, answered⟩ := split_sound only depth rest _ asked
        simp only [Expr.app.injEq] at answered
        exact ⟨x :: before, after, rfl, by rw [← output, xIs, answered.1, answered.2]; rfl⟩

/-- **Every permutation of a list is derived.** -/
theorem permute_complete (included : ∀ c ∈ listClauses, c ∈ program) (picks : ∀ c ∈ pickClauses, c ∈ program) :
    ∀ (ys xs : List Pattern), xs.Perm ys → Derives R program permuteRelation (encodeList xs) (encodeList ys)
  | [], xs, perm => by
      rw [perm.eq_nil]
      have clause := derives_of_clause (R := R) (included permuteNil (by simp [listClauses])) (pick [])
        (fun _ inside => absurd inside List.not_mem_nil)
      simpa [permuteNil, encodeList] using clause
  | y :: ys, xs, perm => by
      obtain ⟨i, bound, rfl⟩ := List.getElem_of_mem (perm.symm.subset List.mem_cons_self)
      have rest : (xs.eraseIdx i).Perm ys := ((List.getElem_cons_eraseIdx_perm bound).trans perm).cons_inv
      have inner := permute_complete included picks ys (xs.eraseIdx i) rest
      have picked := pick_complete (R := R) picks xs i bound
      have clause := derives_of_clause (R := R) (included permuteCons (by simp [listClauses]))
        (pick [encodeList xs, encode xs[i], encodeList (xs.eraseIdx i), encodeList ys]) (fun g inside => by
          simp only [permuteCons, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · simpa [goalHolds, pick] using picked
          · simpa [goalHolds, pick] using inner)
      simpa [permuteCons, pick, encodeList] using clause

/-- **The append of two lists is derived.** -/
theorem append_complete (included : ∀ c ∈ listClauses, c ∈ program) :
    ∀ (xs ys : List Pattern),
      Derives R program appendRelation (.app (encodeList xs) (encodeList ys)) (encodeList (xs ++ ys))
  | [], ys => by
      have clause := derives_of_clause (R := R) (included appendNil (by simp [listClauses])) (pick [encodeList ys])
        (fun _ inside => absurd inside List.not_mem_nil)
      simpa [appendNil, pick, encodeList] using clause
  | x :: xs, ys => by
      have inner := append_complete included xs ys
      have clause := derives_of_clause (R := R) (included appendCons (by simp [listClauses]))
        (pick [encode x, encodeList xs, encodeList ys, encodeList (xs ++ ys)]) (fun g inside => by
          simp only [appendCons, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, pick] using inner)
      simpa [appendCons, pick, encodeList] using clause

/-- **Every split of a list in two is derived.** -/
theorem split_complete (included : ∀ c ∈ listClauses, c ∈ program) :
    ∀ (before after : List Pattern),
      Derives R program splitRelation (encodeList (before ++ after)) (.app (encodeList before) (encodeList after))
  | [], after => by
      have clause := derives_of_clause (R := R) (included splitHere (by simp [listClauses]))
        (pick [encodeList after]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [splitHere, pick, encodeList] using clause
  | x :: before, after => by
      have inner := split_complete included before after
      have clause := derives_of_clause (R := R) (included splitLater (by simp [listClauses]))
        (pick [encode x, encodeList (before ++ after), encodeList before, encodeList after]) (fun g inside => by
          simp only [splitLater, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, pick] using inner)
      simpa [splitLater, pick, encodeList] using clause

end Lists

/-! ## The collection types of a language -/

/-- The collection types at positions in a type: each one's kind and element type. -/
def collectionTypes : TypeExpr → List (CollType × TypeExpr)
  | .base _ => []
  | .arrow domain codomain => collectionTypes domain ++ collectionTypes codomain
  | .multiBinder body => collectionTypes body
  | .collection kind element => (kind, element) :: collectionTypes element

theorem mem_collectionTypes {kind : CollType} {element : TypeExpr} :
    ∀ {type : TypeExpr}, (kind, element) ∈ collectionTypes type ↔ CollectionTypeOccurs kind element type
  | .base _ => by
      simp only [collectionTypes, List.not_mem_nil, false_iff]
      intro occurs
      cases occurs
  | .arrow domain codomain => by
      rw [collectionTypes, List.mem_append, mem_collectionTypes (type := domain),
        mem_collectionTypes (type := codomain)]
      constructor
      · rintro (inside | inside)
        · exact .domain inside
        · exact .codomain inside
      · intro occurs
        cases occurs with
        | domain inside => exact .inl inside
        | codomain inside => exact .inr inside
  | .multiBinder body => by
      rw [collectionTypes, mem_collectionTypes (type := body)]
      constructor
      · exact .binder
      · intro occurs
        cases occurs with
        | binder inside => exact inside
  | .collection kind' element' => by
      rw [collectionTypes, List.mem_cons, mem_collectionTypes (type := element'), Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | inside)
        · exact .here
        · exact .element inside
      · intro occurs
        cases occurs with
        | here => exact .inl ⟨rfl, rfl⟩
        | element inside => exact .inr inside

/-- The collection types found in the parameters of a language's constructors. -/
def languageCollectionTypes (language : LanguageDef) : List (CollType × TypeExpr) :=
  language.terms.flatMap fun rule => rule.params.flatMap fun parameter => collectionTypes parameter.typeExpr

theorem mem_languageCollectionTypes {language : LanguageDef} {kind : CollType} {element : TypeExpr} :
    (kind, element) ∈ languageCollectionTypes language ↔
      ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params, CollectionTypeOccurs kind element parameter.typeExpr := by
  simp only [languageCollectionTypes, List.mem_flatMap, mem_collectionTypes]

theorem elementsHaveType_iff {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {element : TypeExpr} : ∀ {elements : List Pattern},
      ElementsHaveType language free bound elements element ↔ ∀ x ∈ elements, HasType language free bound x element
  | [] => ⟨fun _ _ inside => absurd inside List.not_mem_nil, fun _ => .nil _ _⟩
  | x :: xs => by
      constructor
      · intro typed
        cases typed with
        | cons head tail =>
            intro y inside
            rcases List.mem_cons.mp inside with rfl | later
            · exact head
            · exact elementsHaveType_iff.mp tail y later
      · intro all
        exact .cons (all x List.mem_cons_self)
          (elementsHaveType_iff.mpr fun y inside => all y (List.mem_cons_of_mem _ inside))

/-- **A collection type of a list is one of its permutations.** -/
theorem collectionTypedAt_perm {language : LanguageDef} {rule : GrammarRule} {kind : CollType}
    {elements elements' : List Pattern} (typed : CollectionTypedAt language rule kind elements)
    (perm : elements.Perm elements') : CollectionTypedAt language rule kind elements' := by
  obtain ⟨parameter, member, element, occurs, free, bound, hasType⟩ := typed
  refine ⟨parameter, member, element, occurs, free, bound, ?_⟩
  cases hasType with
  | collection elementsTyped =>
      exact .collection (elementsHaveType_iff.mpr fun x inside =>
        elementsHaveType_iff.mp elementsTyped x (perm.mem_iff.mpr inside))

/-- **The laws relate data to data only.** -/
theorem derivedInstance_data {language : LanguageDef} {s t : Pattern} (derived : DerivedInstance language s t) :
    isData s = true ↔ isData t = true := by
  cases derived with
  | bagPerm _ _ perm =>
      simp only [isData, Option.isNone_none, Bool.true_and, isDataList_iff]
      exact ⟨fun all x inside => all x (perm.mem_iff.mpr inside), fun all x inside => all x (perm.mem_iff.mp inside)⟩
  | setPerm _ _ perm =>
      simp only [isData, Option.isNone_none, Bool.true_and, isDataList_iff]
      exact ⟨fun all x inside => all x (perm.mem_iff.mpr inside), fun all x inside => all x (perm.mem_iff.mp inside)⟩
  | setDedup _ _ => simp [isData, isDataList]
  | flatten _ _ _ =>
      simp only [isData, Option.isNone_none, Bool.true_and, isDataList_iff, List.mem_append, List.mem_cons]
      constructor
      · intro all x inside
        rcases inside with (before | nested) | after
        · exact all x (.inl before)
        · exact (isDataList_iff.mp (by simpa [isData] using all _ (.inr (.inl rfl)))) x nested
        · exact all x (.inr (.inr after))
      · intro all x inside
        rcases inside with before | rfl | after
        · exact all x (.inl (.inl before))
        · simpa [isData, isDataList_iff] using fun y inside => all y (.inl (.inr inside))
        · exact all x (.inr after)
  | singleton _ _ _ => simp [isData, isDataList]
  | unitElim _ _ _ =>
      simp only [isData, Option.isNone_none, Bool.true_and, isDataList_iff, List.mem_append, List.mem_cons]
      constructor
      · intro all x inside
        rcases inside with before | after
        · exact all x (.inl before)
        · exact all x (.inr (.inr after))
      · intro all x inside
        rcases inside with before | rfl | after
        · exact all x (.inl before)
        · simp [isData, isDataList]
        · exact all x (.inr after)
  | emptyUnit _ _ _ => simp [isData, isDataList]

/-! ## Lawful algebras -/

/-- Whether the unit of an algebra, when it has one, is a constructor of the rule's category with no parameters. -/
def unitDeclared (language : LanguageDef) (rule : GrammarRule) (algebra : CollectionAlgebra) : Bool :=
  match algebra.unit with
  | none => true
  | some label => language.terms.any fun unitRule =>
      unitRule.label == label && unitRule.category == rule.category && unitRule.params.isEmpty

theorem unitDeclared_iff {language : LanguageDef} {rule : GrammarRule} {algebra : CollectionAlgebra} :
    unitDeclared language rule algebra = true ↔ ∀ unit, algebra.unit = some unit →
      ∃ unitRule ∈ language.terms, unitRule.label = unit ∧ unitRule.category = rule.category ∧
        unitRule.params = [] := by
  rcases algebra with ⟨flatten, unit⟩
  cases unit <;> simp [unitDeclared, List.any_eq_true, and_assoc]

/-- **The kind and the algebra of a rule whose algebra is lawful**: its single parameter is a collection of its own
category, and its unit, when it has one, is a constructor of that category with no parameters. -/
def algebraOf? (language : LanguageDef) (rule : GrammarRule) : Option (CollType × CollectionAlgebra) :=
  rule.algebra?.bind fun algebra =>
    match rule.params with
    | [.simple _ (.collection kind (.base category))] =>
        if category = rule.category ∧ unitDeclared language rule algebra = true then some (kind, algebra) else none
    | _ => none

theorem algebraOf?_iff {language : LanguageDef} {rule : GrammarRule} (member : rule ∈ language.terms)
    {kind : CollType} {algebra : CollectionAlgebra} :
    algebraOf? language rule = some (kind, algebra) ↔ AlgebraRule language rule kind algebra := by
  constructor
  · intro found
    simp only [algebraOf?, Option.bind_eq_some_iff] at found
    obtain ⟨algebra', declared, rest⟩ := found
    revert rest
    split
    · rename_i parameterName kind' category params
      intro rest
      split at rest
      · rename_i lawful
        simp only [Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        obtain ⟨rfl, unitOk⟩ := lawful
        exact ⟨member, declared, ⟨parameterName, params⟩, unitDeclared_iff.mp unitOk⟩
      · cases rest
    · intro rest
      cases rest
  · intro algebraRule
    obtain ⟨-, declared, ⟨parameterName, params⟩, unitOk⟩ := algebraRule
    simp [algebraOf?, declared, params, unitDeclared_iff.mpr unitOk]

/-! ## The clauses of the laws -/

/-- The relation of one instance of a law, in either direction. -/
def lawRelation : ℕ := 23

/-- The relation of the guard of the laws of bags and sets. -/
def guardRelation : ℕ := 24

/-- **The guard of a collection type**: a collection with no rest has the collection type. -/
def guardClause (kind : CollType) (element : TypeExpr) : Clause :=
  { relation := guardRelation, input := closedTerm kind (.var 0), output := unit,
    body := [.ask typedRelation (appTerm (closedTerm kind (.var 0)) (typeRowTerm (.collection kind element))) unit] }

/-- The guards of a language: one for each collection type found in its parameters. -/
def guardClauses (language : LanguageDef) : List Clause :=
  (languageCollectionTypes language).map fun pair => guardClause pair.1 pair.2

/-- The goal that a collection of a kind is sorted at a category. -/
def sortedGoal (kind : CollType) (elements : Tm) (category : String) : Goal :=
  .ask typedRelation (appTerm (closedTerm kind elements) (typeRowTerm (.base category))) unit

/-- The goal that a collection of a kind has a collection type found in the parameters. -/
def guardGoal (kind : CollType) (elements : Tm) : Goal := .ask guardRelation (closedTerm kind elements) unit

/-- **Bags and sets are unordered**: a collection is related to every permutation of its elements. -/
def permuteLaw (kind : CollType) : Clause :=
  { relation := lawRelation, input := closedTerm kind (.var 0), output := closedTerm kind (.var 1),
    body := [guardGoal kind (.var 0), .ask permuteRelation (.var 0) (.var 1)] }

/-- **Sets drop duplicates**: a repeated first element is dropped. -/
def dedupForward : Clause :=
  { relation := lawRelation, input := closedTerm .hashSet (appTerm (.var 0) (appTerm (.var 0) (.var 1))),
    output := closedTerm .hashSet (appTerm (.var 0) (.var 1)),
    body := [guardGoal .hashSet (appTerm (.var 0) (appTerm (.var 0) (.var 1)))] }

/-- Dropping a duplicate read backwards: the first element is repeated. -/
def dedupBackward : Clause :=
  { relation := lawRelation, input := closedTerm .hashSet (appTerm (.var 0) (.var 1)),
    output := closedTerm .hashSet (appTerm (.var 0) (appTerm (.var 0) (.var 1))),
    body := [guardGoal .hashSet (appTerm (.var 0) (appTerm (.var 0) (.var 1)))] }

/-- The laws of bags and sets. -/
def kindLaws : List Clause := [permuteLaw .hashBag, permuteLaw .hashSet, dedupForward, dedupBackward]

/-- **An algebra that flattens** puts the elements of a nested collection of its kind in its place. -/
def flattenForward (kind : CollType) (category : String) : Clause :=
  { relation := lawRelation, input := closedTerm kind (.var 0), output := closedTerm kind (.var 5),
    body := [sortedGoal kind (.var 0) category,
      .ask splitRelation (.var 0) (appTerm (.var 1) (appTerm (closedTerm kind (.var 2)) (.var 3))),
      .ask appendRelation (appTerm (.var 2) (.var 3)) (.var 4),
      .ask appendRelation (appTerm (.var 1) (.var 4)) (.var 5)] }

/-- Flattening read backwards: some consecutive elements are nested in a collection of the kind. -/
def flattenBackward (kind : CollType) (category : String) : Clause :=
  { relation := lawRelation, input := closedTerm kind (.var 0), output := closedTerm kind (.var 5),
    body := [.ask splitRelation (.var 0) (appTerm (.var 1) (.var 2)),
      .ask splitRelation (.var 2) (appTerm (.var 3) (.var 4)),
      .ask appendRelation (appTerm (.var 1) (appTerm (closedTerm kind (.var 3)) (.var 4))) (.var 5),
      sortedGoal kind (.var 5) category] }

/-- **An algebra that flattens reads a singleton as its element.** -/
def singletonForward (kind : CollType) (category : String) : Clause :=
  { relation := lawRelation, input := closedTerm kind (appTerm (.var 0) (symTerm 0)), output := .var 0,
    body := [sortedGoal kind (appTerm (.var 0) (symTerm 0)) category] }

/-- A singleton read backwards: a term is its own singleton. -/
def singletonBackward (kind : CollType) (category : String) : Clause :=
  { relation := lawRelation, input := .var 0, output := closedTerm kind (appTerm (.var 0) (symTerm 0)),
    body := [sortedGoal kind (appTerm (.var 0) (symTerm 0)) category] }

/-- **The unit of an algebra is absorbed** where it stands among the elements. -/
def unitElimForward (kind : CollType) (category label : String) : Clause :=
  { relation := lawRelation, input := closedTerm kind (.var 0), output := closedTerm kind (.var 3),
    body := [sortedGoal kind (.var 0) category,
      .ask splitRelation (.var 0) (appTerm (.var 1) (appTerm (constantTerm label) (.var 2))),
      .ask appendRelation (appTerm (.var 1) (.var 2)) (.var 3)] }

/-- Absorbing read backwards: the unit is put among the elements. -/
def unitElimBackward (kind : CollType) (category label : String) : Clause :=
  { relation := lawRelation, input := closedTerm kind (.var 0), output := closedTerm kind (.var 3),
    body := [.ask splitRelation (.var 0) (appTerm (.var 1) (.var 2)),
      .ask appendRelation (appTerm (.var 1) (appTerm (constantTerm label) (.var 2))) (.var 3),
      sortedGoal kind (.var 3) category] }

/-- **The empty collection of an algebra with a unit is the unit.** -/
def emptyUnitForward (kind : CollType) (category label : String) : Clause :=
  { relation := lawRelation, input := closedTerm kind (symTerm 0), output := constantTerm label,
    body := [sortedGoal kind (symTerm 0) category] }

/-- The unit is the empty collection. -/
def emptyUnitBackward (kind : CollType) (category label : String) : Clause :=
  { relation := lawRelation, input := constantTerm label, output := closedTerm kind (symTerm 0),
    body := [sortedGoal kind (symTerm 0) category] }

/-- The laws of an algebra of a kind at a category. -/
def algebraLaws (kind : CollType) (category : String) (algebra : CollectionAlgebra) : List Clause :=
  (if algebra.flatten then
    [flattenForward kind category, flattenBackward kind category, singletonForward kind category,
      singletonBackward kind category] else []) ++
  match algebra.unit with
  | some label => [unitElimForward kind category label, unitElimBackward kind category label,
      emptyUnitForward kind category label, emptyUnitBackward kind category label]
  | none => []

/-- **The clauses of the laws of a language**: those of bags and sets, and those of each lawful algebra. -/
def lawClauses (language : LanguageDef) : List Clause :=
  kindLaws ++ language.terms.flatMap fun rule =>
    match algebraOf? language rule with
    | some (kind, algebra) => algebraLaws kind rule.category algebra
    | none => []

/-! ## Modes and relations of the clauses -/

theorem guardClause_moded (kind : CollType) (element : TypeExpr) : Moded (guardClause kind element) :=
  moded_of_inputsBound (.cons (by simp [guardClause, goalInputs]) (.nil _)) (by simp [guardClause, unit])

theorem kindLaws_moded : ∀ c ∈ kindLaws, Moded c := by
  intro c inside
  simp only [kindLaws, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl <;> exact DemandTransformation.moded_of_check (by decide)

theorem algebraLaws_moded (kind : CollType) (category : String) (algebra : CollectionAlgebra) :
    ∀ c ∈ algebraLaws kind category algebra, Moded c := by
  intro c inside
  simp only [algebraLaws, List.mem_append] at inside
  rcases inside with inFlatten | inUnit
  · split at inFlatten
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inFlatten
      rcases inFlatten with rfl | rfl | rfl | rfl
      · exact moded_of_inputsBound (.cons (by simp [flattenForward, sortedGoal, goalInputs])
          (.cons (by simp [flattenForward, sortedGoal, goalInputs, goalUnknowns])
          (.cons (by simp [flattenForward, sortedGoal, goalInputs, goalUnknowns])
          (.cons (by simp [flattenForward, sortedGoal, goalInputs, goalUnknowns]) (.nil _)))))
          (by simp [flattenForward, sortedGoal, goalUnknowns])
      · exact moded_of_inputsBound (.cons (by simp [flattenBackward, goalInputs])
          (.cons (by simp [flattenBackward, goalInputs, goalUnknowns])
          (.cons (by simp [flattenBackward, goalInputs, goalUnknowns])
          (.cons (by simp [flattenBackward, sortedGoal, goalInputs, goalUnknowns]) (.nil _)))))
          (by simp [flattenBackward, sortedGoal, goalUnknowns])
      · exact moded_of_inputsBound (.cons (by simp [singletonForward, sortedGoal, goalInputs]) (.nil _))
          (by simp [singletonForward])
      · exact moded_of_inputsBound (.cons (by simp [singletonBackward, sortedGoal, goalInputs]) (.nil _))
          (by simp [singletonBackward])
    · simp at inFlatten
  · split at inUnit
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inUnit
      rcases inUnit with rfl | rfl | rfl | rfl
      · exact moded_of_inputsBound (.cons (by simp [unitElimForward, sortedGoal, goalInputs])
          (.cons (by simp [unitElimForward, sortedGoal, goalInputs, goalUnknowns])
          (.cons (by simp [unitElimForward, sortedGoal, goalInputs, goalUnknowns]) (.nil _))))
          (by simp [unitElimForward, sortedGoal, goalUnknowns])
      · exact moded_of_inputsBound (.cons (by simp [unitElimBackward, goalInputs])
          (.cons (by simp [unitElimBackward, goalInputs, goalUnknowns])
          (.cons (by simp [unitElimBackward, sortedGoal, goalInputs, goalUnknowns]) (.nil _))))
          (by simp [unitElimBackward, goalUnknowns])
      · exact moded_of_inputsBound (.cons (by simp [emptyUnitForward, sortedGoal, goalInputs]) (.nil _))
          (by simp [emptyUnitForward])
      · exact moded_of_inputsBound (.cons (by simp [emptyUnitBackward, sortedGoal, goalInputs]) (.nil _))
          (by simp [emptyUnitBackward])
    · simp at inUnit

theorem lawClauses_moded (language : LanguageDef) : ∀ c ∈ lawClauses language, Moded c := by
  intro c inside
  simp only [lawClauses, List.mem_append, List.mem_flatMap] at inside
  rcases inside with inKind | ⟨rule, -, inAlgebra⟩
  · exact kindLaws_moded c inKind
  · cases found : algebraOf? language rule with
    | none => simp [found] at inAlgebra
    | some pair =>
        obtain ⟨kind, algebra⟩ := pair
        simp only [found] at inAlgebra
        exact algebraLaws_moded kind rule.category algebra c inAlgebra

theorem guardClauses_moded (language : LanguageDef) : ∀ c ∈ guardClauses language, Moded c := by
  intro c inside
  obtain ⟨pair, -, rfl⟩ := List.mem_map.mp inside
  exact guardClause_moded pair.1 pair.2

theorem lawClauses_relation {language : LanguageDef} {c : Clause} (inside : c ∈ lawClauses language) :
    c.relation = lawRelation := by
  simp only [lawClauses, List.mem_append, List.mem_flatMap] at inside
  rcases inside with inKind | ⟨rule, -, inAlgebra⟩
  · simp only [kindLaws, List.mem_cons, List.not_mem_nil, or_false] at inKind
    rcases inKind with rfl | rfl | rfl | rfl <;> rfl
  · cases found : algebraOf? language rule with
    | none => simp [found] at inAlgebra
    | some pair =>
        obtain ⟨kind, algebra⟩ := pair
        simp only [found, algebraLaws, List.mem_append] at inAlgebra
        rcases inAlgebra with inFlatten | inUnit
        · split at inFlatten
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at inFlatten
            rcases inFlatten with rfl | rfl | rfl | rfl <;> rfl
          · simp at inFlatten
        · split at inUnit
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at inUnit
            rcases inUnit with rfl | rfl | rfl | rfl <;> rfl
          · simp at inUnit

theorem guardClauses_relation {language : LanguageDef} {c : Clause} (inside : c ∈ guardClauses language) :
    c.relation = guardRelation := by
  obtain ⟨pair, -, rfl⟩ := List.mem_map.mp inside
  rfl

/-! ## A program with the laws -/

/-- **A program with the clauses of the laws of a language**, and of typing, lists and picking. -/
structure LawProgram (language : LanguageDef) (R : Relations) (program : List Clause) : Prop where
  typed : TypedProgram language R program
  picks : ∀ c ∈ pickClauses, c ∈ program
  onlyPicks : ∀ c ∈ program, c.relation = pickRelation → c ∈ pickClauses
  lists : ∀ c ∈ listClauses, c ∈ program
  onlyLists : ∀ c ∈ program, permuteRelation ≤ c.relation → c.relation ≤ splitRelation → c ∈ listClauses
  guards : ∀ c ∈ guardClauses language, c ∈ program
  onlyGuards : ∀ c ∈ program, c.relation = guardRelation → c ∈ guardClauses language
  laws : ∀ c ∈ lawClauses language, c ∈ program
  onlyLaws : ∀ c ∈ program, c.relation = lawRelation → c ∈ lawClauses language

section Laws

variable {language : LanguageDef} {R : Relations} {program : List Clause}

/-- **The guard derives exactly the collections whose collection type is found in a parameter.** -/
theorem guard_iff (laws : LawProgram language R program) (kind : CollType) (elements : List Pattern) :
    Derives R program guardRelation (encode (.collection kind elements none)) (.sym 0) ↔
      ∃ rule ∈ language.terms, CollectionTypedAt language rule kind elements := by
  constructor
  · rintro ⟨depth, derived⟩
    cases depth with
    | zero => exact derived.elim
    | succ depth =>
        obtain ⟨c, member, isGuard, θ, input, -, goals⟩ := derived
        obtain ⟨⟨kind', element⟩, found, rfl⟩ := List.mem_map.mp (laws.onlyGuards c member isGuard)
        simp only [guardClause, inst_closedTerm, DemandTransformation.inst_unknown] at input
        obtain ⟨elements', same, elementsIs⟩ := encode_closed_inv input
        simp only [Pattern.collection.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, inst_closedTerm, DemandTransformation.inst_unknown,
          TypingClauses.inst_typeRowTerm, unit, RootRewritesOnTheStep.inst_symTerm, elementsIs] at asked
        rw [← encode_closed] at asked
        obtain ⟨free, bound, typed⟩ := (typed_iff laws.typed _ _).mp ⟨depth, asked⟩
        obtain ⟨rule, ruleIn, parameter, parameterIn, occurs⟩ := mem_languageCollectionTypes.mp found
        exact ⟨rule, ruleIn, parameter, parameterIn, element, occurs, free, bound, typed⟩
  · rintro ⟨rule, ruleIn, parameter, parameterIn, element, occurs, free, bound, typed⟩
    have found : (kind, element) ∈ languageCollectionTypes language :=
      mem_languageCollectionTypes.mpr ⟨rule, ruleIn, parameter, parameterIn, occurs⟩
    have typedDerived := (typed_iff laws.typed (.collection kind elements none) (.collection kind element)).mpr
      ⟨free, bound, typed⟩
    have clause := derives_of_clause (R := R) (laws.guards (guardClause kind element) (List.mem_map.mpr ⟨_, found, rfl⟩))
      (pick [encodeList elements]) (fun g inside => by
        simp only [guardClause, List.mem_cons, List.not_mem_nil, or_false] at inside
        subst inside
        simpa [goalHolds, pick, unit, encode_closed] using typedDerived)
    simpa [guardClause, pick, unit, encode_closed] using clause

theorem sorted_of_goal (laws : LawProgram language R program) {depth : ℕ} {θ : ℕ → Expr} {kind : CollType}
    {elements : Tm} {category : String} {xs : List Pattern}
    (holds : goalHolds R (DerivesAt R program depth) θ (sortedGoal kind elements category))
    (elementsIs : inst θ elements = encodeList xs) :
    SortedAt language (.collection kind xs none) category := by
  simp only [sortedGoal, goalHolds, RootRewritesOnTheStep.inst_appTerm, inst_closedTerm,
    TypingClauses.inst_typeRowTerm, unit, RootRewritesOnTheStep.inst_symTerm, elementsIs] at holds
  rw [← encode_closed] at holds
  exact (typed_iff laws.typed _ _).mp ⟨depth, holds⟩

theorem goal_of_sorted (laws : LawProgram language R program) {θ : ℕ → Expr} {kind : CollType} {elements : Tm}
    {category : String} {xs : List Pattern} (elementsIs : inst θ elements = encodeList xs)
    (sorted : SortedAt language (.collection kind xs none) category) :
    goalHolds R (Derives R program) θ (sortedGoal kind elements category) := by
  simp only [sortedGoal, goalHolds, RootRewritesOnTheStep.inst_appTerm, inst_closedTerm,
    TypingClauses.inst_typeRowTerm, unit, RootRewritesOnTheStep.inst_symTerm, elementsIs]
  rw [← encode_closed]
  exact (typed_iff laws.typed _ _).mpr sorted

theorem typedAt_of_goal (laws : LawProgram language R program) {depth : ℕ} {θ : ℕ → Expr} {kind : CollType}
    {elements : Tm} {xs : List Pattern}
    (holds : goalHolds R (DerivesAt R program depth) θ (guardGoal kind elements))
    (elementsIs : inst θ elements = encodeList xs) :
    ∃ rule ∈ language.terms, CollectionTypedAt language rule kind xs := by
  simp only [guardGoal, goalHolds, inst_closedTerm, unit, RootRewritesOnTheStep.inst_symTerm, elementsIs] at holds
  rw [← encode_closed] at holds
  exact (guard_iff laws kind xs).mp ⟨depth, holds⟩

theorem goal_of_typedAt (laws : LawProgram language R program) {θ : ℕ → Expr} {kind : CollType} {elements : Tm}
    {xs : List Pattern} (elementsIs : inst θ elements = encodeList xs)
    (typed : ∃ rule ∈ language.terms, CollectionTypedAt language rule kind xs) :
    goalHolds R (Derives R program) θ (guardGoal kind elements) := by
  simp only [guardGoal, goalHolds, inst_closedTerm, unit, RootRewritesOnTheStep.inst_symTerm, elementsIs]
  rw [← encode_closed]
  exact (guard_iff laws kind xs).mpr typed

/-- **What the law clauses derive from a term is an instance of a law, in one direction or the other.** -/
theorem law_sound (laws : LawProgram language R program) {s : Pattern} {w : Expr} :
    ∀ {depth : ℕ}, DerivesAt R program depth lawRelation (encode s) w →
      ∃ t, w = encode t ∧ (DerivedInstance language s t ∨ DerivedInstance language t s)
  | 0, derived => derived.elim
  | depth + 1, derived => by
    obtain ⟨c, member, isLaw, θ, input, output, goals⟩ := derived
    have inLaws := laws.onlyLaws c member isLaw
    simp only [lawClauses, List.mem_append, List.mem_flatMap] at inLaws
    rcases inLaws with inKind | ⟨rule, ruleIn, inAlgebra⟩
    · simp only [kindLaws, List.mem_cons, List.not_mem_nil, or_false] at inKind
      rcases inKind with rfl | rfl | rfl | rfl
      · simp only [permuteLaw, inst_closedTerm, DemandTransformation.inst_unknown] at input output
        obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
        obtain ⟨rule, ruleIn, typed⟩ := typedAt_of_goal laws (goals _ List.mem_cons_self) elementsIs
        have asked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, DemandTransformation.inst_unknown, elementsIs] at asked
        obtain ⟨ys, ysIs, perm⟩ := permute_sound laws.onlyLists laws.onlyPicks depth elements _ asked
        exact ⟨.collection .hashBag ys none, by rw [← output, ysIs]; rfl, .inl (.bagPerm ruleIn typed perm)⟩
      · simp only [permuteLaw, inst_closedTerm, DemandTransformation.inst_unknown] at input output
        obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
        obtain ⟨rule, ruleIn, typed⟩ := typedAt_of_goal laws (goals _ List.mem_cons_self) elementsIs
        have asked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, DemandTransformation.inst_unknown, elementsIs] at asked
        obtain ⟨ys, ysIs, perm⟩ := permute_sound laws.onlyLists laws.onlyPicks depth elements _ asked
        exact ⟨.collection .hashSet ys none, by rw [← output, ysIs]; rfl, .inl (.setPerm ruleIn typed perm)⟩
      · simp only [dedupForward, inst_closedTerm, RootRewritesOnTheStep.inst_appTerm,
          DemandTransformation.inst_unknown] at input output
        obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
        obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv elementsIs
        obtain ⟨y, rest', rfl, yIs, rest'Is⟩ := encodeList_cons_inv restIs
        obtain rfl := encode_injective (xIs.symm.trans yIs)
        obtain ⟨rule, ruleIn, typed⟩ := typedAt_of_goal laws (xs := x :: x :: rest')
          (goals _ List.mem_cons_self) (by simp [xIs, rest'Is, encodeList])
        exact ⟨.collection .hashSet (x :: rest') none, by rw [← output, xIs, rest'Is]; rfl,
          .inl (.setDedup ruleIn typed)⟩
      · simp only [dedupBackward, inst_closedTerm, RootRewritesOnTheStep.inst_appTerm,
          DemandTransformation.inst_unknown] at input output
        obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
        obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv elementsIs
        obtain ⟨rule, ruleIn, typed⟩ := typedAt_of_goal laws (xs := x :: x :: rest)
          (goals _ List.mem_cons_self) (by simp [xIs, restIs, encodeList])
        exact ⟨.collection .hashSet (x :: x :: rest) none, by rw [← output, xIs, restIs]; rfl,
          .inr (.setDedup ruleIn typed)⟩
    · cases found : algebraOf? language rule with
      | none => simp [found] at inAlgebra
      | some pair =>
        obtain ⟨kind, algebra⟩ := pair
        have algebraRule := (algebraOf?_iff ruleIn).mp found
        simp only [found, algebraLaws, List.mem_append] at inAlgebra
        rcases inAlgebra with inFlatten | inUnit
        · split at inFlatten
          · rename_i flat
            simp only [List.mem_cons, List.not_mem_nil, or_false] at inFlatten
            rcases inFlatten with rfl | rfl | rfl | rfl
            · simp only [flattenForward, inst_closedTerm, DemandTransformation.inst_unknown] at input output
              obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
              have sorted := sorted_of_goal laws (goals _ List.mem_cons_self) elementsIs
              have first := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have second := goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              have third := goals _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, inst_closedTerm,
                DemandTransformation.inst_unknown, elementsIs] at first
              obtain ⟨before, rest, rfl, splitIs⟩ := split_sound laws.onlyLists depth elements _ first
              simp only [Expr.app.injEq] at splitIs
              obtain ⟨beforeIs, restIs⟩ := splitIs
              obtain ⟨nested, after, rfl, nestedIs, afterIs⟩ := encodeList_cons_inv restIs
              obtain ⟨inner, rfl, innerIs⟩ := encode_closed_inv nestedIs
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, innerIs,
                afterIs] at second
              have appended := append_sound laws.onlyLists depth inner after _ second
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, beforeIs,
                appended] at third
              have result := append_sound laws.onlyLists depth before (inner ++ after) _ third
              refine ⟨.collection kind (before ++ inner ++ after) none, ?_, .inl (.flatten algebraRule flat sorted)⟩
              rw [← output, result, List.append_assoc]
              rfl
            · simp only [flattenBackward, inst_closedTerm, DemandTransformation.inst_unknown] at input output
              obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
              have first := goals _ List.mem_cons_self
              have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have third := goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              have fourth := goals _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
                elementsIs] at first
              obtain ⟨before, rest, rfl, firstIs⟩ := split_sound laws.onlyLists depth elements _ first
              simp only [Expr.app.injEq] at firstIs
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
                firstIs.2] at second
              obtain ⟨inner, after, rfl, secondIs⟩ := split_sound laws.onlyLists depth rest _ second
              simp only [Expr.app.injEq] at secondIs
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, inst_closedTerm,
                DemandTransformation.inst_unknown, firstIs.1, secondIs.1, secondIs.2] at third
              rw [← encode_closed, show Expr.app (encode (.collection kind inner none)) (encodeList after) =
                encodeList (.collection kind inner none :: after) from rfl] at third
              have result := append_sound laws.onlyLists depth before _ _ third
              have sorted := sorted_of_goal laws fourth result
              refine ⟨.collection kind (before ++ .collection kind inner none :: after) none, ?_, .inr ?_⟩
              · rw [← output, result]
                rfl
              · have flattened := DerivedInstance.flatten algebraRule flat sorted
                rwa [List.append_assoc] at flattened
            · simp only [singletonForward, inst_closedTerm, RootRewritesOnTheStep.inst_appTerm,
                RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] at input output
              obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
              obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv elementsIs
              obtain rfl := encodeList_nil_inv restIs
              have sorted := sorted_of_goal laws (xs := [x]) (goals _ List.mem_cons_self) (by simp [xIs, encodeList])
              exact ⟨x, by rw [← output, xIs], .inl (.singleton algebraRule flat sorted)⟩
            · simp only [singletonBackward, inst_closedTerm, RootRewritesOnTheStep.inst_appTerm,
                RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] at input output
              have sorted := sorted_of_goal laws (xs := [s]) (goals _ List.mem_cons_self) (by simp [input, encodeList])
              exact ⟨.collection kind [s] none, by rw [← output, input]; rfl, .inr (.singleton algebraRule flat sorted)⟩
          · simp at inFlatten
        · split at inUnit
          · rename_i label unitIs
            simp only [List.mem_cons, List.not_mem_nil, or_false] at inUnit
            rcases inUnit with rfl | rfl | rfl | rfl
            · simp only [unitElimForward, inst_closedTerm, DemandTransformation.inst_unknown] at input output
              obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
              have sorted := sorted_of_goal laws (goals _ List.mem_cons_self) elementsIs
              have first := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have second := goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, inst_constantTerm,
                DemandTransformation.inst_unknown, elementsIs] at first
              obtain ⟨before, rest, rfl, splitIs⟩ := split_sound laws.onlyLists depth elements _ first
              simp only [Expr.app.injEq] at splitIs
              obtain ⟨beforeIs, restIs⟩ := splitIs
              obtain ⟨u, after, rfl, uIs, afterIs⟩ := encodeList_cons_inv restIs
              obtain rfl := encode_injective uIs
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, beforeIs,
                afterIs] at second
              have result := append_sound laws.onlyLists depth before after _ second
              exact ⟨.collection kind (before ++ after) none, by rw [← output, result]; rfl,
                .inl (.unitElim algebraRule unitIs sorted)⟩
            · simp only [unitElimBackward, inst_closedTerm, DemandTransformation.inst_unknown] at input output
              obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
              have first := goals _ List.mem_cons_self
              have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have third := goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
                elementsIs] at first
              obtain ⟨before, after, rfl, splitIs⟩ := split_sound laws.onlyLists depth elements _ first
              simp only [Expr.app.injEq] at splitIs
              simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, inst_constantTerm,
                DemandTransformation.inst_unknown, splitIs.1, splitIs.2] at second
              rw [show Expr.app (encode (.apply label [])) (encodeList after) =
                encodeList (.apply label [] :: after) from rfl] at second
              have result := append_sound laws.onlyLists depth before _ _ second
              have sorted := sorted_of_goal laws third result
              exact ⟨.collection kind (before ++ .apply label [] :: after) none, by rw [← output, result]; rfl,
                .inr (.unitElim algebraRule unitIs sorted)⟩
            · simp only [emptyUnitForward, inst_closedTerm, RootRewritesOnTheStep.inst_symTerm,
                inst_constantTerm] at input output
              obtain ⟨elements, rfl, elementsIs⟩ := encode_closed_inv input
              obtain rfl := encodeList_nil_inv elementsIs
              have sorted := sorted_of_goal laws (xs := []) (goals _ List.mem_cons_self) rfl
              exact ⟨.apply label [], output.symm, .inl (.emptyUnit algebraRule unitIs sorted)⟩
            · simp only [emptyUnitBackward, inst_closedTerm, RootRewritesOnTheStep.inst_symTerm,
                inst_constantTerm] at input output
              obtain rfl := encode_injective input
              have sorted := sorted_of_goal laws (xs := []) (goals _ List.mem_cons_self) rfl
              exact ⟨.collection kind [] none, by rw [← output]; rfl, .inr (.emptyUnit algebraRule unitIs sorted)⟩
          · simp at inUnit

theorem algebra_member {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (algebraRule : AlgebraRule language rule kind algebra) {c : Clause}
    (inside : c ∈ algebraLaws kind rule.category algebra) : c ∈ lawClauses language := by
  have found := (algebraOf?_iff algebraRule.authored).mpr algebraRule
  simp only [lawClauses, List.mem_append, List.mem_flatMap]
  exact .inr ⟨rule, algebraRule.authored, by simpa [found] using inside⟩

/-- **Every instance of a law is derived by the law clauses.** -/
theorem law_forward (laws : LawProgram language R program) {s t : Pattern} (derived : DerivedInstance language s t) :
    Derives R program lawRelation (encode s) (encode t) := by
  cases derived with
  | @bagPerm rule elements elements' ruleIn typed perm =>
      have clause := derives_of_clause (R := R) (laws.laws (permuteLaw .hashBag) (by simp [lawClauses, kindLaws]))
        (pick [encodeList elements, encodeList elements']) (fun g inside => by
          simp only [permuteLaw, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · exact goal_of_typedAt laws rfl ⟨rule, ruleIn, typed⟩
          · simpa [goalHolds, pick] using permute_complete laws.lists laws.picks elements' elements perm)
      simpa [permuteLaw, pick, encode_closed] using clause
  | @setPerm rule elements elements' ruleIn typed perm =>
      have clause := derives_of_clause (R := R) (laws.laws (permuteLaw .hashSet) (by simp [lawClauses, kindLaws]))
        (pick [encodeList elements, encodeList elements']) (fun g inside => by
          simp only [permuteLaw, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · exact goal_of_typedAt laws rfl ⟨rule, ruleIn, typed⟩
          · simpa [goalHolds, pick] using permute_complete laws.lists laws.picks elements' elements perm)
      simpa [permuteLaw, pick, encode_closed] using clause
  | @setDedup rule x rest ruleIn typed =>
      have clause := derives_of_clause (R := R) (laws.laws dedupForward (by simp [lawClauses, kindLaws]))
        (pick [encode x, encodeList rest]) (fun g inside => by
          simp only [dedupForward, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact goal_of_typedAt laws (xs := x :: x :: rest) (by simp [pick, encodeList]) ⟨rule, ruleIn, typed⟩)
      simpa [dedupForward, pick, encode_closed, encodeList] using clause
  | @flatten rule kind algebra before inner after algebraRule flat sorted =>
      have member := algebra_member algebraRule (c := flattenForward kind rule.category) (by simp [algebraLaws, flat])
      have clause := derives_of_clause (R := R) (laws.laws _ member)
        (pick [encodeList (before ++ .collection kind inner none :: after), encodeList before, encodeList inner,
          encodeList after, encodeList (inner ++ after), encodeList (before ++ (inner ++ after))]) (fun g inside => by
          simp only [flattenForward, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl | rfl
          · exact goal_of_sorted laws rfl sorted
          · simpa [goalHolds, pick, encodeList, encode_closed] using
              split_complete (R := R) laws.lists before (.collection kind inner none :: after)
          · simpa [goalHolds, pick] using append_complete (R := R) laws.lists inner after
          · simpa [goalHolds, pick] using append_complete (R := R) laws.lists before (inner ++ after))
      simpa [flattenForward, pick, encode_closed, List.append_assoc] using clause
  | @singleton rule kind algebra _ algebraRule flat sorted =>
      have member := algebra_member algebraRule (c := singletonForward kind rule.category)
        (by simp [algebraLaws, flat])
      have clause := derives_of_clause (R := R) (laws.laws _ member) (pick [encode t]) (fun g inside => by
        simp only [singletonForward, List.mem_cons, List.not_mem_nil, or_false] at inside
        subst inside
        exact goal_of_sorted laws (xs := [t]) (by simp [pick, encodeList]) sorted)
      simpa [singletonForward, pick, encode_closed, encodeList] using clause
  | @unitElim rule kind algebra label before after algebraRule unitIs sorted =>
      have member := algebra_member algebraRule (c := unitElimForward kind rule.category label)
        (by simp [algebraLaws, unitIs])
      have clause := derives_of_clause (R := R) (laws.laws _ member)
        (pick [encodeList (before ++ .apply label [] :: after), encodeList before, encodeList after,
          encodeList (before ++ after)]) (fun g inside => by
          simp only [unitElimForward, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · exact goal_of_sorted laws rfl sorted
          · simpa [goalHolds, pick, encodeList] using
              split_complete (R := R) laws.lists before (.apply label [] :: after)
          · simpa [goalHolds, pick] using append_complete (R := R) laws.lists before after)
      simpa [unitElimForward, pick, encode_closed] using clause
  | @emptyUnit rule kind algebra label algebraRule unitIs sorted =>
      have member := algebra_member algebraRule (c := emptyUnitForward kind rule.category label)
        (by simp [algebraLaws, unitIs])
      have clause := derives_of_clause (R := R) (laws.laws _ member) (pick []) (fun g inside => by
        simp only [emptyUnitForward, List.mem_cons, List.not_mem_nil, or_false] at inside
        subst inside
        exact goal_of_sorted laws (xs := []) rfl sorted)
      simpa [emptyUnitForward, pick, encode_closed, encodeList] using clause

/-- **Every instance of a law read backwards is derived by the law clauses.** -/
theorem law_backward (laws : LawProgram language R program) {s t : Pattern} (derived : DerivedInstance language s t) :
    Derives R program lawRelation (encode t) (encode s) := by
  cases derived with
  | @bagPerm rule elements elements' ruleIn typed perm =>
      have clause := derives_of_clause (R := R) (laws.laws (permuteLaw .hashBag) (by simp [lawClauses, kindLaws]))
        (pick [encodeList elements', encodeList elements]) (fun g inside => by
          simp only [permuteLaw, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · exact goal_of_typedAt laws rfl ⟨rule, ruleIn, collectionTypedAt_perm typed perm⟩
          · simpa [goalHolds, pick] using permute_complete laws.lists laws.picks elements elements' perm.symm)
      simpa [permuteLaw, pick, encode_closed] using clause
  | @setPerm rule elements elements' ruleIn typed perm =>
      have clause := derives_of_clause (R := R) (laws.laws (permuteLaw .hashSet) (by simp [lawClauses, kindLaws]))
        (pick [encodeList elements', encodeList elements]) (fun g inside => by
          simp only [permuteLaw, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · exact goal_of_typedAt laws rfl ⟨rule, ruleIn, collectionTypedAt_perm typed perm⟩
          · simpa [goalHolds, pick] using permute_complete laws.lists laws.picks elements elements' perm.symm)
      simpa [permuteLaw, pick, encode_closed] using clause
  | @setDedup rule x rest ruleIn typed =>
      have clause := derives_of_clause (R := R) (laws.laws dedupBackward (by simp [lawClauses, kindLaws]))
        (pick [encode x, encodeList rest]) (fun g inside => by
          simp only [dedupBackward, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          exact goal_of_typedAt laws (xs := x :: x :: rest) (by simp [pick, encodeList]) ⟨rule, ruleIn, typed⟩)
      simpa [dedupBackward, pick, encode_closed, encodeList] using clause
  | @flatten rule kind algebra before inner after algebraRule flat sorted =>
      have member := algebra_member algebraRule (c := flattenBackward kind rule.category)
        (by simp [algebraLaws, flat])
      have clause := derives_of_clause (R := R) (laws.laws _ member)
        (pick [encodeList (before ++ (inner ++ after)), encodeList before, encodeList (inner ++ after),
          encodeList inner, encodeList after, encodeList (before ++ .collection kind inner none :: after)])
        (fun g inside => by
          simp only [flattenBackward, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl | rfl
          · simpa [goalHolds, pick] using split_complete (R := R) laws.lists before (inner ++ after)
          · simpa [goalHolds, pick] using split_complete (R := R) laws.lists inner after
          · simpa [goalHolds, pick, encodeList, encode_closed] using
              append_complete (R := R) laws.lists before (.collection kind inner none :: after)
          · exact goal_of_sorted laws rfl sorted)
      simpa [flattenBackward, pick, encode_closed, List.append_assoc] using clause
  | @singleton rule kind algebra _ algebraRule flat sorted =>
      have member := algebra_member algebraRule (c := singletonBackward kind rule.category)
        (by simp [algebraLaws, flat])
      have clause := derives_of_clause (R := R) (laws.laws _ member) (pick [encode t]) (fun g inside => by
        simp only [singletonBackward, List.mem_cons, List.not_mem_nil, or_false] at inside
        subst inside
        exact goal_of_sorted laws (xs := [t]) (by simp [pick, encodeList]) sorted)
      simpa [singletonBackward, pick, encode_closed, encodeList] using clause
  | @unitElim rule kind algebra label before after algebraRule unitIs sorted =>
      have member := algebra_member algebraRule (c := unitElimBackward kind rule.category label)
        (by simp [algebraLaws, unitIs])
      have clause := derives_of_clause (R := R) (laws.laws _ member)
        (pick [encodeList (before ++ after), encodeList before, encodeList after,
          encodeList (before ++ .apply label [] :: after)]) (fun g inside => by
          simp only [unitElimBackward, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · simpa [goalHolds, pick] using split_complete (R := R) laws.lists before after
          · simpa [goalHolds, pick, encodeList] using
              append_complete (R := R) laws.lists before (.apply label [] :: after)
          · exact goal_of_sorted laws rfl sorted)
      simpa [unitElimBackward, pick, encode_closed] using clause
  | @emptyUnit rule kind algebra label algebraRule unitIs sorted =>
      have member := algebra_member algebraRule (c := emptyUnitBackward kind rule.category label)
        (by simp [algebraLaws, unitIs])
      have clause := derives_of_clause (R := R) (laws.laws _ member) (pick []) (fun g inside => by
        simp only [emptyUnitBackward, List.mem_cons, List.not_mem_nil, or_false] at inside
        subst inside
        exact goal_of_sorted laws (xs := []) rfl sorted)
      simpa [emptyUnitBackward, pick, encode_closed, encodeList] using clause

/-- **The law clauses derive exactly the instances of the laws, in both directions.** -/
theorem derives_law_iff (laws : LawProgram language R program) {s : Pattern} {w : Expr} :
    Derives R program lawRelation (encode s) w ↔
      ∃ t, w = encode t ∧ (DerivedInstance language s t ∨ DerivedInstance language t s) := by
  constructor
  · rintro ⟨depth, derived⟩
    exact law_sound laws derived
  · rintro ⟨t, rfl, forward | backward⟩
    · exact law_forward laws forward
    · exact law_backward laws backward

end Laws

end Mettapedia.GSLT.Compilation.Uniform.CollectionLaws

#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionLaws.derives_law_iff
