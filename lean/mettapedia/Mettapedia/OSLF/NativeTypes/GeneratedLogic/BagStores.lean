import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagJudgmentPremises
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Tables

/-!
# Stores that plug into bag languages

A store decides a relation (`DecidableRelations.ofDecision`), and every decision procedure is one: a closed list of
facts, a trie of serialized terms, a table under a key. A bag language reads its terms modulo the bag laws, so a rule's
query hands the store captured values in whatever order a presentation lists their bags. The sorted-bag reading of the
language stays coherent with its queries exactly when the store answers modulo the bag laws too (`RespectsCanon`). That
is the condition a store must meet to plug in.

- A store whose decision gives the same verdict at canonical arguments respects canonical forms
  (`respectsCanon_ofDecision`).
- A store that reads its arguments through their canonical forms does (`respectsCanon_throughCanon`). A trie or table
  keyed by the serialization of canonical forms is one.
- A closed fact store of first-order tuples does, whatever its keys (`respectsCanon_factStore`): first-order terms are
  their own canonical forms, and only they are.
- A table of first-order rows does, open or closed, alone or with others (`respectsCanon_table`,
  `respectsCanon_tablesEnv`), and its tuples have no set (`tuplesSetFree_tablesEnv`), so rules may both query tables
  and ask judgments (`BagForms.formsJudgments`).
- A store that reads the order a presentation lists does not. Asking whether the first element of a bag is `A`
  separates `{A, B}` from `{B, A}`, which have one canonical form (`firstIsA_not_respectsCanon`).

A bag language whose rules query a store that respects canonical forms, over metavariables, has certified canonical
forms in that store's relation environment (`BagForms.formsQueries`), for instance with a closed fact store
(`factStoreForms`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags
  (canon canon_collection canon_apply canon_idempotent arrange_bag setFree setFreeList_iff)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (sortLex)
open Mettapedia.GSLT.LanguageDef.DecidableRelations
  (FirstOrder ofDecision factStore Table tablesEnv isFirstOrderList isFirstOrderList_iff_firstOrder)

/-! ## The condition for plugging in -/

variable {relation complement : String}

/-- **A store respects canonical forms when its verdict is the same at canonical arguments.** -/
theorem respectsCanon_ofDecision {decide : List Pattern → Bool}
    (invariant : ∀ arguments, decide (arguments.map canon) = decide arguments) :
    RespectsCanon (ofDecision relation complement decide) := by
  intro name arguments tuple member
  simp only [ofDecision] at member ⊢
  rw [invariant arguments]
  by_cases isRelation : name = relation
  · simp only [isRelation, ↓reduceIte] at member ⊢
    cases verdict : decide arguments <;> simp_all
  · by_cases isComplement : name = complement
    · simp only [isComplement, ↓reduceIte] at member ⊢
      cases verdict : decide arguments <;> simp_all
    · simp [isRelation, isComplement] at member

/-- **A store that reads its arguments through their canonical forms respects them**, as a trie or a table keyed by
the serialization of canonical forms does. -/
theorem respectsCanon_throughCanon (test : List Pattern → Bool) :
    RespectsCanon (ofDecision relation complement fun arguments => test (arguments.map canon)) :=
  respectsCanon_ofDecision fun arguments => by
    simp only [List.map_map]
    congr 1
    exact List.map_congr_left fun argument _ => canon_idempotent argument

/-- **A closed fact store of first-order tuples respects canonical forms**, whatever its keys. -/
theorem respectsCanon_factStore {stored : List (List Pattern)} (first : ∀ tuple ∈ stored, ∀ x ∈ tuple, FirstOrder x) :
    RespectsCanon (factStore relation complement stored) :=
  respectsCanon_ofDecision fun arguments => by
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    constructor
    · intro member
      have same : arguments = arguments.map canon := eq_of_map_canon_eq_firstOrder (first _ member) rfl
      rw [same]
      exact member
    · intro member
      have unchanged : arguments.map canon = arguments := by
        conv_rhs => rw [← List.map_id arguments]
        exact List.map_congr_left fun x inArguments => canon_firstOrder (first _ member x inArguments)
      rwa [unchanged]

/-- A list of first-order terms is its own list of canonical forms. -/
theorem map_canon_firstOrder {terms : List Pattern} (first : ∀ x ∈ terms, FirstOrder x) : terms.map canon = terms := by
  conv_rhs => rw [← List.map_id terms]
  exact List.map_congr_left fun x member => canon_firstOrder (first x member)

/-- **A table of first-order rows respects canonical forms**: its rows are their own canonical forms, and a closed
table's complement reads a tuple only where it is first-order. -/
theorem respectsCanon_table {table : Table} (first : ∀ row ∈ table.rows, ∀ x ∈ row, FirstOrder x) :
    RespectsCanon table.store := by
  intro name arguments tuple offered
  simp only [Table.store, Table.tuples] at offered ⊢
  by_cases isRelation : name = table.relation
  · simp only [isRelation, ↓reduceIte] at offered ⊢
    rwa [map_canon_firstOrder (first tuple offered)]
  · by_cases isComplement : table.complement = some name
    · simp only [isRelation, isComplement, ↓reduceIte] at offered ⊢
      split at offered
      · rename_i condition
        rw [List.mem_singleton] at offered
        subst offered
        have checked : isFirstOrderList tuple = true := by
          simp only [Bool.and_eq_true] at condition
          exact condition.1
        rw [map_canon_firstOrder (isFirstOrderList_iff_firstOrder.mp checked), if_pos condition]
        exact List.mem_singleton_self _
      · simp at offered
    · simp [isRelation, isComplement] at offered

/-- **Tables of first-order rows plugged in together respect canonical forms.** -/
theorem respectsCanon_tablesEnv {tables : List Table}
    (first : ∀ table ∈ tables, ∀ row ∈ table.rows, ∀ x ∈ row, FirstOrder x) : RespectsCanon (tablesEnv tables) := by
  intro name arguments tuple offered
  simp only [tablesEnv, List.mem_flatMap] at offered ⊢
  obtain ⟨table, member, inTable⟩ := offered
  exact ⟨table, member, respectsCanon_table (first table member) name arguments tuple inTable⟩

/-- A first-order term has no set. -/
theorem setFree_of_firstOrder {term : Pattern} (first : FirstOrder term) : setFree term = true := by
  induction first with
  | @apply constructor arguments _ inner =>
    simp only [setFree, setFreeList_iff]
    exact inner

/-- **A table of first-order rows offers tuples with no set.** -/
theorem tuplesSetFree_table {table : Table} (first : ∀ row ∈ table.rows, ∀ x ∈ row, FirstOrder x) :
    TuplesSetFree table.store := by
  intro name arguments tuple offered
  simp only [Table.store, Table.tuples] at offered
  by_cases isRelation : name = table.relation
  · simp only [isRelation, ↓reduceIte] at offered
    exact fun x member => setFree_of_firstOrder (first tuple offered x member)
  · by_cases isComplement : table.complement = some name
    · simp only [isRelation, isComplement, ↓reduceIte] at offered
      split at offered
      · rename_i condition
        rw [List.mem_singleton] at offered
        subst offered
        have checked : isFirstOrderList tuple = true := by
          simp only [Bool.and_eq_true] at condition
          exact condition.1
        exact fun x member => setFree_of_firstOrder (isFirstOrderList_iff_firstOrder.mp checked x member)
      · simp at offered
    · simp [isRelation, isComplement] at offered

/-- **Tables of first-order rows plugged in together offer tuples with no set.** -/
theorem tuplesSetFree_tablesEnv {tables : List Table}
    (first : ∀ table ∈ tables, ∀ row ∈ table.rows, ∀ x ∈ row, FirstOrder x) : TuplesSetFree (tablesEnv tables) := by
  intro name arguments tuple offered
  simp only [tablesEnv, List.mem_flatMap] at offered
  obtain ⟨table, member, inTable⟩ := offered
  exact tuplesSetFree_table (first table member) name arguments tuple inTable

/-- **Certified canonical forms for a bag language querying a closed fact store**: no authored equations, no
collection algebra, and rules whose premises are queries over metavariables. -/
def factStoreForms {language : LanguageDef} {stored : List (List Pattern)}
    (first : ∀ tuple ∈ stored, ∀ x ∈ tuple, FirstOrder x) (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false)
    (queried : language.rewrites.all (fun rule => rule.premises.all query) = true) (fuel : ℕ) :
    CanonicalForms (factStore relation complement stored) language fuel :=
  formsQueries noEquations noAlgebra queried (respectsCanon_factStore first) fuel

/-! ## A store that does not plug in -/

/-- The constant `A`. -/
def constantA : Pattern := .apply "A" []

/-- The constant `B`. -/
def constantB : Pattern := .apply "B" []

/-- Whether the first element listed in a bag argument is `A`: a store that reads the order of a presentation. -/
def firstIsA : List Pattern → Bool
  | [.collection _ (first :: _) _] => first == constantA
  | _ => false

/-- `{A, B}` and `{B, A}` have one canonical form. -/
theorem canon_pair_swap :
    canon (.collection .hashBag [constantA, constantB] none) = canon (.collection .hashBag [constantB, constantA] none) := by
  rw [canon_collection, canon_collection]
  congr 1
  simp only [List.map_cons, List.map_nil]
  exact Mettapedia.OSLF.MeTTaIL.CanonicalBags.arrange_perm rfl (List.Perm.swap _ _ [])

/-- **Negative: a store that reads the order of a presentation does not respect canonical forms.** It tells `{A, B}`
from `{B, A}`, which have one canonical form, so one of them is answered at a match and not at the canonical match. -/
theorem firstIsA_not_respectsCanon : ¬ RespectsCanon (ofDecision "First" "NotFirst" firstIsA) := by
  intro respects
  cases verdict : firstIsA [canon (.collection .hashBag [constantA, constantB] none)] with
  | true =>
    have answered : [Pattern.collection .hashBag [constantB, constantA] none] ∈
        (ofDecision "First" "NotFirst" firstIsA).tuples "NotFirst" [.collection .hashBag [constantB, constantA] none] := by
      simp [ofDecision, firstIsA, constantA, constantB]
    have moved := respects "NotFirst" _ _ answered
    simp only [List.map_cons, List.map_nil, ← canon_pair_swap] at moved
    simp [ofDecision, verdict] at moved
  | false =>
    have answered : [Pattern.collection .hashBag [constantA, constantB] none] ∈
        (ofDecision "First" "NotFirst" firstIsA).tuples "First" [.collection .hashBag [constantA, constantB] none] := by
      simp [ofDecision, firstIsA, constantA]
    have moved := respects "First" _ _ answered
    simp only [List.map_cons, List.map_nil] at moved
    simp [ofDecision, verdict] at moved

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms
