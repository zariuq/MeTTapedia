import Mettapedia.GSLT.LanguageDef.DecidableRelations.Stores

/-!
# Tables: stores that list their rows

A table lists the rows of one relation (`Table`). Asked about the relation, its store offers every row, and a query's
arguments select the rows they match, binding what the query leaves open. A table may be **closed**, under the name of
its complement: asked about the complement, it answers a first-order tuple it does not list.

- A table holds of exactly its rows (`table_answers_iff`), and a closed table's complement holds of exactly the other
  first-order tuples (`table_answers_complement_iff`). So the two are complemented there (`table_complemented`). This is
  the closed-world reading of a table, proved rather than assumed.
- An open table answers its relation and nothing else (`Table.tuples_eq_nil`). Its absence from a query is not a
  verdict.
- Tables plug in together (`tablesEnv`). A name declared by one table only is answered by that table alone
  (`mem_tablesEnv_tuples_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

/-- **A table**: the rows of a relation, and the name of its complement when the table is closed. -/
structure Table where
  relation : String
  complement : Option String := none
  rows : List (List Pattern)
  deriving Repr

namespace Table

/-- The names a table answers: its relation, and its complement when it is closed. -/
def names (table : Table) : List String := table.relation :: table.complement.toList

/-- **The tuples a table offers**: every row for its relation; for the complement of a closed table, a first-order
tuple it does not list. -/
def tuples (table : Table) (name : String) (arguments : List Pattern) : List (List Pattern) :=
  if name = table.relation then table.rows
  else if table.complement = some name then
    if isFirstOrderList arguments && !table.rows.contains arguments then [arguments] else []
  else []

/-- A table offers nothing for a name it does not declare. -/
theorem tuples_eq_nil (table : Table) {name : String} (undeclared : name ∉ table.names) (arguments : List Pattern) :
    table.tuples name arguments = [] := by
  simp only [names, List.mem_cons, Option.mem_toList, not_or] at undeclared
  have notComplement : table.complement ≠ some name := fun same => undeclared.2 (Option.mem_def.mpr same)
  simp [tuples, undeclared.1, notComplement]

/-- **The store of a table.** -/
def store (table : Table) : RelationEnv := ⟨table.tuples⟩

end Table

variable {language : LanguageDef} {table : Table}

/-- **A table holds of exactly its rows**, on first-order tuples. -/
theorem table_answers_iff (notEq : table.relation ≠ "eq") {arguments : List Pattern}
    (first : ∀ argument ∈ arguments, FirstOrder argument) :
    Answers table.store language table.relation arguments ↔ arguments ∈ table.rows := by
  rw [answers_iff first, builtinRelationTuples_eq_nil notEq]
  simp [Table.store, Table.tuples]

/-- **A closed table's complement holds of exactly the first-order tuples it does not list.** -/
theorem table_answers_complement_iff {complement : String} (closed : table.complement = some complement)
    (complementNotEq : complement ≠ "eq") (distinct : complement ≠ table.relation) {arguments : List Pattern}
    (first : ∀ argument ∈ arguments, FirstOrder argument) :
    Answers table.store language complement arguments ↔ arguments ∉ table.rows := by
  rw [answers_iff first, builtinRelationTuples_eq_nil complementNotEq]
  have checked : isFirstOrderList arguments = true := isFirstOrderList_iff_firstOrder.mpr first
  by_cases listed : arguments ∈ table.rows <;>
    simp [Table.store, Table.tuples, distinct, closed, checked, listed]

/-- **A closed table and its complement are complemented** on first-order tuples. -/
theorem table_complemented {complement : String} (closed : table.complement = some complement)
    (notEq : table.relation ≠ "eq") (complementNotEq : complement ≠ "eq") (distinct : complement ≠ table.relation) :
    Complemented (Answers table.store language table.relation) (Answers table.store language complement)
      (fun arguments => ∀ argument ∈ arguments, FirstOrder argument) where
  disjoint arguments first held failed :=
    (table_answers_complement_iff closed complementNotEq distinct first).mp failed
      ((table_answers_iff notEq first).mp held)
  exhaustive arguments first := by
    by_cases listed : arguments ∈ table.rows
    · exact .inl ((table_answers_iff notEq first).mpr listed)
    · exact .inr ((table_answers_complement_iff closed complementNotEq distinct first).mpr listed)

/-! ## Tables together -/

/-- **Tables plugged in together**: each offers its tuples for the names it declares. -/
def tablesEnv (tables : List Table) : RelationEnv :=
  ⟨fun name arguments => tables.flatMap fun table => table.tuples name arguments⟩

/-- **A name declared by one table only is answered by that table alone**: the tuples offered for it are that table's. -/
theorem mem_tablesEnv_tuples_iff {tables : List Table} {table : Table} (member : table ∈ tables) {name : String}
    (alone : ∀ other ∈ tables, name ∈ other.names → other = table) (arguments tuple : List Pattern) :
    tuple ∈ (tablesEnv tables).tuples name arguments ↔ tuple ∈ table.tuples name arguments := by
  simp only [tablesEnv, List.mem_flatMap]
  constructor
  · rintro ⟨other, otherMember, offered⟩
    by_cases otherDeclares : name ∈ other.names
    · rwa [alone other otherMember otherDeclares] at offered
    · rw [other.tuples_eq_nil otherDeclares] at offered
      simp at offered
  · intro offered
    exact ⟨table, member, offered⟩

end Mettapedia.GSLT.LanguageDef.DecidableRelations
