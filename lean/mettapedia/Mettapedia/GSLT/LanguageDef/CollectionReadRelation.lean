import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# Pure collection-membership premises

This relation reads an explicit closed collection value without consuming an
element. Each premise enumerates the same value independently, so repeated
premises may select the same element. The ordinary premise-aware engine still
matches the requested schema and threads its bindings. No global table or
external proof authority is consulted.

The enumeration retains the collection's list order and duplicate occurrences.
An open rest is not a completed collection and supplies no relation rows.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionReadRelation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

def name : String := "collection-member"

def rows : List Pattern → List (List Pattern)
  | [whole@(.collection _ elements none), _] => elements.map fun element => [whole, element]
  | _ => []

def environment : RelationEnv where
  tuples := fun relation arguments => if relation = name then rows arguments else []

theorem member_iff (kind : CollType) (elements : List Pattern) (query element : Pattern) :
    [.collection kind elements none, element] ∈
      environment.tuples name [.collection kind elements none, query] ↔ element ∈ elements := by
  simp [environment, rows]

theorem row_iff (kind : CollType) (elements : List Pattern) (query : Pattern) (row : List Pattern) :
    row ∈ environment.tuples name [.collection kind elements none, query] ↔
      ∃ element ∈ elements, row = [.collection kind elements none, element] := by
  simp only [environment, if_true, rows, List.mem_map]
  constructor
  · rintro ⟨element, member, rfl⟩
    exact ⟨element, member, rfl⟩
  · rintro ⟨element, member, rfl⟩
    exact ⟨element, member, rfl⟩

theorem unknown_relation (relation : String) (arguments : List Pattern) (different : relation ≠ name) :
    environment.tuples relation arguments = [] := by simp [environment, different]

theorem open_rest_is_not_completed (kind : CollType) (elements : List Pattern) (rest : String)
    (query : Pattern) :
    environment.tuples name [.collection kind elements (some rest), query] = [] := by
  simp [environment, rows]

theorem empty_has_no_rows (kind : CollType) (query : Pattern) :
    environment.tuples name [.collection kind [] none, query] = [] := by
  simp [environment, rows]

end Mettapedia.GSLT.LanguageDef.CollectionReadRelation
