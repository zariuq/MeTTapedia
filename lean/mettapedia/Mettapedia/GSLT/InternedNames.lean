/-
# Interned names for GSLT encodings

Finite boundary tables keep object-language names as `String` only at the
parser/user edge.  Internal encodings can then use small `Nat` keys, avoiding
choice-bearing name selection and making signature dispatch a finite table.
-/

namespace Mettapedia.GSLT.InternedNames

abbrev Key := Nat

structure Table where
  names : List String
  deriving Repr, DecidableEq

namespace Table

def empty : Table := { names := [] }

/-- Resolve an interned key back to its boundary string, when present. -/
def resolve? (tab : Table) (k : Key) : Option String := tab.names[k]?

/-- Search a list from a starting index, returning the first matching key. -/
def internAux (target : String) : Key -> List String -> Option Key
  | _, [] => none
  | k, name :: rest =>
      if target = name then some k else internAux target (k + 1) rest

/-- Intern a boundary string into the first matching key in the finite table. -/
def intern? (tab : Table) (target : String) : Option Key :=
  internAux target 0 tab.names

def contains (tab : Table) (target : String) : Bool :=
  (intern? tab target).isSome

theorem internAux_nil (target : String) (k : Key) :
    internAux target k [] = none := rfl

theorem internAux_hit (target : String) (k : Key) (rest : List String) :
    internAux target k (target :: rest) = some k := by
  simp [internAux]

theorem internAux_miss {target name : String} (h : target ≠ name) (k : Key)
    (rest : List String) :
    internAux target k (name :: rest) = internAux target (k + 1) rest := by
  simp [internAux, h]

theorem resolve?_empty (k : Key) : resolve? empty k = none := by
  cases k <;> rfl

def demo : Table := { names := ["prop", "nat", "z"] }

theorem demo_intern_nat : intern? demo "nat" = some 1 := rfl

theorem demo_intern_missing : intern? demo "missing" = none := rfl

theorem demo_resolve_nat : resolve? demo 1 = some "nat" := rfl

theorem demo_resolve_out_of_range : resolve? demo 3 = none := rfl

end Table

end Mettapedia.GSLT.InternedNames
