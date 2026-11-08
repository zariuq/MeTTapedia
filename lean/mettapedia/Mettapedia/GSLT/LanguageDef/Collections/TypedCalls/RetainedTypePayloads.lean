import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeSymbolKeys

/-!
# Immutable payloads for retained type-state interning

The output of type inference needs its own retention check. A stable input
term can infer a type containing an external mutable value. Groundness does
not exclude that value, and copying the surrounding tree retains its handle.

This module admits the existing Atom carrier's exact immutable fragment:
symbols, integers, Booleans, strings and expressions made from them. Variables
and custom/external values decline. The native counterpart must also exclude
numeric representations whose equality forgets observable distinctions; this
fragment does not certify floats, rationals, opaque values or their codecs.

The logical interner below performs the native sequence: hash prefilter,
ordered equality, then copy-and-append. Its ids are zero-based array indices
(the native nonzero id is index plus one). Hash collisions cannot make an
incorrect hit. A failed admission returns no id and requires canonical
inference, not a language failure. Allocation, pointer epochs and capacity
are separate from the retained-value law.

External observations are explicit only to expose the mutable counterexample.
They do not occur in admitted payloads. The copy is a structural rebuilding
operation and leaves external handles intact, matching reference-copy rather
than freezing semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RetainedTypePayloads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

mutual
def admitted : Atom → Bool
  | .symbol _ => true
  | .var _ => false
  | .grounded (.int _) => true
  | .grounded (.bool _) => true
  | .grounded (.string _) => true
  | .grounded (.custom _ _) => false
  | .expression children => admittedList children
def admittedList : List Atom → Bool
  | [] => true
  | atom :: atoms => admitted atom && admittedList atoms
end

mutual
def copy : Atom → Atom
  | .symbol name => .symbol name
  | .var name => .var name
  | .grounded (.int n) => .grounded (.int n)
  | .grounded (.bool b) => .grounded (.bool b)
  | .grounded (.string s) => .grounded (.string s)
  | .grounded (.custom tag key) => .grounded (.custom tag key)
  | .expression children => .expression (copyList children)
def copyList : List Atom → List Atom
  | [] => []
  | atom :: atoms => copy atom :: copyList atoms
end

abbrev ExternalView := String → String → Atom

mutual
def observe (external : ExternalView) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => .var name
  | .grounded (.custom tag key) => external tag key
  | .grounded other => .grounded other
  | .expression children => .expression (observeList external children)
def observeList (external : ExternalView) : List Atom → List Atom
  | [] => []
  | atom :: atoms => observe external atom :: observeList external atoms
end

mutual
theorem copy_eq : ∀ atom, copy atom = atom
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded value => by cases value <;> rfl
  | .expression children => by rw [copy, copyList_eq]
theorem copyList_eq : ∀ atoms, copyList atoms = atoms
  | [] => rfl
  | atom :: atoms => by rw [copyList, copy_eq, copyList_eq]
end

mutual
theorem admitted_observe (external : ExternalView) : ∀ atom,
    admitted atom = true → observe external atom = atom
  | .symbol _, _ => rfl
  | .var _, valid => by simp [admitted] at valid
  | .grounded value, valid => by cases value <;> simp_all [admitted, observe]
  | .expression children, valid => by
      rw [observe, admittedList_observe external children valid]
theorem admittedList_observe (external : ExternalView) : ∀ atoms,
    admittedList atoms = true → observeList external atoms = atoms
  | [], _ => rfl
  | atom :: atoms, valid => by
      simp only [admittedList, Bool.and_eq_true] at valid
      rw [observeList, admitted_observe external atom valid.1,
        admittedList_observe external atoms valid.2]
end

theorem admittedList_iff (atoms : List Atom) :
    admittedList atoms = true ↔ ∀ atom ∈ atoms, admitted atom = true := by
  induction atoms with
  | nil => simp [admittedList]
  | cons atom atoms ih => simp [admittedList, ih]

/-- Equality at one observation point need not be stable for external
payloads. On admitted type lists it is exact structural equality. -/
def equalAt (external : ExternalView) (left right : List Atom) : Bool :=
  observeList external left == observeList external right

theorem admitted_equal_iff (external : ExternalView) {left right : List Atom}
    (leftSafe : admittedList left = true) (rightSafe : admittedList right = true) :
    equalAt external left right = true ↔ left = right := by
  simp [equalAt, admittedList_observe external left leftSafe,
    admittedList_observe external right rightSafe]

abbrev Table := List (List Atom)

def Valid (table : Table) : Prop := ∀ types ∈ table, admittedList types = true

def find (external : ExternalView) (hash : List Atom → Nat) (query : List Atom) : Table → Option Nat
  | [] => none
  | types :: rest =>
      if hash types == hash query && equalAt external types query then some 0
      else (find external hash query rest).map Nat.succ

def materialize (table : Table) (index : Nat) : Option (List Atom) :=
  table[index]?.map copyList

def intern (external : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (table : Table) : Option (Nat × Table) :=
  if admittedList query then
    match find external hash query table with
    | some index => some (index, table)
    | none => some (table.length, table ++ [copyList query])
  else none

theorem find_exact (external : ExternalView) (hash : List Atom → Nat) (query : List Atom)
    (safe : admittedList query = true) : ∀ table, Valid table → ∀ index,
      find external hash query table = some index → table[index]? = some query
  | [], _, _, found => by simp [find] at found
  | types :: rest, valid, index, found => by
      unfold find at found
      split at found
      next equal =>
        have same := (admitted_equal_iff external (valid types (by simp)) safe).mp
          (Bool.and_eq_true_iff.mp equal).2
        cases Option.some.inj found
        simp [same]
      next unequal =>
        simp only [Option.map_eq_some_iff] at found
        obtain ⟨position, found, rfl⟩ := found
        simpa using find_exact external hash query safe rest
          (fun types member => valid types (List.mem_cons_of_mem _ member)) position found

/-- The interner returns an id whose materialization is the original type
list, preserving its order and duplicates; it also preserves admission of
every retained payload. No injective hash assumption is required. -/
theorem intern_sound (external : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (table : Table) (valid : Valid table)
    (index : Nat) (after : Table) (stored : intern external hash query table = some (index, after)) :
    Valid after ∧ materialize after index = some query ∧ admittedList query = true := by
  unfold intern at stored
  split at stored
  next safe =>
    split at stored
    next found =>
      cases Option.some.inj stored
      exact ⟨valid, by simp [materialize, find_exact external hash query safe table valid _ found, copyList_eq], safe⟩
    next missing =>
      cases Option.some.inj stored
      refine ⟨?_, ?_, safe⟩
      · intro types member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact valid types old
        · simpa [copyList_eq] using safe
      · simp [materialize, copyList_eq]
  next refused => simp at stored

/-- After arbitrary external state changes, the retained id still observes
the same types. The output-side admission, not input groundness, earns this. -/
theorem retained_observation_stable (before later : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (table : Table) (valid : Valid table)
    (index : Nat) (after : Table) (stored : intern before hash query table = some (index, after)) :
    (materialize after index).map (observeList later) = some query := by
  obtain ⟨_, readback, safe⟩ := intern_sound before hash query table valid index after stored
  rw [readback, Option.map_some, admittedList_observe later query safe]

/-- Publishing another type state does not retarget any previously returned
id. The table grows by appending a separately rebuilt payload. -/
theorem intern_preserves_materialized (external : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (table : Table) (index : Nat) (after : Table)
    (stored : intern external hash query table = some (index, after))
    (oldIndex : Nat) (old : List Atom) (readback : materialize table oldIndex = some old) :
    materialize after oldIndex = some old := by
  unfold intern at stored
  split at stored
  · split at stored
    · cases Option.some.inj stored
      exact readback
    · cases Option.some.inj stored
      unfold materialize at readback ⊢
      have present : table[oldIndex]?.isSome := by
        cases found : table[oldIndex]? with
        | none => simp [found] at readback
        | some types => rfl
      obtain ⟨types, lookup⟩ := Option.isSome_iff_exists.mp present
      obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp lookup
      rw [List.getElem?_append_left inside]
      exact readback
  · simp at stored

/-- An unsafe type is declined before any representative is published. -/
theorem unsafe_declines (external : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (table : Table) (rejected : admittedList query = false) :
    intern external hash query table = none := by simp [intern, rejected]

inductive ChildCode (Kind : Type) where
  | symbol (name : String)
  | typed (kind : Kind) (state : Nat)
  deriving DecidableEq

structure KeyCode (Kind : Type) where
  head : String
  question : Bool
  children : List (ChildCode Kind)
  deriving DecidableEq

def encodeChild {Kind : Type} (external : ExternalView) (hash : List Atom → Nat) (table : Table) :
    NativeSymbolKeys.ChildKey Atom Kind → Option (ChildCode Kind)
  | .symbol name => some (.symbol name)
  | .typed kind types =>
      if admittedList types then (find external hash types table).map (.typed kind) else none

def decodeChild {Kind : Type} (table : Table) : ChildCode Kind → Option (NativeSymbolKeys.ChildKey Atom Kind)
  | .symbol name => some (.symbol name)
  | .typed kind state => (materialize table state).map (.typed kind)

theorem encodeChild_readback {Kind : Type} (external : ExternalView) (hash : List Atom → Nat)
    (table : Table) (valid : Valid table) (child : NativeSymbolKeys.ChildKey Atom Kind)
    (code : ChildCode Kind) (encoded : encodeChild external hash table child = some code) :
    decodeChild table code = some child := by
  cases child with
  | symbol name => cases Option.some.inj encoded; rfl
  | typed kind types =>
      change (if admittedList types then (find external hash types table).map (ChildCode.typed kind)
        else none) = some code at encoded
      split at encoded
      next safe =>
        simp only [Option.map_eq_some_iff] at encoded
        obtain ⟨state, found, rfl⟩ := encoded
        simp [decodeChild, materialize, find_exact external hash types safe table valid state found, copyList_eq]
      next refused => simp at encoded

def encodeChildren {Kind : Type} (external : ExternalView) (hash : List Atom → Nat) (table : Table) :
    List (NativeSymbolKeys.ChildKey Atom Kind) → Option (List (ChildCode Kind))
  | [] => some []
  | child :: children => (encodeChild external hash table child).bind fun code =>
      (encodeChildren external hash table children).map (code :: ·)

def decodeChildren {Kind : Type} (table : Table) :
    List (ChildCode Kind) → Option (List (NativeSymbolKeys.ChildKey Atom Kind))
  | [] => some []
  | code :: codes => (decodeChild table code).bind fun child =>
      (decodeChildren table codes).map (child :: ·)

theorem encodeChildren_readback {Kind : Type} (external : ExternalView) (hash : List Atom → Nat)
    (table : Table) (valid : Valid table) :
    ∀ (children : List (NativeSymbolKeys.ChildKey Atom Kind)) (codes : List (ChildCode Kind)),
      encodeChildren external hash table children = some codes → decodeChildren table codes = some children
  | [], codes, encoded => by cases Option.some.inj encoded; rfl
  | child :: children, codes, encoded => by
      simp only [encodeChildren, Option.bind_eq_some_iff, Option.map_eq_some_iff] at encoded
      obtain ⟨code, first, rest, later, rfl⟩ := encoded
      rw [decodeChildren, encodeChild_readback external hash table valid child code first,
        Option.bind_some, encodeChildren_readback external hash table valid children rest later]
      rfl

def encodeKey {Kind : Type} (external : ExternalView) (hash : List Atom → Nat) (table : Table)
    (key : NativeSymbolKeys.Key Atom Kind) : Option (KeyCode Kind) :=
  (encodeChildren external hash table key.children).map fun children => ⟨key.head, key.question, children⟩

def decodeKey {Kind : Type} (table : Table) (code : KeyCode Kind) : Option (NativeSymbolKeys.Key Atom Kind) :=
  (decodeChildren table code.children).map fun children => ⟨code.head, code.question, children⟩

theorem encodeKey_readback {Kind : Type} (external : ExternalView) (hash : List Atom → Nat)
    (table : Table) (valid : Valid table) (key : NativeSymbolKeys.Key Atom Kind) (code : KeyCode Kind)
    (encoded : encodeKey external hash table key = some code) : decodeKey table code = some key := by
  simp only [encodeKey, Option.map_eq_some_iff] at encoded
  obtain ⟨children, encoded, rfl⟩ := encoded
  rw [decodeKey, encodeChildren_readback external hash table valid key.children children encoded]
  rfl

/-- The repaired symbol-sensitive key remains adequate after its type lists
are replaced by verified retained state ids. This supplies a concrete codec
law rather than assuming that the native interner has one. -/
theorem retained_key_source_congruence {Kind Bind : Type}
    (ops : NativeTypeViews.Ops Atom Bind Kind) (reads : NativeTypeViews.Reads Atom Atom Kind)
    (tupleView : List Atom → List Atom) (hash : List Atom → Nat)
    (table : Table) (valid : Valid table) (leftWorld rightWorld : ExternalView)
    (q q' : Bool) (head head' : String) (children children' : List Atom)
    (leftAdmitted : NativeSymbolKeys.Admitted reads tupleView q head children)
    (rightAdmitted : NativeSymbolKeys.Admitted reads tupleView q' head' children')
    (code : KeyCode Kind)
    (leftStored : encodeKey leftWorld hash table (NativeSymbolKeys.key reads q head children) = some code)
    (rightStored : encodeKey rightWorld hash table (NativeSymbolKeys.key reads q' head' children') = some code) :
    NativeTypeViews.sourceNode ops reads q (.symbol head) children =
      NativeTypeViews.sourceNode ops reads q' (.symbol head') children' := by
  apply NativeSymbolKeys.equal_keys_equal_source ops leftAdmitted rightAdmitted
  have leftRead := encodeKey_readback leftWorld hash table valid _ code leftStored
  have rightRead := encodeKey_readback rightWorld hash table valid _ code rightStored
  exact Option.some.inj (leftRead.symm.trans rightRead)

namespace Controls

def ordinary : List Atom := [.expression [.symbol "List", .grounded (.int 3)],
  .grounded (.bool true), .grounded (.string "typed")]

theorem ordinary_grammar_admitted : admittedList ordinary = true := by decide

theorem colliding_hashes_still_compare_payloads (external : ExternalView) :
    intern external (fun _ => 0) ordinary [[.symbol "different"]] =
      some (1, [[.symbol "different"], ordinary]) := by
  simp [intern, find, equalAt, ordinary, admittedList, admitted, observeList, observe, copyList_eq]

def state (key : String) : Atom := .grounded (.custom "State" key)
def query (key : String) : List Atom := [.expression [.symbol "H", state key]]
def initial : ExternalView := fun _ _ => .grounded (.int 1)
def changed : ExternalView := fun _ key => .grounded (.int (if key = "A" then 2 else 1))

theorem ground_external_payload_not_admitted : admittedList (query "A") = false := rfl

/-- The current-content equality read conflates the two handles. Copying
the chosen representative retains its handle rather than freezing a value. -/
theorem mutable_initially_equal :
    equalAt initial (query "A") (query "B") = true ∧
      find initial (fun _ => 0) (query "B") [query "A"] = some 0 := by decide

theorem mutable_copy_keeps_handle : materialize [query "A"] 0 = some (query "A") := by decide

theorem mutable_reuse_changes_observation :
    (materialize [query "A"] 0).map (observeList changed) ≠ some (observeList changed (query "B")) := by
  decide

theorem output_check_rejects_conflation :
    intern initial (fun _ => 0) (query "B") [query "A"] = none := rfl

def formalOps (external : ExternalView) : NativeTypeViews.Ops Atom Unit Unit where
  arrow := fun type_ => match type_ with
    | .expression [.symbol "->", formal, returned] => some ([formal], returned)
    | _ => none
  initial := ()
  apply := fun _ type_ => type_
  unify := fun _ actual expected => if equalAt external [actual] [expected] then some () else none
  metaCheck := fun _ _ => none
  normalize := id
  tuple := Atom.expression
  undefined := .symbol "%Undefined%"
  nativeMork := .symbol "MorkSpace"
  listType := .symbol "List"
  subtypeAdditions := fun _ => []

def formalReads : NativeTypeViews.Reads Atom Atom Unit where
  classify := fun _ _ => .ordinary
  annotations := fun _ _ => []
  headRows := fun _ => [.expression [.symbol "->", state "A", .symbol "R"]]
  tupleHead := fun _ => []
  kind := fun _ => ()
  inferred := fun _ => [state "B"]
  tuplePart := fun _ => [state "B"]

/-- The inferred result can be immutable even though the service used to
compute it changes within a declaration revision. Whole-node hits also need
the mutable dependencies of formal matching in their validated scope. -/
theorem immutable_output_does_not_stabilize_service :
    admitted (.expression [.symbol "f", .symbol "a"]) = true ∧
    NativeTypeViews.sourceNode (formalOps initial) formalReads true (.symbol "f") [.symbol "a"] =
      [.symbol "R"] ∧
    NativeTypeViews.sourceNode (formalOps changed) formalReads true (.symbol "f") [.symbol "a"] = [] ∧
    admittedList [.symbol "R"] = true := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RetainedTypePayloads
