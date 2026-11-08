import Mettapedia.Machines.ReadCertifiedQueryReuse

/-!
# Read-certified token dispatch

Leading and trailing parser tables have separate keyed and unindexed buckets.
Identifier dispatch distinguishes an absent named bucket from a present empty
one, and avoids duplicating the identifier bucket when both keys coincide.
The direct table semantics and the adaptive read program are independent
definitions. Their exact ordered results agree, including duplicate parsers.

This is dispatch, not parser execution, syntax selection or error recovery.
An adapter must establish its table and token interpretation. Release identity
is a conservative cache boundary, not a proof of cross-version equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.KeyedParserDispatch

open Mettapedia.Machines

inductive Phase where
  | leading | trailing
  deriving DecidableEq, Repr

inductive IdentBehavior where
  | default | symbol | both
  deriving DecidableEq, Repr

inductive Token (Name : Type) where
  | atom (name : Name)
  | ident (name : Name)
  | node (kind : Name)
  | other
  deriving DecidableEq, Repr

structure Key (Name : Type) where
  category : Name
  phase : Phase
  token : Option Name
  deriving DecidableEq, Repr

structure Request (Name : Type) where
  category : Name
  phase : Phase
  token : Token Name
  behavior : IdentBehavior
  identKind : Name
  deriving DecidableEq, Repr

structure Profile where
  schema : Nat
  release : String
  adapter : String
  deriving DecidableEq, Repr

variable {Name Parser : Type} [DecidableEq Name]

abbrev Store (Name Parser : Type) := Key Name → Option (List Parser)
abbrev Program (Name Parser Answer : Type) :=
  ReadOnlyQuery.Program (Key Name) (Option (List Parser)) Answer

def Request.key (request : Request Name) (token : Option Name) : Key Name :=
  ⟨request.category, request.phase, token⟩

/-- Independent ordered dispatch semantics for one already classified token. -/
def indexed (store : Store Name Parser) (request : Request Name) : List Parser :=
  let find := fun name => (store (request.key (some name))).getD []
  match request.token with
  | .atom name | .node name => find name
  | .other => []
  | .ident name =>
      match request.behavior with
      | .default => find request.identKind
      | .symbol =>
          match store (request.key (some name)) with
          | some parsers => parsers
          | none => find request.identKind
      | .both =>
          match store (request.key (some name)) with
          | none => find request.identKind
          | some parsers =>
              if name = request.identKind then parsers
              else parsers ++ find request.identKind

def dispatch (store : Store Name Parser) (request : Request Name) : List Parser :=
  let keyed := indexed store request
  let unindexed := (store (request.key none)).getD []
  match request.phase with
  | .leading => unindexed ++ keyed
  | .trailing => keyed ++ unindexed

def findQuery (request : Request Name) (name : Name) : Program Name Parser (List Parser) :=
  .read (request.key (some name)) fun found => .pure (found.getD [])

def indexedQuery (request : Request Name) : Program Name Parser (List Parser) :=
  match request.token with
  | .atom name | .node name => findQuery request name
  | .other => .pure []
  | .ident name =>
      match request.behavior with
      | .default => findQuery request request.identKind
      | .symbol => .read (request.key (some name)) fun found =>
          match found with
          | some parsers => .pure parsers
          | none => findQuery request request.identKind
      | .both => .read (request.key (some name)) fun found =>
          match found with
          | none => findQuery request request.identKind
          | some parsers =>
              if name = request.identKind then .pure parsers
              else ReadOnlyQuery.bind (findQuery request request.identKind)
                fun identifiers => .pure (parsers ++ identifiers)

def query (request : Request Name) : Program Name Parser (List Parser) :=
  ReadOnlyQuery.bind (indexedQuery request) fun keyed =>
    .read (request.key none) fun found =>
      .pure (match request.phase with
        | .leading => found.getD [] ++ keyed
        | .trailing => keyed ++ found.getD [])

theorem indexedQuery_exact (store : Store Name Parser) (request : Request Name) :
    (ReadOnlyQuery.run store (indexedQuery request)).answer = indexed store request := by
  cases token : request.token with
  | atom name | node name | other => simp [indexedQuery, indexed, findQuery, token, ReadOnlyQuery.run]
  | ident name =>
      cases behavior : request.behavior with
      | default => simp [indexedQuery, indexed, findQuery, token, behavior, ReadOnlyQuery.run]
      | symbol =>
          cases found : store (request.key (some name)) <;>
            simp [indexedQuery, indexed, findQuery, token, behavior, found, ReadOnlyQuery.run]
      | both =>
          cases found : store (request.key (some name)) with
          | none => simp [indexedQuery, indexed, findQuery, token, behavior, found, ReadOnlyQuery.run]
          | some parsers =>
              by_cases same : name = request.identKind
              · subst name
                simp [indexedQuery, indexed, token, behavior, found, ReadOnlyQuery.run]
              · simp [indexedQuery, indexed, findQuery, token, behavior, found, same,
                  ReadOnlyQuery.run, ReadOnlyQuery.run_bind]

theorem query_exact (store : Store Name Parser) (request : Request Name) :
    (ReadOnlyQuery.run store (query request)).answer = dispatch store request := by
  simp [query, dispatch, ReadOnlyQuery.run_bind, ReadOnlyQuery.run, indexedQuery_exact]

theorem validated_dispatch [DecidableEq Parser] (before after : Store Name Parser)
    (request : Request Name)
    (valid : ReadOnlyQuery.checkReads after (ReadOnlyQuery.run before (query request)).reads = true) :
    dispatch after request = dispatch before request := by
  simpa only [query_exact] using ReadOnlyQuery.validated_answer before after (query request) valid

/-- The portable dispatch algorithm is fixed. Release/profile metadata still
participates in validation so independently versioned adapters cannot mix entries. -/
def family (_profile : Profile) (request : Request Name) : Program Name Parser (List Parser) :=
  query request

abbrev Entry (Name Parser : Type) := ReadCertifiedQueryReuse.Entry Profile
  (Request Name) (Key Name) (Option (List Parser)) (List Parser)

def capture (profile : Profile) (store : Store Name Parser) (request : Request Name) : Entry Name Parser :=
  ReadCertifiedQueryReuse.populate family profile request store

def reuse [DecidableEq Parser] (profile : Profile) (store : Store Name Parser)
    (request : Request Name) (entry : Entry Name Parser) : List Parser × Nat :=
  ReadCertifiedQueryReuse.reuse family profile request store entry

theorem reuse_exact [DecidableEq Parser] (oldProfile profile : Profile)
    (before after : Store Name Parser) (oldRequest request : Request Name) :
    (reuse profile after request (capture oldProfile before oldRequest)).1 = dispatch after request := by
  exact (ReadCertifiedQueryReuse.reuse_exact family profile request after _
    (ReadCertifiedQueryReuse.populate_recorded family oldProfile oldRequest before)).trans
      (query_exact after request)

theorem profile_change_recomputes [DecidableEq Parser]
    (oldProfile profile : Profile) (different : oldProfile ≠ profile)
    (before after : Store Name Parser) (request : Request Name) :
    (reuse profile after request (capture oldProfile before request)).2 = 1 := by
  apply ReadCertifiedQueryReuse.rejected_executes_query
  simp [ReadCertifiedQueryReuse.admissible, capture, ReadCertifiedQueryReuse.populate,
    ReadCertifiedQueryReuse.Supported.populate, ReadCertifiedQueryReuse.programObserver, different]

/-- Source registrations are already in their declared candidate order. -/
def catalogue (entries : List (Key Name × Parser)) (key : Key Name) : List Parser :=
  entries.filterMap fun entry => if key = entry.1 then some entry.2 else none

def find (key : Key Name) : List (Key Name × List Parser) → Option (List Parser)
  | [] => none
  | (stored, values) :: rest => if key = stored then some values else find key rest

/-- A finite reference index; a physical hash/trie implementation owes a
separate refinement. Older bucket versions share their tails. -/
def build : List (Key Name × Parser) → List (Key Name × List Parser)
  | [] => []
  | (key, parser) :: rest =>
      let table := build rest
      (key, parser :: (find key table).getD []) :: table

theorem find_build (entries : List (Key Name × Parser)) (key : Key Name) :
    (find key (build entries)).getD [] = catalogue entries key := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, parser⟩
      by_cases same : key = stored
      · subst stored
        simp [build, find, catalogue] at *
        exact ih
      · simp [build, find, catalogue, same] at *
        exact ih

theorem find_build_none_iff (entries : List (Key Name × Parser)) (key : Key Name) :
    find key (build entries) = none ↔ catalogue entries key = [] := by
  induction entries with
  | nil => simp [build, find, catalogue]
  | cons entry rest ih =>
      rcases entry with ⟨stored, parser⟩
      by_cases same : key = stored
      · subst stored
        simp [build, find, catalogue]
      · simpa [build, find, catalogue, same] using ih

/-- Exact indexed dispatch, with absence distinct from a present bucket. -/
theorem find_build_exact (entries : List (Key Name × Parser)) (key : Key Name) :
    find key (build entries) =
      if catalogue entries key = [] then none else some (catalogue entries key) := by
  cases found : find key (build entries) with
  | none => simp [(find_build_none_iff entries key).mp found]
  | some values =>
      have same : values = catalogue entries key := by simpa [found] using find_build entries key
      have nonempty : catalogue entries key ≠ [] := by
        intro empty
        have := (find_build_none_iff entries key).mpr empty
        simp [found] at this
      simp [nonempty, same]

end Mettapedia.GSLT.Parsing.KeyedParserDispatch
