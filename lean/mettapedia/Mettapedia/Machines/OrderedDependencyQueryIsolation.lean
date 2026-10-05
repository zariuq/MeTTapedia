import Mettapedia.Machines.OrderedDependencyStore
import Mettapedia.GSLT.Dynamics.JoinAggregation

/-!
# Query-specific isolation of native module reads

The outer-shape checker rejects imported candidates before local indexes or
aggregates are used. Its result concerns one query, not the whole module. This
model separates the conservative C-shaped Boolean loop from an independent
possible-unification predicate and ordered collection of source segments.

The checker preserves the entire ordered candidate list, including duplicates.
Consequently any subsequent field matcher or observer sees the same candidates.
The two- and three-relation consequences compose this with checked join laws.
Cached admission is proved along the actual finite-store notification algorithm;
the key includes the query shape, reader, session, generation and revision.

This is an outer-candidate and finite-store model. It does not establish the C
pointer, allocator, passive-comparison or concurrent read-window obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyQueryIsolation

open OrderedDependencyStore
open Mettapedia.GSLT.Dynamics.JoinAggregation

universe u

inductive QueryShape where
  | symbol (head : Nat)
  | expression (head arity : Nat)
  deriving DecidableEq

inductive OuterShape where
  | scalar
  | symbol (head : Nat)
  | expression (head : Option Nat) (arity : Nat)
  | variable
  | extensible
  deriving DecidableEq

structure Record (Value : Type u) where
  shape : OuterShape
  value : Value
  deriving DecidableEq

/-- Independent outer unification: an unknown head can unify with any symbol
head of the same arity. Extensible payloads cannot be refuted by this layer. -/
def Compatible (query : QueryShape) (row : OuterShape) : Prop :=
  match query, row with
  | _, .variable | _, .extensible => True
  | .symbol expected, .symbol actual => actual = expected
  | .expression expected length, .expression actual width =>
      width = length ∧ (actual = none ∨ actual = some expected)
  | _, _ => False

instance compatibleDecidable (query : QueryShape) (row : OuterShape) :
    Decidable (Compatible query row) := by
  cases query <;> cases row <;> simp only [Compatible] <;> infer_instance

/-- The native checker tests the arity before a fixed head; unknown heads and
extensible representations require the composed route. -/
def mayMatch (query : QueryShape) (row : OuterShape) : Bool :=
  match row with
  | .variable | .extensible => true
  | .scalar => false
  | .symbol actual =>
      match query with
      | .symbol expected => actual == expected
      | .expression _ _ => false
  | .expression actual width =>
      match query with
      | .symbol _ => false
      | .expression expected length =>
          if width != length then false else
            match actual with
            | none => true
            | some head => head == expected

theorem mayMatch_iff (query : QueryShape) (row : OuterShape) :
    mayMatch query row = true ↔ Compatible query row := by
  cases query <;> cases row <;> simp [Compatible, mayMatch]
  cases ‹Option Nat› <;> simp

variable {Value : Type u} {size : Nat}

def select (shape : QueryShape) (row : Record Value) : Option (Record Value) :=
  if Compatible shape row.shape then some row else none

theorem select_none_of_rejected (shape : QueryShape) (row : Record Value)
    (rejected : mayMatch shape row.shape = false) : select shape row = none := by
  have absent : ¬ Compatible shape row.shape := by
    intro compatible
    have accepted := (mayMatch_iff shape row.shape).mpr compatible
    simp [rejected] at accepted
  simp [select, absent]

def checkSegment (shape : QueryShape) (rows : List (Record Value)) : Bool :=
  rows.all fun row => !(mayMatch shape row.shape)

theorem checked_segment_empty (shape : QueryShape) (rows : List (Record Value))
    (checked : checkSegment shape rows = true) : rows.filterMap (select shape) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro row included
  apply select_none_of_rejected
  have rejected := (List.all_eq_true.mp checked) row included
  simpa using rejected

/-- Every imported segment is checked, including empty sources. -/
def checkOwn (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) : Bool :=
  (segments s reader).2.all fun source => checkSegment shape source.2

def own (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) : List (Record Value) :=
  (s.members reader).own.filterMap (select shape)

def query (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) : List (Record Value) :=
  (OrderedDependencyStore.query s reader).filterMap (select shape)

theorem checked_imported_empty (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) (checked : checkOwn s reader shape = true) :
    ((s.members reader).deps.flatMap fun source =>
      (s.members source).own.filterMap (select shape)) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro source included
  apply checked_segment_empty
  exact (List.all_eq_true.mp checked) (source, (s.members source).own)
    (List.mem_map.mpr ⟨source, included, rfl⟩)

theorem checked_query_eq_own (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) (checked : checkOwn s reader shape = true) :
    query s reader shape = own s reader shape := by
  simp only [query, OrderedDependencyStore.query_eq_view, view,
    List.filterMap_append, List.filterMap_flatMap]
  rw [checked_imported_empty s reader shape checked, List.append_nil]
  rfl

theorem checked_observation (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) (checked : checkOwn s reader shape = true)
    {Answer : Type*} (observe : List (Record Value) → Answer) :
    observe (query s reader shape) = observe (own s reader shape) := by
  rw [checked_query_eq_own s reader shape checked]

structure Certificate (size : Nat) where
  shape : QueryShape
  read : ReadStamp size
  ownOnly : Bool

def capture (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) : Certificate size :=
  ⟨shape, readStamp s reader, checkOwn s reader shape⟩

def validate (s : Store (Record Value) size) (reader : Fin size)
    (shape : QueryShape) (certificate : Certificate size) : Bool :=
  certificate.ownOnly && decide
    (certificate.shape = shape ∧ certificate.read = readStamp s reader)

theorem checkOwn_of_revision_eq (s : Store (Record Value) size)
    (holds : ObserverInvariant s) (actions : List (Action (Record Value) size))
    (reader : Fin size) (shape : QueryShape)
    (unchanged : ((execute s actions).members reader).revision =
      (s.members reader).revision) :
    checkOwn (execute s actions) reader shape = checkOwn s reader shape := by
  unfold checkOwn
  rw [execute_segments_of_revision_eq s holds actions reader unchanged]

theorem validated_isolation (s : Store (Record Value) size)
    (holds : ObserverInvariant s) (actions : List (Action (Record Value) size))
    (reader : Fin size) (shape : QueryShape)
    (checked : validate (execute s actions) reader shape (capture s reader shape) = true) :
    checkOwn (execute s actions) reader shape = true := by
  have evidence : checkOwn s reader shape = true ∧
      readStamp s reader = readStamp (execute s actions) reader := by
    simpa [validate, capture] using checked
  have revision := congrArg ReadStamp.revision evidence.2
  simp only [readStamp] at revision
  rw [checkOwn_of_revision_eq s holds actions reader shape revision.symm]
  exact evidence.1

theorem validated_query_eq_own (s : Store (Record Value) size)
    (holds : ObserverInvariant s) (actions : List (Action (Record Value) size))
    (reader : Fin size) (shape : QueryShape)
    (checked : validate (execute s actions) reader shape (capture s reader shape) = true) :
    query (execute s actions) reader shape = own (execute s actions) reader shape :=
  checked_query_eq_own _ reader shape
    (validated_isolation s holds actions reader shape checked)

section Aggregation

variable {X Y Z W : Type*} [DecidableEq Y]

theorem isolated_join (s : Store (Record Value) size) (reader : Fin size)
    (left right : QueryShape)
    (checkedLeft : checkOwn s reader left = true)
    (checkedRight : checkOwn s reader right = true)
    (extractLeft : Record Value → Option (X × Y))
    (extractRight : Record Value → Option (Y × Z)) :
    join ((query s reader left).filterMap extractLeft)
      ((query s reader right).filterMap extractRight) =
    join ((own s reader left).filterMap extractLeft)
      ((own s reader right).filterMap extractRight) := by
  rw [checked_query_eq_own s reader left checkedLeft,
    checked_query_eq_own s reader right checkedRight]

/-- The local count computes the composed bag size without constructing it. -/
theorem isolated_join_count (s : Store (Record Value) size) (reader : Fin size)
    (left right : QueryShape)
    (checkedLeft : checkOwn s reader left = true)
    (checkedRight : checkOwn s reader right = true)
    (extractLeft : Record Value → Option (X × Y))
    (extractRight : Record Value → Option (Y × Z)) :
    (join ((query s reader left).filterMap extractLeft)
      ((query s reader right).filterMap extractRight)).length =
    (((own s reader left).filterMap extractLeft).map fun row =>
      ((own s reader right).filterMap extractRight).countP fun other =>
        other.1 = row.2).sum := by
  rw [isolated_join s reader left right checkedLeft checkedRight extractLeft extractRight]
  exact length_join_eq_sum_countP _ _

theorem isolated_join_sum (s : Store (Record Value) size) (reader : Fin size)
    (left right : QueryShape)
    (checkedLeft : checkOwn s reader left = true)
    (checkedRight : checkOwn s reader right = true)
    (extractLeft : Record Value → Option (X × Y))
    (extractRight : Record Value → Option (Y × Z)) (column : X × Y → Int) :
    ((join ((query s reader left).filterMap extractLeft)
      ((query s reader right).filterMap extractRight)).map
      fun row => column (row.1, row.2.1)).sum =
    ∑ key ∈ (((own s reader left).filterMap extractLeft).map Prod.snd).toFinset,
      groupSum Prod.snd column ((own s reader left).filterMap extractLeft) key *
        ((((own s reader right).filterMap extractRight).countP
          fun row => row.1 = key : Nat) : Int) := by
  rw [isolated_join s reader left right checkedLeft checkedRight extractLeft extractRight]
  exact sum_join_column _ _ column

variable [DecidableEq Z]

theorem isolated_path (s : Store (Record Value) size) (reader : Fin size)
    (left middle right : QueryShape)
    (checkedLeft : checkOwn s reader left = true)
    (checkedMiddle : checkOwn s reader middle = true)
    (checkedRight : checkOwn s reader right = true)
    (extractLeft : Record Value → Option (X × Y))
    (extractMiddle : Record Value → Option (Y × Z))
    (extractRight : Record Value → Option (Z × W)) :
    pathJoin ((query s reader left).filterMap extractLeft)
      ((query s reader middle).filterMap extractMiddle)
      ((query s reader right).filterMap extractRight) =
    pathJoin ((own s reader left).filterMap extractLeft)
      ((own s reader middle).filterMap extractMiddle)
      ((own s reader right).filterMap extractRight) := by
  rw [checked_query_eq_own s reader left checkedLeft,
    checked_query_eq_own s reader middle checkedMiddle,
    checked_query_eq_own s reader right checkedRight]

end Aggregation

namespace Controls

def row (head value : Nat) : Record Nat := ⟨.expression (some head) 3, value⟩
def left : QueryShape := .expression 1 3
def right : QueryShape := .expression 2 3
def base : Store (Record Nat) 3 :=
  link (initial 401 fun source =>
    if source = 0 then [row 1 2, row 1 2, row 2 5]
    else if source = 1 then [row 9 7] else []) 0 1

theorem duplicates_survive_irrelevant_import :
    checkOwn base 0 left = true ∧ query base 0 left = [row 1 2, row 1 2] := by decide

def changed : Store (Record Nat) 3 := appendOwn base 1 [row 2 11]

theorem each_query_needs_its_own_check :
    checkOwn changed 0 left = true ∧ checkOwn changed 0 right = false ∧
    query changed 0 right ≠ own changed 0 right := by decide

theorem import_publication_expires_admission :
    validate changed 0 right (capture base 0 right) = false ∧
    query changed 0 right = [row 2 5, row 2 11] := by decide

def omittedNotification : Store (Record Nat) 3 :=
  { changed with members := fun source =>
      { changed.members source with revision := (base.members source).revision } }

theorem omitted_notification_accepts_wrong_local_route :
    validate omittedNotification 0 right (capture base 0 right) = true ∧
    checkOwn omittedNotification 0 right = false ∧
    query omittedNotification 0 right ≠ own omittedNotification 0 right := by decide

theorem shape_is_part_of_admission_key :
    checkOwn changed 0 left = true ∧
    checkRead changed (capture changed 0 left).read = true ∧
    validate changed 0 right (capture changed 0 left) = false ∧
    checkOwn changed 0 right = false := by decide

theorem unknown_heads_and_extensible_rows_are_not_refuted :
    mayMatch left (.expression none 3) = true ∧
    mayMatch left .extensible = true ∧ mayMatch left .variable = true ∧
    mayMatch left (.expression none 4) = false := by decide

end Controls

end Mettapedia.Machines.OrderedDependencyQueryIsolation
