import Mathlib.Data.Prod.Lex
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Explicit selection over parser attempts

The score is lexicographic: endpoint, success over error at that endpoint,
then priority. All exact ties remain in source order. In particular a farther
failure can beat a shorter success. This isolates the score/choice boundary;
Lean's diagnostic merging, recovery and syntax-stack transitions are separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserAttemptSelection

structure Attempt (Payload : Type) where
  stop : Nat
  succeeded : Bool
  priority : Nat
  payload : Payload
  deriving DecidableEq, Repr

abbrev Score := Nat ×ₗ Nat ×ₗ Nat

def score {Payload : Type} (attempt : Attempt Payload) : Score :=
  toLex (attempt.stop, toLex (if attempt.succeeded then 1 else 0, attempt.priority))

/-- A direct specification of the complete winning list. -/
def select {Payload : Type} (attempts : List (Attempt Payload)) : List (Attempt Payload) :=
  attempts.filter fun candidate => attempts.all fun other => decide (score other ≤ score candidate)

theorem mem_select_iff {Payload : Type} (attempts : List (Attempt Payload)) (candidate : Attempt Payload) :
    candidate ∈ select attempts ↔
      candidate ∈ attempts ∧ ∀ other ∈ attempts, score other ≤ score candidate := by
  simp [select]

theorem selected_sublist {Payload : Type} (attempts : List (Attempt Payload)) :
    List.Sublist (select attempts) attempts := List.filter_sublist

theorem no_invented_attempt {Payload : Type} (attempts : List (Attempt Payload))
    (candidate : Attempt Payload) (selected : candidate ∈ select attempts) : candidate ∈ attempts :=
  ((mem_select_iff attempts candidate).mp selected).1

theorem farther_dominates {Payload : Type} (first second : Attempt Payload)
    (farther : first.stop < second.stop) : score first < score second := by
  exact (Prod.Lex.toLex_lt_toLex).mpr (Or.inl farther)

/-- Any adaptive attempt-producing computation retains the dependencies of
losing and failed attempts as well as those of the winners. -/
def selectedQuery {Key Value Payload : Type}
    (query : Mettapedia.Machines.ReadOnlyQuery.Program Key Value (List (Attempt Payload))) :
    Mettapedia.Machines.ReadOnlyQuery.Program Key Value (List (Attempt Payload)) :=
  Mettapedia.Machines.ReadOnlyQuery.bind query fun attempts => .pure (select attempts)

theorem selectedQuery_reads {Key Value Payload : Type}
    (store : Key → Value)
    (query : Mettapedia.Machines.ReadOnlyQuery.Program Key Value (List (Attempt Payload))) :
    (Mettapedia.Machines.ReadOnlyQuery.run store (selectedQuery query)).reads =
      (Mettapedia.Machines.ReadOnlyQuery.run store query).reads := by
  simp [selectedQuery, Mettapedia.Machines.ReadOnlyQuery.run_bind,
    Mettapedia.Machines.ReadOnlyQuery.run]

theorem selection_preserved {Key Value Payload : Type} [DecidableEq Value]
    (before after : Key → Value)
    (query : Mettapedia.Machines.ReadOnlyQuery.Program Key Value (List (Attempt Payload)))
    (valid : Mettapedia.Machines.ReadOnlyQuery.checkReads after
      (Mettapedia.Machines.ReadOnlyQuery.run before query).reads = true) :
    select (Mettapedia.Machines.ReadOnlyQuery.run after query).answer =
      select (Mettapedia.Machines.ReadOnlyQuery.run before query).answer := by
  rw [Mettapedia.Machines.ReadOnlyQuery.validated_answer before after query valid]

end Mettapedia.GSLT.Parsing.ParserAttemptSelection
