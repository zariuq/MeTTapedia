import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Ordered coefficients with shared physical factors

A ledger records factors by physical identity, dependency and coefficient.
Merging two branches keeps their identical inherited prefix once and then
appends disjoint fresh suffixes in logical left-before-right order. A repeated
identity outside the shared prefix, including a conflicting value or dependency,
is refused. Equal values with different identities remain separate factors.

The construction is independent of an execution language or coefficient
interpreter. Its denotation needs a monoid, not commutative multiplication.
Ownership and validity of a concrete memory representation are separate runtime
correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SharedCoefficientLedger

universe uId uDependency uValue

structure Factor (Identity : Type uId) (Dependency : Type uDependency) (V : Type uValue) where
  identity : Identity
  dependency : Dependency
  coefficient : V
  deriving DecidableEq, Repr

variable {Identity : Type uId} {Dependency : Type uDependency} {V : Type uValue}

abbrev Ledger (Identity : Type uId) (Dependency : Type uDependency) (V : Type uValue) :=
  List (Factor Identity Dependency V)

def identities (ledger : Ledger Identity Dependency V) : List Identity :=
  ledger.map Factor.identity

/-- Each physical factor occurs at most once within one execution world. -/
def Valid (ledger : Ledger Identity Dependency V) : Prop := (identities ledger).Nodup

instance [DecidableEq Identity] (ledger : Ledger Identity Dependency V) :
    Decidable (Valid ledger) := inferInstanceAs (Decidable (identities ledger).Nodup)

structure PrefixSplit (Identity : Type uId) (Dependency : Type uDependency) (V : Type uValue) where
  shared : Ledger Identity Dependency V
  leftFresh : Ledger Identity Dependency V
  rightFresh : Ledger Identity Dependency V
  deriving Repr

/-- Compare complete factors, so identity agreement cannot conceal a changed
coefficient or dependency. -/
def splitPrefix [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V] :
    Ledger Identity Dependency V → Ledger Identity Dependency V →
      PrefixSplit Identity Dependency V
  | first :: left, second :: right =>
      if first = second then
        let rest := splitPrefix left right
        ⟨first :: rest.shared, rest.leftFresh, rest.rightFresh⟩
      else ⟨[], first :: left, second :: right⟩
  | left, right => ⟨[], left, right⟩

theorem splitPrefix_reconstruct [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) :
    (splitPrefix left right).shared ++ (splitPrefix left right).leftFresh = left ∧
      (splitPrefix left right).shared ++ (splitPrefix left right).rightFresh = right := by
  induction left generalizing right with
  | nil => simp [splitPrefix]
  | cons first rest ih =>
      cases right with
      | nil => simp [splitPrefix]
      | cons second later =>
          by_cases same : first = second
          · subst second
            simpa [splitPrefix] using ih later
          · simp [splitPrefix, same]

def PrefixSplit.ordered (parts : PrefixSplit Identity Dependency V) : Ledger Identity Dependency V :=
  parts.shared ++ parts.leftFresh ++ parts.rightFresh

/-- The caller's logical branch order is explicit; completion order is not an input. -/
def merge? [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) : Option (Ledger Identity Dependency V) :=
  let merged := (splitPrefix left right).ordered
  if Valid merged then some merged else none

theorem merge_accepted_iff [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right merged : Ledger Identity Dependency V) :
    merge? left right = some merged ↔
      merged = (splitPrefix left right).ordered ∧ Valid merged := by
  dsimp [merge?]
  by_cases accepted : Valid (splitPrefix left right).ordered <;> simp_all [eq_comm]

theorem merge_valid [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) : Valid merged :=
  ((merge_accepted_iff left right merged).mp accepted).2

/-- The stateful API installs a merged ledger only after successful validation. -/
def commitMerge [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) : Ledger Identity Dependency V × Bool :=
  match merge? left right with
  | none => (left, false)
  | some merged => (merged, true)

theorem refused_merge_retains_state [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    (left right : Ledger Identity Dependency V) (refused : merge? left right = none) :
    commitMerge left right = (left, false) := by simp [commitMerge, refused]

theorem merge_contains_left [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) : ∀ factor ∈ left, factor ∈ merged := by
  obtain ⟨rfl, _⟩ := (merge_accepted_iff left right merged).mp accepted
  intro factor present
  rw [← (splitPrefix_reconstruct left right).1] at present
  simp only [PrefixSplit.ordered, List.mem_append] at *
  tauto

theorem merge_contains_right [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) : ∀ factor ∈ right, factor ∈ merged := by
  obtain ⟨rfl, _⟩ := (merge_accepted_iff left right merged).mp accepted
  intro factor present
  rw [← (splitPrefix_reconstruct left right).2] at present
  simp only [PrefixSplit.ordered, List.mem_append] at *
  tauto

theorem merge_no_new_factor [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) :
    ∀ factor ∈ merged, factor ∈ left ∨ factor ∈ right := by
  obtain ⟨rfl, _⟩ := (merge_accepted_iff left right merged).mp accepted
  intro factor present
  rcases List.mem_append.mp present with fromLeft | fromRight
  · exact Or.inl ((splitPrefix_reconstruct left right).1 ▸ fromLeft)
  · exact Or.inr ((splitPrefix_reconstruct left right).2 ▸
      List.mem_append.mpr (Or.inr fromRight))

/-- Chronological appending refuses a previously charged physical identity. -/
def append? [DecidableEq Identity] (ledger : Ledger Identity Dependency V)
    (factor : Factor Identity Dependency V) : Option (Ledger Identity Dependency V) :=
  if factor.identity ∈ identities ledger then none else some (ledger ++ [factor])

theorem append_valid [DecidableEq Identity]
    {ledger next : Ledger Identity Dependency V} {factor : Factor Identity Dependency V}
    (valid : Valid ledger) (accepted : append? ledger factor = some next) : Valid next := by
  unfold append? at accepted
  split at accepted
  · simp at accepted
  · cases accepted
    simpa [Valid, identities, List.nodup_append] using
      And.intro valid (show (identities ledger).Disjoint [factor.identity] from by simp_all)

def denote [Monoid V] (ledger : Ledger Identity Dependency V) : V :=
  (ledger.map Factor.coefficient).prod

theorem denote_append [Monoid V] (left right : Ledger Identity Dependency V) :
    denote (left ++ right) = denote left * denote right := by
  simp [denote, List.prod_append]

/-- Shared work is interpreted once, before both logically ordered suffixes. -/
theorem merge_denotation [Monoid V] [DecidableEq Identity] [DecidableEq Dependency] [DecidableEq V]
    {left right merged : Ledger Identity Dependency V}
    (accepted : merge? left right = some merged) :
    denote merged = denote (splitPrefix left right).shared *
      denote (splitPrefix left right).leftFresh * denote (splitPrefix left right).rightFresh := by
  rw [((merge_accepted_iff left right merged).mp accepted).1, PrefixSplit.ordered]
  rw [denote_append, denote_append]

end Mettapedia.Algebra.SharedCoefficientLedger
