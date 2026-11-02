import Mettapedia.Machines.Resources.StateIndexed
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Bound read certificates

Every dependency is a semantic store coordinate. A directory's membership or
a negative query is one such coordinate, even when no returned row exists.
An overlapping write conservatively forgets a certificate; a separate proof
may establish preservation when the actual written value is unchanged.
Checking a certificate is an observation, not a lease excluding later writes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.Certificates

open Mettapedia.Machines.ReadOnlyQuery

variable {Key Value Answer : Type} [DecidableEq Key]

structure BoundReads (Key Value : Type) where
  allocation : AllocationId
  revision : Revision
  reads : Reads Key Value

def Current (identity : AllocationId) (revision : Revision) (store : Key → Value)
    (certificate : BoundReads Key Value) : Prop :=
  certificate.allocation = identity ∧ certificate.revision = revision ∧
    Agrees store certificate.reads

def Affected (writes : Finset Key) (certificate : BoundReads Key Value) : Prop :=
  ∃ read ∈ certificate.reads, read.1 ∈ writes

instance (writes : Finset Key) (certificate : BoundReads Key Value) :
    Decidable (Affected writes certificate) :=
  inferInstanceAs (Decidable (∃ read ∈ certificate.reads, read.1 ∈ writes))

def forgetAffected (writes : Finset Key) (certificates : List (BoundReads Key Value)) :
    List (BoundReads Key Value) := certificates.filter fun c => !decide (Affected writes c)

/-- Read dependencies suffice to preserve a query's complete observation,
including answer order and multiplicity. -/
theorem disjoint_write_preserves_query (before : Key → Value)
    (program : Program Key Value Answer) (key : Key) (value : Value)
    (untouched : ∀ read ∈ (run before program).reads, read.1 ≠ key) :
    run (Function.update before key value) program = run before program := by
  apply run_eq_of_agrees
  intro read member
  simpa [untouched read member] using run_agrees before program read member

theorem survivor_has_no_written_dependency (writes : Finset Key)
    (certificates : List (BoundReads Key Value)) (certificate : BoundReads Key Value)
    (survived : certificate ∈ forgetAffected writes certificates) :
    ∀ read ∈ certificate.reads, read.1 ∉ writes := by
  have clean : ¬ Affected writes certificate := by
    simpa [forgetAffected] using (List.mem_filter.mp survived).2
  intro read member written
  exact clean ⟨read, member, written⟩

omit [DecidableEq Key] in
theorem changed_incarnation_refuses (old current : AllocationId) (revision : Revision)
    (store : Key → Value) (certificate : BoundReads Key Value)
    (origin : certificate.allocation = old) (different : old ≠ current) :
    ¬ Current current revision store certificate := by
  rintro ⟨identity, _, _⟩
  exact different (origin.symm.trans identity)

omit [DecidableEq Key] in
theorem changed_revision_refuses (identity : AllocationId) (old current : Revision)
    (store : Key → Value) (certificate : BoundReads Key Value)
    (stamp : certificate.revision = old) (different : old ≠ current) :
    ¬ Current identity current store certificate := by
  rintro ⟨_, revision, _⟩
  exact different (stamp.symm.trans revision)

def absent : Program Nat (List Nat) Bool := .read 0 fun rows => .pure rows.isEmpty
def emptyStore : Nat → List Nat := fun _ => []
def insertedStore : Nat → List Nat := Function.update emptyStore 0 [42]

theorem negative_query_has_structural_dependency :
    (run emptyStore absent).reads = [(0, [])] := rfl

theorem insertion_changes_negative_answer :
    (run emptyStore absent).answer = true ∧ (run insertedStore absent).answer = false := by decide

theorem insertion_refuses_old_certificate :
    checkReads insertedStore (run emptyStore absent).reads = false := by decide

theorem overlap_need_not_change_answer :
    run (Function.update emptyStore 0 []) absent = run emptyStore absent := rfl

#print axioms disjoint_write_preserves_query
#print axioms changed_incarnation_refuses
#print axioms insertion_refuses_old_certificate

end Mettapedia.Machines.Resources.Certificates
