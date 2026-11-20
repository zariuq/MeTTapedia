import Mettapedia.Ownership.Geometry

/-!
# Permission states and their invariant

Plans name logical allocations and loans. Names can be reused after every
permission to that lifetime has ended, as for a local allocation in a loop;
they are not numerical C addresses. The source projection, C ABI layout and
native contracts remain separate implementation obligations.

A state holds the live loans, the allocations, the release authorities and the
result, transfer and suspension records of one function. `Valid` is the
separation invariant, stated independently of any checker; `validB` decides it
and `validB_iff` says so.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

inductive Origin where
  | local | input | heap | static
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

structure Allocation where
  root : Nat
  count : Nat
  origin : Origin
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def Allocation.region (a : Allocation) : Region := ⟨a.root, 0, a.count⟩

inductive TransferKind where
  | owned | released
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

/-- A consumed owner remains accounted for until its native call takes it.
Nested argument calls may consume their own receipts, never another call's. -/
structure Transfer where
  holder : Nat
  family : Nat
  region : Region
  kind : TransferKind
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

/-- The storage of the whole input rooted at `root` was released to a native
call of `family` to be replaced: nothing reaches the input until fresh storage
of that family is stored back. A reallocation's source is `restorable`: when
that call's result is null nothing moved, and the old storage remains. -/
structure Suspension where
  root : Nat
  family : Nat
  restorable : Bool
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def suspendedRoot (suspended : List Suspension) (root : Nat) : Bool :=
  suspended.any fun x => x.root == root

structure FieldResult where
  key : Nat
  region : Option Region
  writing : Bool
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

inductive Argument where
  | value
  | loan (id : Nat)
  | maybe (id : Nat)
  | owned (holder : Nat)
  | released (holder : Nat)
  | null
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

structure State where
  loans : List Loan
  allocations : List Allocation
  authorities : List ReleaseAuthority := []
  result : Option Region := none
  ownedResult : Option Nat := none
  nullResult : Bool := false
  resultWriting : Bool := false
  transfers : List Transfer := []
  fieldResults : List FieldResult := []
  recordResults : List FieldResult := []
  recordOwners : List (Nat × Nat) := []
  suspended : List Suspension := []
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def Compatible (a b : Loan) : Prop :=
  a.id ∈ b.ancestors ∨ b.id ∈ a.ancestors ∨ a.region.Disjoint b.region ∨
    a.mode = .shared ∧ b.mode = .shared

instance (a b : Loan) : Decidable (Compatible a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∧ _))

/-- The separation invariant of a permission state, stated independently of the
executable checker rather than as the set of states it reaches. -/
structure Valid (s : State) : Prop where
  /-- No two live loans share an id. -/
  loanIds : (s.loans.map LoanOf.id).Nodup
  /-- No two allocations share a root. -/
  allocationRoots : (s.allocations.map Allocation.root).Nodup
  /-- At most one release authority per root. -/
  authorityRoots : (s.authorities.map ReleaseAuthority.root).Nodup
  /-- A loan's ancestors were lent before it. -/
  ordered : Ordered s.loans
  /-- Every loan lies inside an allocation. -/
  covered : ∀ l ∈ s.loans, ∃ a ∈ s.allocations, a.region.Contains l.region
  /-- Every ancestor of a loan is live, contains it, and is shared only if it is. -/
  ancestorsLive : ∀ l ∈ s.loans, ∀ id ∈ l.ancestors, ∃ p ∈ s.loans,
    p.id = id ∧ p.region.Contains l.region ∧ (p.mode = .shared → l.mode = .shared)
  /-- Two distinct live loans are nested, disjoint, or both shared. -/
  compatible : ∀ a ∈ s.loans, ∀ b ∈ s.loans, a.id ≠ b.id → Compatible a b
  /-- A release authority names a live heap allocation. -/
  authoritiesHeap : ∀ token ∈ s.authorities, ∃ a ∈ s.allocations,
    a.root = token.root ∧ a.origin = .heap
  /-- No holder holds two release authorities. -/
  holders : (s.authorities.map ReleaseAuthority.holder).Nodup

def uniqueIds : List Nat → Bool
  | [] => true
  | id :: rest => !rest.contains id && uniqueIds rest

theorem uniqueIds_iff (ids : List Nat) : uniqueIds ids = true ↔ ids.Nodup := by
  induction ids with
  | nil => simp [uniqueIds]
  | cons id rest ih => simp [uniqueIds, ih]

def compatibleB (a b : Loan) : Bool :=
  b.ancestors.contains a.id || a.ancestors.contains b.id || disjointB a.region b.region ||
    (a.mode == .shared && b.mode == .shared)

theorem compatibleB_iff (a b : Loan) : compatibleB a b = true ↔ Compatible a b := by
  simp [compatibleB, Compatible, disjointB_iff, or_assoc]

def pairB (a b : Loan) : Bool := a.id == b.id || compatibleB a b

theorem pairB_iff (a b : Loan) : pairB a b = true ↔ (a.id ≠ b.id → Compatible a b) := by
  by_cases same : a.id = b.id <;> simp [pairB, same, compatibleB_iff]

/-- Boolean reflection avoids constructing bounded-quantifier proofs during
each invariant decision. The equivalence below justifies the entire check. -/
def validB (s : State) : Bool :=
  uniqueIds (s.loans.map LoanOf.id) && uniqueIds (s.allocations.map Allocation.root) &&
  uniqueIds (s.authorities.map ReleaseAuthority.root) &&
  s.loans.all (fun l => l.ancestors.all (fun parent => parent < l.id)) &&
  s.loans.all (fun l => s.allocations.any (fun a => containsB a.region l.region)) &&
  s.loans.all (fun l => l.ancestors.all (fun id => s.loans.any (fun p =>
    p.id == id && containsB p.region l.region && allowsB p.mode l.mode))) &&
  s.loans.all (fun a => s.loans.all (fun b => pairB a b)) &&
  s.authorities.all (fun token => s.allocations.any (fun a =>
    a.root == token.root && a.origin == .heap)) &&
  uniqueIds (s.authorities.map ReleaseAuthority.holder)

theorem valid_iff (s : State) : Valid s ↔
    (s.loans.map LoanOf.id).Nodup ∧ (s.allocations.map Allocation.root).Nodup ∧
    (s.authorities.map ReleaseAuthority.root).Nodup ∧ Ordered s.loans ∧
    (∀ l ∈ s.loans, ∃ a ∈ s.allocations, a.region.Contains l.region) ∧
    (∀ l ∈ s.loans, ∀ id ∈ l.ancestors, ∃ p ∈ s.loans,
      p.id = id ∧ p.region.Contains l.region ∧ (p.mode = .shared → l.mode = .shared)) ∧
    (∀ a ∈ s.loans, ∀ b ∈ s.loans, a.id ≠ b.id → Compatible a b) ∧
    (∀ token ∈ s.authorities, ∃ a ∈ s.allocations, a.root = token.root ∧ a.origin = .heap) ∧
    (s.authorities.map ReleaseAuthority.holder).Nodup :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
   fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

theorem validB_iff (s : State) : validB s = true ↔ Valid s := by
  rw [valid_iff]
  simp [validB, Ordered, OrderedIn, List.all_eq_true, List.any_eq_true,
    uniqueIds_iff, containsB_iff, allowsB_iff, pairB_iff, and_assoc]

instance (s : State) : Decidable (Valid s) := decidable_of_iff _ (validB_iff s)

/-- The invariant reads only loans, allocations and release authorities. -/
theorem valid_congr {s t : State} (loans : s.loans = t.loans)
    (allocations : s.allocations = t.allocations) (authorities : s.authorities = t.authorities) :
    Valid s ↔ Valid t := by
  rw [valid_iff, valid_iff, loans, allocations, authorities]

/-! ## Deciders on loans

Each permission a step asks for, decided by a Bool function with its meaning as
a proposition. -/

/-- Decides `Access`: a live loan `id` contains `part` and lends it for writing
if the access writes, and every other loan overlapping `part` is its ancestor
or, for a read, shared. -/
def accessB (loans : List Loan) (id : Nat) (part : Region) (writing : Bool) : Bool :=
  loans.any fun l => l.id == id && containsB l.region part && (!writing || l.mode == .exclusive) &&
    loans.all fun other => other.id == id || disjointB part other.region ||
      l.ancestors.contains other.id || (!writing && other.mode == .shared)

theorem accessB_iff (loans : List Loan) (id : Nat) (part : Region) (writing : Bool) :
    accessB loans id part writing = true ↔ Access loans id part writing := by
  simp only [accessB, Access, AccessIn, regionGeometry, List.any_eq_true, List.all_eq_true,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, containsB_iff, disjointB_iff,
    List.contains_iff_mem, Bool.not_eq_true', and_assoc, or_assoc]
  refine exists_congr fun l => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr ?_ ?_
  · cases writing <;> simp
  · refine forall_congr' fun other => forall_congr' fun _ => ?_
    by_cases same : other.id = id <;> by_cases apart : part.Disjoint other.region <;>
      simp [same, apart]

/-- Decides `MayEnd`: the loan is live and no live loan descends from it. -/
def mayEndB (loans : List Loan) (id : Nat) : Bool :=
  loans.any (fun l => l.id == id) && loans.all (fun l => !l.ancestors.contains id)

theorem mayEndB_iff (loans : List Loan) (id : Nat) : mayEndB loans id = true ↔ MayEnd loans id := by
  simp [mayEndB, MayEnd, List.any_eq_true, List.all_eq_true]

/-- Decides `MayRelease`: the actor holds the authority for the family, and no
live loan lies in its storage. -/
def mayReleaseB (loans : List Loan) (authority : ReleaseAuthority) (actor family : Nat) : Bool :=
  actor == authority.holder && family == authority.family &&
    loans.all (fun l => l.region.root != authority.root)

theorem mayReleaseB_iff (loans : List Loan) (authority : ReleaseAuthority) (actor family : Nat) :
    mayReleaseB loans authority actor family = true ↔ MayRelease loans authority actor family := by
  simp [mayReleaseB, MayRelease, List.all_eq_true, and_assoc]

def initial : State :=
  { loans := [⟨0, ⟨0, 0, 18446744073709551615⟩, .shared, []⟩]
    allocations := [⟨0, 18446744073709551615, .static⟩] }

theorem initial_valid : Valid initial := by decide

end Mettapedia.Ownership
