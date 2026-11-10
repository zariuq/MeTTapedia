import Mettapedia.Machines.CMemory.Borrowing

/-!
# Admission of allocation-range ownership plans

Plans name logical allocations and loans. Names can be reused after every
permission to that lifetime has ended, as for a local allocation in a loop;
they are not numerical C addresses. The source projection, C ABI layout and
native contracts remain separate implementation obligations.

Unlike a whole-buffer permission, a loan contains a range. Release tokens are
kept separately, so neither a shared nor an exclusive borrow can free a root.
The executable transition checks the independent spatial invariant after each
structural operation. Access and result metadata preserve it by theorem. This
is translation validation: a mistaken native checker cannot
make a malformed permission plan pass kernel admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Ownership

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
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def Compatible (a b : Loan) : Prop :=
  a.id ∈ b.ancestors ∨ b.id ∈ a.ancestors ∨ a.region.Disjoint b.region ∨
    a.mode = .shared ∧ b.mode = .shared

instance (a b : Loan) : Decidable (Compatible a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∧ _))

/-- An independently stated spatial/lifetime invariant, rather than the set of
states reachable from the executable checker. -/
def Valid (s : State) : Prop :=
  (s.loans.map LoanOf.id).Nodup ∧ (s.allocations.map Allocation.root).Nodup ∧
  (s.authorities.map ReleaseAuthority.root).Nodup ∧ Ordered s.loans ∧
  (∀ l ∈ s.loans, ∃ a ∈ s.allocations, a.region.Contains l.region) ∧
  (∀ l ∈ s.loans, ∀ id ∈ l.ancestors, ∃ p ∈ s.loans,
    p.id = id ∧ p.region.Contains l.region ∧
    (p.mode = .shared → l.mode = .shared)) ∧
  (∀ a ∈ s.loans, ∀ b ∈ s.loans, a.id ≠ b.id → Compatible a b) ∧
  (∀ token ∈ s.authorities, ∃ a ∈ s.allocations,
    a.root = token.root ∧ a.origin = .heap) ∧
  (s.authorities.map ReleaseAuthority.holder).Nodup

instance (s : State) : Decidable (Valid s) := by unfold Valid; infer_instance

def uniqueIds : List Nat → Bool
  | [] => true
  | id :: rest => !rest.contains id && uniqueIds rest

theorem uniqueIds_iff (ids : List Nat) : uniqueIds ids = true ↔ ids.Nodup := by
  induction ids with
  | nil => simp [uniqueIds]
  | cons id rest ih => simp [uniqueIds, ih]

def containsB (outer inner : Region) : Bool :=
  outer.root == inner.root && outer.first ≤ inner.first && inner.finish ≤ outer.finish

theorem containsB_iff (outer inner : Region) : containsB outer inner = true ↔ outer.Contains inner := by
  simp [containsB, Region.Contains, and_assoc]

def disjointB (a b : Region) : Bool :=
  a.root != b.root || a.finish ≤ b.first || b.finish ≤ a.first

theorem disjointB_iff (a b : Region) : disjointB a b = true ↔ a.Disjoint b := by
  simp [disjointB, Region.Disjoint, or_assoc]

def allowsB (parent child : Mode) : Bool := parent == .exclusive || child == .shared

theorem allowsB_iff (parent child : Mode) : allowsB parent child = true ↔
    (parent = .shared → child = .shared) := by
  cases parent <;> cases child <;> decide

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

theorem validB_iff (s : State) : validB s = true ↔ Valid s := by
  simp [validB, Valid, Ordered, OrderedIn, List.all_eq_true, List.any_eq_true,
    uniqueIds_iff, containsB_iff, allowsB_iff, pairB_iff, and_assoc]

def initial : State :=
  { loans := [⟨0, ⟨0, 0, 18446744073709551615⟩, .shared, []⟩]
    allocations := [⟨0, 18446744073709551615, .static⟩] }

theorem initial_valid : Valid initial := by decide

inductive Action where
  | root (id count : Nat) (mode : Mode) (origin : Origin) (family : Nat)
  | borrow (id parent : Nat) (region : Region) (mode : Mode)
  | access (id : Nat) (region : Region) (writing : Bool)
  | view (id : Nat) (region : Region) (length : Nat) (writing : Bool)
  | endLoan (id : Nat)
  | move (old fresh : Nat)
  | restrict (id : Nat) (region : Region)
  | release (holder family : Nat)
  | give (holder family : Nat)
  | handoff (holder family : Nat)
  | result (id : Nat) (region : Region) (writing : Bool)
  | nullResult
  | fieldResult (key id : Nat) (region : Region) (writing : Bool)
  | nullFieldResult (key : Nat)
  | recordResult (key id : Nat) (region : Region) (writing : Bool)
  | nullRecordResult (key : Nat)
  | recordGive (key holder family : Nat)
  | invoke (name : String) (arguments : List Argument)
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def require (condition : Bool) : Option Unit := if condition then some () else none

def findLoan (s : State) (id : Nat) : Option Loan := s.loans.find? (fun l => l.id == id)
def eraseLoan (s : State) (id : Nat) : State := { s with loans := endLoan s.loans id }
def fresh (s : State) (id : Nat) : Bool :=
  !(s.loans.any fun l => l.id == id) &&
  !(s.transfers.any fun t => t.holder == id || t.region.root == id)

def transition (s : State) : Action → Option State
  | .root id count mode origin family => do
      require (id != 0 && fresh s id && !(s.allocations.any fun a => a.root == id))
      require ((origin == .heap) == (family != 0))
      pure { s with
        loans := s.loans ++ [⟨id, ⟨id, 0, count⟩, mode, []⟩]
        allocations := s.allocations ++ [⟨id, count, origin⟩]
        authorities := if origin == .heap then s.authorities ++ [⟨id, id, family⟩] else s.authorities }
  | .borrow id parent region mode => do
      let p ← findLoan s parent
      require (fresh s id && parent < id && p.ancestors.all (fun n => n < id))
      require (decide (Access s.loans parent region (mode == .exclusive)))
      pure { s with loans := s.loans ++ [⟨id, region, mode, parent :: p.ancestors⟩] }
  | .access id region writing => do
      require (decide (Access s.loans id region writing))
      pure s
  | .view id region length writing => do
      require (length == region.count && decide (Access s.loans id region writing))
      pure s
  | .endLoan id => do
      require (id != 0 && decide (MayEnd s.loans id))
      let l ← findLoan s id
      let after := eraseLoan s id
      pure { after with allocations := after.allocations.filter fun a =>
        !(a.root == l.region.root && id == a.root && a.origin != .heap) }
  | .move old freshId => do
      let l ← findLoan s old
      require (old != 0 && fresh s freshId && decide (MayEnd s.loans old))
      require (l.ancestors.all fun p => p < freshId)
      require (s.authorities.any fun t => t.holder == old)
      pure { s with loans := (eraseLoan s old).loans ++ [{ l with id := freshId }]
                    authorities := s.authorities.map fun token =>
                      if token.holder == old then token.move freshId else token }
  | .release holder family => do
      let token ← s.authorities.find? (fun a => a.holder == holder)
      require (decide (MayRelease s.loans token holder family))
      let allocation ← s.allocations.find? (fun a => a.root == token.root)
      pure { s with authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    transfers := s.transfers ++ [⟨holder, family, allocation.region, .released⟩] }
  | .restrict id region => do
      let l ← findLoan s id
      require (id != 0 && containsB l.region region && decide (MayEnd s.loans id))
      require (!(s.authorities.any fun token => token.holder == id))
      pure { s with loans := s.loans.map fun loan => if loan.id == id then { loan with region := region } else loan }
  | .give holder family => do
      let token ← s.authorities.find? (fun a => a.holder == holder)
      require (token.family == family && s.ownedResult.isNone && s.result.isNone && !s.nullResult)
      require (decide (MayEnd s.loans holder))
      let l ← findLoan s holder
      require (l.region.root == token.root && l.ancestors.isEmpty)
      pure { s with loans := (eraseLoan s holder).loans
                    authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    ownedResult := some family }
  | .handoff holder family => do
      let token ← s.authorities.find? (fun a => a.holder == holder)
      require (token.family == family)
      require (decide (MayEnd s.loans holder))
      let l ← findLoan s holder
      require (l.region.root == token.root && l.ancestors.isEmpty)
      pure { s with loans := (eraseLoan s holder).loans
                    authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    transfers := s.transfers ++ [⟨holder, family, l.region, .owned⟩] }
  | .result id region writing => do
      require (s.result.isNone && s.ownedResult.isNone && !s.nullResult)
      require (decide (Access s.loans id region writing))
      require (s.allocations.any fun a => a.root == region.root && (a.origin == .input || a.origin == .static))
      pure { s with result := some region, resultWriting := writing }
  | .nullResult => do
      require (s.result.isNone && s.ownedResult.isNone && !s.nullResult)
      pure { s with nullResult := true }
  | .fieldResult key id region writing => do
      require (!(s.fieldResults.any fun r => r.key == key))
      require (decide (Access s.loans id region writing))
      require (s.allocations.any fun a => a.root == region.root && (a.origin == .input || a.origin == .static))
      pure { s with fieldResults := s.fieldResults ++ [⟨key, some region, writing⟩] }
  | .nullFieldResult key => do
      require (!(s.fieldResults.any fun r => r.key == key))
      pure { s with fieldResults := s.fieldResults ++ [⟨key, none, false⟩] }
  | .recordResult key id region writing => do
      require (!(s.recordResults.any fun r => r.key == key))
      require (!(s.recordOwners.any fun r => r.1 == key))
      require (decide (Access s.loans id region writing))
      require (s.allocations.any fun a => a.root == region.root && (a.origin == .input || a.origin == .static))
      pure { s with recordResults := s.recordResults ++ [⟨key, some region, writing⟩] }
  | .nullRecordResult key => do
      require (!(s.recordResults.any fun r => r.key == key))
      require (!(s.recordOwners.any fun r => r.1 == key))
      pure { s with recordResults := s.recordResults ++ [⟨key, none, false⟩] }
  | .recordGive key holder family => do
      require (!(s.recordResults.any fun r => r.key == key) && !(s.recordOwners.any fun r => r.1 == key))
      let token ← s.authorities.find? (fun a => a.holder == holder)
      require (token.family == family)
      require (decide (MayEnd s.loans holder))
      let l ← findLoan s holder
      require (l.region.root == token.root && l.ancestors.isEmpty)
      pure { s with loans := (eraseLoan s holder).loans
                    authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    recordOwners := s.recordOwners ++ [(key, family)] }
  | .invoke name _ => do
      require (!name.isEmpty)
      pure s

def requiresValidation : Action → Bool
  | .access .. | .view .. | .result .. | .nullResult | .fieldResult .. | .nullFieldResult ..
  | .recordResult .. | .nullRecordResult .. | .invoke .. => false
  | _ => true

def apply (s : State) (action : Action) : Option State :=
  (transition s action).bind fun after =>
    if requiresValidation action then
      (require (validB after)).bind fun _ => some after
    else some after

theorem require_some {condition : Bool} (h : require condition = some ()) : condition = true := by
  unfold require at h
  split at h
  · assumption
  · contradiction

theorem apply_transition {s after : State} {a : Action} (h : apply s a = some after) :
    transition s a = some after := by
  obtain ⟨next, step, rest⟩ := Option.bind_eq_some_iff.mp h
  by_cases validates : requiresValidation a = true
  · simp only [validates, ↓reduceIte] at rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    have equal := Option.some.inj same
    subst after
    exact step
  · have metadata : requiresValidation a = false := by cases h : requiresValidation a <;> simp_all
    simp [metadata] at rest
    subst after
    exact step

theorem metadata_preserves_valid {s after : State} {a : Action}
    (metadata : requiresValidation a = false) (h : transition s a = some after)
    (valid : Valid s) : Valid after := by
  cases a <;> simp only [requiresValidation] at metadata <;> try contradiction
  case access id region writing =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    have equal := Option.some.inj same
    subst after
    exact valid
  case view id region length writing =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj same
    exact valid
  case result id region writing =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    have equal := Option.some.inj same
    subst after
    exact valid
  case nullResult =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    have equal := Option.some.inj same
    subst after
    exact valid
  case fieldResult key id region writing =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact valid
  case nullFieldResult key =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj same
    exact valid
  case recordResult key id region writing =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact valid
  case nullRecordResult key =>
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact valid
  case invoke name arguments =>
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
    have equal := Option.some.inj same
    subst after
    exact valid

theorem apply_preserves_valid {s after : State} {a : Action}
    (h : apply s a = some after) (valid : Valid s) : Valid after := by
  have step := apply_transition h
  by_cases validates : requiresValidation a = true
  · simp only [apply, step, Option.bind_some, validates, ↓reduceIte] at h
    obtain ⟨_, passed, _⟩ := Option.bind_eq_some_iff.mp h
    exact (validB_iff after).mp (require_some passed)
  · have metadata : requiresValidation a = false := by cases h : requiresValidation a <;> simp_all
    exact metadata_preserves_valid metadata step valid

/-- Returning an owned field removes its sole release authority from the
callee and records exactly one corresponding result token. -/
theorem recordGive_consumes_authority {s after : State} {key holder family : Nat}
    (step : apply s (.recordGive key holder family) = some after) :
    (∀ token ∈ after.authorities, token.holder ≠ holder) ∧
    after.recordOwners = s.recordOwners ++ [(key, family)] ∧
    MayEnd s.loans holder := by
  have execution := apply_transition step
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp execution
  obtain ⟨token, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, ended, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨loan, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  refine ⟨?_, rfl, of_decide_eq_true (require_some ended)⟩
  intro other present
  simpa using (List.mem_filter.mp present).2

theorem recordGive_duplicate_refused (s : State) (key holder family : Nat)
    (present : (s.recordOwners.map Prod.fst).contains key = true) :
    transition s (.recordGive key holder family) = none := by
  have existing : s.recordOwners.any (fun r => r.1 == key) = true := by
    simpa [List.contains_iff_mem, List.mem_map, List.any_eq_true] using present
  simp [transition, require, existing]

/-- A returned borrowed field must refer to an input or static allocation;
ownership cleanup cannot turn local storage into a persistent lifetime. -/
theorem recordResult_external_lifetime {s after : State} {key id : Nat}
    {region : Region} {writing : Bool}
    (step : apply s (.recordResult key id region writing) = some after) :
    Access s.loans id region writing ∧
    ∃ allocation ∈ s.allocations,
      allocation.root = region.root ∧ (allocation.origin = .input ∨ allocation.origin = .static) := by
  have execution := apply_transition step
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp execution
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, accessible, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, external, _⟩ := Option.bind_eq_some_iff.mp rest
  refine ⟨of_decide_eq_true (require_some accessible), ?_⟩
  simpa using require_some external

theorem apply_access_iff {s : State} {id : Nat} {r : Region} {w : Bool} :
    apply s (.access id r w) = some s ↔ Access s.loans id r w := by
  by_cases allowed : Access s.loans id r w <;>
    simp [apply, transition, require, requiresValidation, allowed]

theorem admitted_view_exact {s after : State} {id length : Nat} {region : Region} {writing : Bool}
    (step : apply s (.view id region length writing) = some after) :
    length = region.count ∧ Access s.loans id region writing := by
  obtain ⟨_, passed, _⟩ := Option.bind_eq_some_iff.mp (apply_transition step)
  simpa using require_some passed

theorem restriction_never_widens {s after : State} {id : Nat} {region : Region}
    (step : apply s (.restrict id region) = some after) :
    ∃ loan ∈ s.loans, loan.id = id ∧ loan.region.Contains region ∧ MayEnd s.loans id := by
  obtain ⟨loan, found, rest⟩ := Option.bind_eq_some_iff.mp (apply_transition step)
  obtain ⟨_, passed, _⟩ := Option.bind_eq_some_iff.mp rest
  have checks := require_some passed
  have bounds : containsB loan.region region = true := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp checks).1).2
  have noChildren : MayEnd s.loans id := of_decide_eq_true (Bool.and_eq_true_iff.mp checks).2
  exact ⟨loan, List.mem_of_find?_eq_some found, by simpa using List.find?_some found,
    (containsB_iff _ _).mp bounds, noChildren⟩

/-- Admission never authorizes a write to a range concurrently usable through
another loan. This is a spatial theorem, independent of the implementation of
the C plan producer. -/
theorem admitted_write_excludes_alias {s : State} (valid : Valid s)
    {id other : Nat} {x y : Region} {w : Bool}
    (h : apply s (.access id x true) = some s) (different : id ≠ other)
    (reader : Access s.loans other y w) : x.Disjoint y :=
  exclusive_access_disjoint valid.2.2.2.1 different (apply_access_iff.mp h) reader

/-- A checked access cannot be dangling: its allocation is still present and
contains the accessed range. -/
theorem admitted_access_live {s : State} (valid : Valid s) {id : Nat} {r : Region} {w : Bool}
    (h : apply s (.access id r w) = some s) :
    ∃ a ∈ s.allocations, a.region.Contains r := by
  have access := apply_access_iff.mp h
  obtain ⟨l, mem, _, contained⟩ := access_has_live_loan access
  obtain ⟨a, present, bounds⟩ := valid.2.2.2.2.1 l mem
  exact ⟨a, present, Region.contains_trans bounds contained⟩

theorem release_has_authority {s after : State} {holder family : Nat}
    (h : apply s (.release holder family) = some after) :
    ∃ token ∈ s.authorities, token.holder = holder ∧ token.family = family ∧
      ∀ l ∈ s.loans, l.region.root ≠ token.root := by
  have step := apply_transition h
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, passed, _⟩ := Option.bind_eq_some_iff.mp rest
  have mem := List.mem_of_find?_eq_some found
  have allowed := of_decide_eq_true (require_some passed)
  exact ⟨token, mem, allowed.1.symm, allowed.2.1.symm, allowed.2.2⟩

namespace Controls

def rootPlan : List Action := [.root 1 16 .exclusive .local 0,
  .borrow 2 1 ⟨1, 0, 8⟩ .exclusive, .borrow 3 1 ⟨1, 8, 8⟩ .exclusive]

def run : State → List Action → Option State
  | s, [] => some s
  | s, a :: rest => (apply s a).bind fun after => run after rest

theorem separate_fields_admitted : (run initial (rootPlan ++
    [.access 2 ⟨1, 0, 8⟩ true, .access 3 ⟨1, 8, 8⟩ true])).isSome = true := by decide

theorem overlapping_fields_refused : run initial (rootPlan ++
    [.borrow 4 1 ⟨1, 4, 8⟩ .exclusive]) = none := by decide

theorem use_after_scope_refused : run initial
    [.root 1 4 .exclusive .local 0, .endLoan 1, .access 1 ⟨1, 0, 4⟩ false] = none := by decide

theorem borrow_does_not_acquire_release : run initial
    [.root 1 4 .exclusive .heap 9, .borrow 2 1 ⟨1, 0, 4⟩ .exclusive,
      .endLoan 2, .release 2 9] = none := by decide

theorem move_and_release_admitted : (run initial
    [.root 1 4 .exclusive .heap 9, .move 1 2, .endLoan 2, .release 2 9]).isSome = true := by decide

theorem moved_from_access_refused : run initial
    [.root 1 4 .exclusive .heap 9, .move 1 2, .access 1 ⟨1, 0, 4⟩ false] = none := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Ownership
