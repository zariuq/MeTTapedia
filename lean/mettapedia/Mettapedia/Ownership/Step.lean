import Mettapedia.Ownership.State

/-!
# Steps of a permission plan

Unlike a whole-buffer permission, a loan contains a range. Release tokens are
kept separately, so neither a shared nor an exclusive borrow can free a root.
A step is the transition of one action followed by the local check of the
objects it touched (`localCheck`). That a step keeps the invariant `Valid`, and
that from a valid state the local check decides exactly what a check of the
whole invariant decides, is proved in `Mettapedia.Ownership.StepValid`. This is
translation validation: a mistaken native checker cannot make a malformed
permission plan pass kernel admission.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

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
  /-- The storage of the input `view`, released earlier (`vacate`), is replaced
  by the fresh owned allocation `holder` of the same `family`, as a reallocation
  or a rehash does. The input keeps its identity for every caller, and whoever
  owns it releases its current storage later; the holder's sole release
  authority is consumed. -/
  | replace (view holder family : Nat)
  /-- The current storage of the whole input `view` is released to a native
  call of `family`, which receives it as a released transfer. The input is
  suspended until its storage is replaced, or restored by a reallocation that
  moved nothing. -/
  | vacate (view family : Nat)
  /-- The reallocation that received the storage of `view` returned null here,
  so nothing moved and the old storage remains. -/
  | restore (view : Nat)
  /-- The owner `holder` is null on this path: it owns nothing, so its
  authority and allocation end with no release. -/
  | nullOwner (holder family : Nat)
  | invoke (name : String) (arguments : List Argument)
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

/-- Nothing unless the condition holds. -/
def require (condition : Bool) : Option Unit := if condition then some () else none

def findLoan (s : State) (id : Nat) : Option Loan := s.loans.find? (fun l => l.id == id)

/-- The release authority `holder` holds, if any. -/
def findAuthority (s : State) (holder : Nat) : Option ReleaseAuthority :=
  s.authorities.find? (fun a => a.holder == holder)

def eraseLoan (s : State) (id : Nat) : State := { s with loans := endLoan s.loans id }
def fresh (s : State) (id : Nat) : Bool :=
  !(s.loans.any fun l => l.id == id) &&
  !(s.transfers.any fun t => t.holder == id || t.region.root == id)

/-- One action's change of state, or nothing when its checks fail. Each check is
`require`, each lookup a `find?`, chained with `Option.bind`. -/
def transition (s : State) : Action → Option State
  | .root id count mode origin family =>
      (require (id != 0 && fresh s id && !(s.allocations.any fun a => a.root == id))).bind fun _ =>
      (require ((origin == .heap) == (family != 0))).bind fun _ =>
      some { s with
        loans := s.loans ++ [⟨id, ⟨id, 0, count⟩, mode, []⟩]
        allocations := s.allocations ++ [⟨id, count, origin⟩]
        authorities := if origin == .heap then s.authorities ++ [⟨id, id, family⟩] else s.authorities }
  | .borrow id parent region mode =>
      (findLoan s parent).bind fun p =>
      (require (fresh s id && parent < id && p.ancestors.all (fun n => n < id))).bind fun _ =>
      (require (accessB s.loans parent region (mode == .exclusive))).bind fun _ =>
      some { s with loans := s.loans ++ [⟨id, region, mode, parent :: p.ancestors⟩] }
  | .access id region writing =>
      (require (accessB s.loans id region writing)).bind fun _ =>
      some s
  | .view id region length writing =>
      (require (length == region.count && accessB s.loans id region writing)).bind fun _ =>
      some s
  | .endLoan id =>
      (require (id != 0 && mayEndB s.loans id)).bind fun _ =>
      (findLoan s id).bind fun l =>
      let after := eraseLoan s id
      some { after with allocations := after.allocations.filter fun a =>
        !(a.root == l.region.root && id == a.root && a.origin != .heap) }
  | .move old freshId =>
      (findLoan s old).bind fun l =>
      (require (old != 0 && fresh s freshId && mayEndB s.loans old)).bind fun _ =>
      (require (l.ancestors.all fun p => p < freshId)).bind fun _ =>
      (require (s.authorities.any fun t => t.holder == old)).bind fun _ =>
      some { s with loans := (eraseLoan s old).loans ++ [{ l with id := freshId }]
                    authorities := s.authorities.map fun token =>
                      if token.holder == old then token.move freshId else token }
  | .release holder family =>
      (findAuthority s holder).bind fun token =>
      (require (mayReleaseB s.loans token holder family)).bind fun _ =>
      (s.allocations.find? (fun a => a.root == token.root)).bind fun allocation =>
      some { s with authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    transfers := s.transfers ++ [⟨holder, family, allocation.region, .released⟩] }
  | .restrict id region =>
      (findLoan s id).bind fun l =>
      (require (id != 0 && containsB l.region region && mayEndB s.loans id)).bind fun _ =>
      (require (!(s.authorities.any fun token => token.holder == id))).bind fun _ =>
      some { s with loans := s.loans.map fun loan =>
        if loan.id == id then { loan with region := region } else loan }
  | .give holder family =>
      (findAuthority s holder).bind fun token =>
      (require (token.family == family && s.ownedResult.isNone && s.result.isNone &&
        !s.nullResult)).bind fun _ =>
      (require (mayEndB s.loans holder)).bind fun _ =>
      (findLoan s holder).bind fun l =>
      (require (l.region.root == token.root && l.ancestors.isEmpty)).bind fun _ =>
      some { s with loans := (eraseLoan s holder).loans
                    authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    ownedResult := some family }
  | .handoff holder family =>
      (findAuthority s holder).bind fun token =>
      (require (token.family == family)).bind fun _ =>
      (require (mayEndB s.loans holder)).bind fun _ =>
      (findLoan s holder).bind fun l =>
      (require (l.region.root == token.root && l.ancestors.isEmpty)).bind fun _ =>
      some { s with loans := (eraseLoan s holder).loans
                    authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    transfers := s.transfers ++ [⟨holder, family, l.region, .owned⟩] }
  | .result id region writing =>
      (require (s.result.isNone && s.ownedResult.isNone && !s.nullResult)).bind fun _ =>
      (require (accessB s.loans id region writing)).bind fun _ =>
      (require (s.allocations.any fun a =>
        a.root == region.root && (a.origin == .input || a.origin == .static))).bind fun _ =>
      some { s with result := some region, resultWriting := writing }
  | .nullResult =>
      (require (s.result.isNone && s.ownedResult.isNone && !s.nullResult)).bind fun _ =>
      some { s with nullResult := true }
  | .fieldResult key id region writing =>
      (require (!(s.fieldResults.any fun r => r.key == key))).bind fun _ =>
      (require (accessB s.loans id region writing)).bind fun _ =>
      (require (s.allocations.any fun a =>
        a.root == region.root && (a.origin == .input || a.origin == .static))).bind fun _ =>
      some { s with fieldResults := s.fieldResults ++ [⟨key, some region, writing⟩] }
  | .nullFieldResult key =>
      (require (!(s.fieldResults.any fun r => r.key == key))).bind fun _ =>
      some { s with fieldResults := s.fieldResults ++ [⟨key, none, false⟩] }
  | .recordResult key id region writing =>
      (require (!(s.recordResults.any fun r => r.key == key))).bind fun _ =>
      (require (!(s.recordOwners.any fun r => r.1 == key))).bind fun _ =>
      (require (accessB s.loans id region writing)).bind fun _ =>
      (require (s.allocations.any fun a =>
        a.root == region.root && (a.origin == .input || a.origin == .static))).bind fun _ =>
      some { s with recordResults := s.recordResults ++ [⟨key, some region, writing⟩] }
  | .nullRecordResult key =>
      (require (!(s.recordResults.any fun r => r.key == key))).bind fun _ =>
      (require (!(s.recordOwners.any fun r => r.1 == key))).bind fun _ =>
      some { s with recordResults := s.recordResults ++ [⟨key, none, false⟩] }
  | .recordGive key holder family =>
      (require (!(s.recordResults.any fun r => r.key == key) &&
        !(s.recordOwners.any fun r => r.1 == key))).bind fun _ =>
      (findAuthority s holder).bind fun token =>
      (require (token.family == family)).bind fun _ =>
      (require (mayEndB s.loans holder)).bind fun _ =>
      (findLoan s holder).bind fun l =>
      (require (l.region.root == token.root && l.ancestors.isEmpty)).bind fun _ =>
      some { s with loans := (eraseLoan s holder).loans
                    authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    recordOwners := s.recordOwners ++ [(key, family)] }
  | .replace view holder family =>
      (findAuthority s holder).bind fun token =>
      (require (token.family == family)).bind fun _ =>
      (require (mayEndB s.loans holder)).bind fun _ =>
      (findLoan s holder).bind fun l =>
      (require (l.region.root == token.root && l.ancestors.isEmpty)).bind fun _ =>
      (findLoan s view).bind fun v =>
      (require (v.region.root != token.root && v.ancestors.isEmpty)).bind fun _ =>
      (require (s.allocations.any fun a => a.root == v.region.root && a.origin == .input)).bind fun _ =>
      (require (accessB s.loans view v.region true)).bind fun _ =>
      (require (s.suspended.any fun x => x.root == v.region.root && x.family == family)).bind fun _ =>
      some { s with loans := (eraseLoan s holder).loans
                    authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root
                    suspended := s.suspended.filter fun x => x.root != v.region.root }
  | .vacate view family =>
      (findLoan s view).bind fun v =>
      (require (family != 0 && v.ancestors.isEmpty &&
        !suspendedRoot s.suspended v.region.root)).bind fun _ =>
      (require (s.allocations.any fun a => a.root == v.region.root && a.origin == .input)).bind fun _ =>
      (require (accessB s.loans view v.region true)).bind fun _ =>
      (require (!(s.transfers.any fun t =>
        t.holder == view || t.region.root == v.region.root))).bind fun _ =>
      some { s with transfers := s.transfers ++ [⟨view, family, v.region, .released⟩]
                    suspended := s.suspended ++ [⟨v.region.root, family, false⟩] }
  | .restore view =>
      (findLoan s view).bind fun v =>
      (require (s.suspended.any fun x => x.root == v.region.root && x.restorable)).bind fun _ =>
      some { s with suspended := s.suspended.filter fun x => x.root != v.region.root }
  | .nullOwner holder family =>
      (findAuthority s holder).bind fun token =>
      (require (mayReleaseB s.loans token holder family)).bind fun _ =>
      some { s with authorities := s.authorities.filter fun a => a.holder != holder
                    allocations := s.allocations.filter fun a => a.root != token.root }
  | .invoke name _ =>
      (require (!name.isEmpty)).bind fun _ =>
      some s

/-- Actions that change no loan, allocation or release authority. -/
def metadata : Action → Bool
  | .access .. | .view .. | .result .. | .nullResult | .fieldResult .. | .nullFieldResult ..
  | .recordResult .. | .nullRecordResult .. | .invoke .. => true
  | _ => false

/-- No release authority is held by `holder`. -/
def holderFree (s : State) (holder : Nat) : Bool :=
  !(s.authorities.any fun a => a.holder == holder)

/-- No loan lies in the allocation rooted at `root`. -/
def rootFree (loans : List Loan) (root : Nat) : Bool :=
  !(loans.any fun l => l.region.root == root)

/-- After a step, the root is still allocated, or no loan is left in it. -/
def keptOrUnused (after : State) (root : Nat) : Bool :=
  after.allocations.any (fun a => a.root == root) || rootFree after.loans root

/-- The root of the storage `holder` may release. -/
def tokenRoot (s : State) (holder : Nat) : Option Nat :=
  (findAuthority s holder).map (·.root)

/-- The part of the invariant a step can break that its own checks do not
already ensure, checked on the objects the step touches: a new release
authority needs a holder that holds none, and storage a step stops allocating
must hold no loan. -/
def localCheck (s : State) (action : Action) (after : State) : Bool :=
  match action with
  | .root id _ _ origin _ => origin != .heap || holderFree s id
  | .move _ freshId => holderFree s freshId
  | .endLoan id => keptOrUnused after id
  | .give holder _ | .handoff holder _ | .recordGive _ holder _ | .replace _ holder _ =>
      match tokenRoot s holder with
      | some root => keptOrUnused after root
      | none => true
  | _ => true

/-- A step: the transition, then the local check of what it touched. -/
def apply (s : State) (action : Action) : Option State :=
  (transition s action).bind fun after =>
    (require (localCheck s action after)).bind fun _ => some after

theorem require_some {condition : Bool} (h : require condition = some ()) : condition = true := by
  unfold require at h
  split at h
  · assumption
  · contradiction


/-- A passed access check is the access its loans allow. -/
theorem require_access {loans : List Loan} {id : Nat} {part : Region} {writing : Bool}
    (h : require (accessB loans id part writing) = some ()) : Access loans id part writing :=
  (accessB_iff _ _ _ _).mp (require_some h)

/-- A passed end check: the loan is live and nothing descends from it. -/
theorem require_mayEnd {loans : List Loan} {id : Nat} (h : require (mayEndB loans id) = some ()) :
    MayEnd loans id :=
  (mayEndB_iff _ _).mp (require_some h)

/-- A passed release check: the actor holds the authority and no loan uses its storage. -/
theorem require_mayRelease {loans : List Loan} {authority : ReleaseAuthority} {actor family : Nat}
    (h : require (mayReleaseB loans authority actor family) = some ()) :
    MayRelease loans authority actor family :=
  (mayReleaseB_iff _ _ _ _).mp (require_some h)

theorem apply_transition {s after : State} {a : Action} (h : apply s a = some after) :
    transition s a = some after := by
  obtain ⟨next, step, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  exact step

/-- `apply` passed the local check of the step it took. -/
theorem apply_localCheck {s after : State} {a : Action} (h : apply s a = some after) :
    localCheck s a after = true := by
  obtain ⟨next, step, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, checked, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  exact require_some checked

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
  refine ⟨?_, rfl, require_mayEnd ended⟩
  intro other present
  simpa using (List.mem_filter.mp present).2

/-- Replacing an input's storage consumes the fresh allocation's sole release
authority, and is admitted only with exclusive access to the whole input: no
pointer into the old storage is live. The old storage was released earlier to
the same allocator family, and the input is reachable again afterwards. -/
theorem replace_consumes_authority {s after : State} {view holder family : Nat}
    (step : apply s (.replace view holder family) = some after) :
    (∀ token ∈ after.authorities, token.holder ≠ holder) ∧
    ∃ v, findLoan s view = some v ∧ Access s.loans view v.region true ∧
      (∃ x ∈ s.suspended, x.root = v.region.root ∧ x.family = family) ∧
      suspendedRoot after.suspended v.region.root = false := by
  have execution := apply_transition step
  obtain ⟨token, _, rest⟩ := Option.bind_eq_some_iff.mp execution
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨loan, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨v, found, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, exclusive, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, released, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  obtain ⟨x, present, agrees⟩ := List.any_eq_true.mp (require_some released)
  refine ⟨?_, v, found, require_access exclusive,
    ⟨x, present, by simpa using agrees⟩, ?_⟩
  · intro other present
    simpa using (List.mem_filter.mp present).2
  · simp [suspendedRoot]

/-- Releasing an input's storage needs exclusive access to the whole input. It
suspends the input and accounts for the storage as a released transfer, which
the native call must take. -/
theorem vacate_suspends {s after : State} {view family : Nat}
    (step : apply s (.vacate view family) = some after) :
    ∃ v, findLoan s view = some v ∧ Access s.loans view v.region true ∧
      suspendedRoot after.suspended v.region.root = true ∧
      after.transfers = s.transfers ++ [⟨view, family, v.region, .released⟩] := by
  have execution := apply_transition step
  obtain ⟨v, found, rest⟩ := Option.bind_eq_some_iff.mp execution
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, exclusive, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  exact ⟨v, found, require_access exclusive, by simp [suspendedRoot], rfl⟩

/-- Only a reallocation's source comes back: storage released to a call that
always releases it is never restored. -/
theorem restore_requires_reallocation {s after : State} {view : Nat}
    (step : apply s (.restore view) = some after) :
    ∃ v, findLoan s view = some v ∧
      ∃ x ∈ s.suspended, x.root = v.region.root ∧ x.restorable = true := by
  have execution := apply_transition step
  obtain ⟨v, found, rest⟩ := Option.bind_eq_some_iff.mp execution
  obtain ⟨_, restorable, _⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨x, present, agrees⟩ := List.any_eq_true.mp (require_some restorable)
  exact ⟨v, found, x, present, by simpa using agrees⟩

/-- A null owner ends with its authority, as a release does, once every loan
of its allocation has ended; nothing is transferred. -/
theorem nullOwner_has_authority {s after : State} {holder family : Nat}
    (h : apply s (.nullOwner holder family) = some after) :
    (∃ token ∈ s.authorities, token.holder = holder ∧ token.family = family ∧
      ∀ l ∈ s.loans, l.region.root ≠ token.root) ∧ after.transfers = s.transfers := by
  have step := apply_transition h
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, passed, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have mem := List.mem_of_find?_eq_some found
  have allowed := require_mayRelease passed
  exact ⟨⟨token, mem, allowed.1.symm, allowed.2.1.symm, allowed.2.2⟩, rfl⟩

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
  refine ⟨require_access accessible, ?_⟩
  simpa using require_some external

theorem apply_access_iff {s : State} {id : Nat} {r : Region} {w : Bool} :
    apply s (.access id r w) = some s ↔ Access s.loans id r w := by
  rw [← accessB_iff]
  cases allowed : accessB s.loans id r w <;> simp [apply, transition, require, localCheck, allowed]

theorem admitted_view_exact {s after : State} {id length : Nat} {region : Region} {writing : Bool}
    (step : apply s (.view id region length writing) = some after) :
    length = region.count ∧ Access s.loans id region writing := by
  obtain ⟨_, passed, _⟩ := Option.bind_eq_some_iff.mp (apply_transition step)
  simpa [accessB_iff] using require_some passed

theorem restriction_never_widens {s after : State} {id : Nat} {region : Region}
    (step : apply s (.restrict id region) = some after) :
    ∃ loan ∈ s.loans, loan.id = id ∧ loan.region.Contains region ∧ MayEnd s.loans id := by
  obtain ⟨loan, found, rest⟩ := Option.bind_eq_some_iff.mp (apply_transition step)
  obtain ⟨_, passed, _⟩ := Option.bind_eq_some_iff.mp rest
  have checks := require_some passed
  have bounds : containsB loan.region region = true := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp checks).1).2
  have noChildren : MayEnd s.loans id := (mayEndB_iff _ _).mp (Bool.and_eq_true_iff.mp checks).2
  exact ⟨loan, List.mem_of_find?_eq_some found, by simpa using List.find?_some found,
    (containsB_iff _ _).mp bounds, noChildren⟩

/-- Admission never authorizes a write to a range concurrently usable through
another loan. This is a spatial theorem, independent of the implementation of
the C plan producer. -/
theorem admitted_write_excludes_alias {s : State} (valid : Valid s)
    {id other : Nat} {x y : Region} {w : Bool}
    (h : apply s (.access id x true) = some s) (different : id ≠ other)
    (reader : Access s.loans other y w) : x.Disjoint y :=
  exclusive_access_disjoint valid.ordered different (apply_access_iff.mp h) reader

/-- A checked access cannot be dangling: its allocation is still present and
contains the accessed range. -/
theorem admitted_access_live {s : State} (valid : Valid s) {id : Nat} {r : Region} {w : Bool}
    (h : apply s (.access id r w) = some s) :
    ∃ a ∈ s.allocations, a.region.Contains r := by
  have access := apply_access_iff.mp h
  obtain ⟨l, mem, _, contained⟩ := access_has_live_loan access
  obtain ⟨a, present, bounds⟩ := valid.covered l mem
  exact ⟨a, present, Region.contains_trans bounds contained⟩

theorem release_has_authority {s after : State} {holder family : Nat}
    (h : apply s (.release holder family) = some after) :
    ∃ token ∈ s.authorities, token.holder = holder ∧ token.family = family ∧
      ∀ l ∈ s.loans, l.region.root ≠ token.root := by
  have step := apply_transition h
  obtain ⟨token, found, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, passed, _⟩ := Option.bind_eq_some_iff.mp rest
  have mem := List.mem_of_find?_eq_some found
  have allowed := require_mayRelease passed
  exact ⟨token, mem, allowed.1.symm, allowed.2.1.symm, allowed.2.2⟩

end Mettapedia.Ownership
