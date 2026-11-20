import Mettapedia.Ownership.Admission
import Mettapedia.Ownership.Interface
import Mettapedia.Ownership.Composition

/-!
# The frame rule of ownership admission

A checked function is admitted in its own coordinates: its plan starts from the
static root alone and acquires each input root against its declared parameter.
This module proves the separation-logic frame property of that admission.

* **Reach.** In every reachable state of an admitted function, every loan, and
  every region an access, borrow, view, restriction or result names, is static
  storage used only for reading, the storage an input parameter lends (within
  the extent the parameter declares, written only if the parameter lends it for
  writing), or an allocation the function made itself. Applied to a function
  admitted against a narrowed interface, this is reach relative to the narrowed
  inputs: a part outside the interface cannot be acquired at all.
* **The caller-side frame.** A call changes no loan, allocation or release
  authority of its caller. Every callee region on a lent input lies, in the
  caller, inside the loan lent for it (or the owned storage handed over), and
  its use there is authorized through that loan alone. A caller loan the call
  does not lend is kept, and no callee region conflicts with it: wherever
  either side may write, the two are disjoint.
* **Suspension.** Storage released to be replaced is named by no action and lent
  to no call, and stays released until it is replaced or restored.

The frame is exactly the unlent loans: a lent part is what the callee writes.
The call contract lends a loan passed for writing once (`lentOnce`): an admitted
function may release one input and write the other, and one exclusive loan lent
as both would put the two on the same caller storage. The controls show the
function admitted and that call refused.

Loans and roots are names local to one plan; a callee region is placed in its
caller by the lent loan (`instantiateView`), and a whole view's unit is the
whole lent span. The native projection of C bodies onto plans remains a
separate boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership.Frame

open Mettapedia.Machines.CMemory.Borrowing
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.PermissionFlow

/-! ## Footprints -/

/-- The storage a parameter lends to the callee: the extent of its input root in
the callee's units (a whole view is one abstract unit), and whether the callee
may write it. Value, static, released and resized parameters lend none of the
caller's storage. -/
def lends : Parameter → Option (Nat × Bool)
  | .borrowed count writing | .optionalBorrowed count writing => some (count, writing)
  | .viewed writing | .optionalViewed writing => some (1, writing)
  | .owned count _ | .optionalOwned count _ => some (count, true)
  | _ => none

/-- The footprint classes of a function's storage, for a region used with right
`writing`: static storage, for reading only; the storage an input parameter
lends, within the extent it declares and with at most its right; or an
allocation of the function's own, which no input names. -/
def Reach (f : Function) (s : State) (x : Region) (writing : Bool) : Prop :=
  (x.root = 0 ∧ writing = false) ∨
  (x.root ≠ 0 ∧ ∃ (i : Nat) (p : Parameter) (count : Nat) (canWrite : Bool),
    f.signature.parameters[i]? = some p ∧ f.inputs[i]? = some x.root ∧
    lends p = some (count, canWrite) ∧ x.finish ≤ count ∧ (writing = true → canWrite = true)) ∨
  (x.root ≠ 0 ∧ x.root ∉ f.inputs ∧ ∃ a ∈ s.allocations, a.root = x.root ∧ a.origin ≠ .input)

/-- The regions an action names, with the right it uses. A restriction narrows a
loan and uses no right. -/
def named : Action → List (Region × Bool)
  | .borrow _ _ region mode => [(region, mode == .exclusive)]
  | .access _ region writing | .view _ region _ writing | .result _ region writing
  | .fieldResult _ _ region writing | .recordResult _ _ region writing => [(region, writing)]
  | .restrict _ region => [(region, false)]
  | _ => []

/-- The loans a call lends. -/
def lentLoans (arguments : List Argument) : List Nat :=
  arguments.filterMap fun argument => match argument with
    | .loan id | .maybe id => some id
    | _ => none

theorem reach_sub {f : Function} {s : State} {outer x : Region} {right writing : Bool}
    (reach : Reach f s outer right) (inside : outer.Contains x)
    (rights : writing = true → right = true) : Reach f s x writing := by
  have root : outer.root = x.root := inside.1
  rcases reach with ⟨zero, reading⟩ | ⟨nonzero, i, p, count, canWrite, param, input, lent, bound, canW⟩ |
      ⟨nonzero, fresh, a, allocated, same, origin⟩
  · refine Or.inl ⟨root ▸ zero, ?_⟩
    cases writing
    · rfl
    · exact absurd ((rights rfl).symm.trans reading) (by decide)
  · exact Or.inr (Or.inl ⟨root ▸ nonzero, i, p, count, canWrite, param, root ▸ input, lent,
      le_trans inside.2.2 bound, fun w => canW (rights w)⟩)
  · exact Or.inr (Or.inr ⟨root ▸ nonzero, root ▸ fresh, a, allocated, same.trans root, origin⟩)

theorem access_reading {loans : List Loan} {id : Nat} {x : Region} {writing : Bool}
    (access : Access loans id x writing) : Access loans id x false := by
  obtain ⟨l, live, same, contains, _, others⟩ := access
  refine ⟨l, live, same, contains, (fun h => by cases h), ?_⟩
  intro other present different overlaps
  rcases others other present different overlaps with ancestor | ⟨_, shared⟩
  · exact Or.inl ancestor
  · exact Or.inr ⟨rfl, shared⟩

/-! ## What a call changes in its caller -/

/-- What a call may change in its caller's permissions: no loan, allocation or
release authority; it only takes transfers, and keeps every suspended root. -/
structure CallFrame (s t : State) : Prop where
  loans : t.loans = s.loans
  allocations : t.allocations = s.allocations
  authorities : t.authorities = s.authorities
  transfers : ∀ tr ∈ t.transfers, tr ∈ s.transfers
  suspended : t.suspended.map Suspension.root = s.suspended.map Suspension.root

theorem CallFrame.refl (s : State) : CallFrame s s :=
  ⟨rfl, rfl, rfl, fun _ mem => mem, rfl⟩

theorem CallFrame.trans {s u t : State} (first : CallFrame s u) (second : CallFrame u t) :
    CallFrame s t :=
  ⟨second.loans.trans first.loans, second.allocations.trans first.allocations,
    second.authorities.trans first.authorities,
    fun tr mem => first.transfers tr (second.transfers tr mem),
    second.suspended.trans first.suspended⟩

theorem receipt_frame {s t : State} {holder family count : Nat} {kind : TransferKind}
    (h : receipt s holder family kind count = some t) : CallFrame s t := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  exact ⟨rfl, rfl, rfl, fun tr mem => (List.mem_filter.mp mem).1, rfl⟩

theorem resizeReceipt_frame {s t : State} {holder family : Nat}
    (h : resizeReceipt s holder family = some t) : CallFrame s t := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨middle, received, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have frame := receipt_frame received
  refine ⟨frame.loans, frame.allocations, frame.authorities, frame.transfers, ?_⟩
  show (middle.suspended.map _).map Suspension.root = s.suspended.map Suspension.root
  rw [List.map_map, ← frame.suspended]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  split <;> rfl

theorem passBorrow_frame {s t : State} {count id : Nat} {writing : Bool}
    (h : passBorrow s count writing id = some t) : t = s := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  exact (Option.some.inj same).symm

theorem passArgument_frame {s t : State} {p : Parameter} {argument : Argument}
    (h : passArgument s p argument = some t) : CallFrame s t := by
  cases p <;> cases argument <;> simp only [passArgument] at h <;> try contradiction
  all_goals first
    | exact receipt_frame h
    | exact resizeReceipt_frame h
    | (rw [passBorrow_frame h]; exact CallFrame.refl _)
    | (cases Option.some.inj h; exact CallFrame.refl _)
    | (obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
       cases Option.some.inj same
       exact CallFrame.refl _)

theorem passArguments_frame {s t : State} {ps : List Parameter} {args : List Argument}
    (h : passArguments s ps args = some t) : CallFrame s t := by
  induction ps generalizing s args with
  | nil =>
      cases args with
      | nil => cases Option.some.inj h; exact CallFrame.refl _
      | cons => contradiction
  | cons _ _ ih =>
      cases args with
      | nil => contradiction
      | cons _ _ =>
          obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp h
          exact (passArgument_frame first).trans (ih rest)

theorem passVariadic_frame {s t : State} {args : List Argument}
    (h : passVariadic s args = some t) : CallFrame s t := by
  induction args generalizing s with
  | nil => cases Option.some.inj h; exact CallFrame.refl _
  | cons a _ ih =>
      cases a <;> simp only [passVariadic] at h <;> try contradiction
      · exact ih h
      · obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp h
        exact (passArgument_frame first).trans (ih rest)

/-- (b), its permission part: a call changes no loan, allocation or release
authority of its caller. It only takes the transfers its arguments name, and
keeps every suspended root suspended. -/
theorem invoke_frame {signature : Signature} {s after : State} {arguments : List Argument}
    (h : invoke signature s arguments = some after) : CallFrame s after := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp rest
  have frame := passArguments_frame first
  split at rest
  · exact frame.trans (passVariadic_frame rest)
  · obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact frame

theorem passArguments_at {s t : State} {ps : List Parameter} {args : List Argument}
    (h : passArguments s ps args = some t) {i : Nat} {p : Parameter} (hp : ps[i]? = some p) :
    ∃ argument u v, args[i]? = some argument ∧ CallFrame s u ∧
      passArgument u p argument = some v := by
  induction ps generalizing s args i with
  | nil => simp at hp
  | cons _ _ ih =>
      cases args with
      | nil => contradiction
      | cons b _ =>
          obtain ⟨u, first, rest⟩ := Option.bind_eq_some_iff.mp h
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
              subst hp
              exact ⟨b, s, u, rfl, CallFrame.refl s, first⟩
          | succ _ =>
              simp only [List.getElem?_cons_succ] at hp
              obtain ⟨argument, u', v, found, frame, passed⟩ := ih rest hp
              exact ⟨argument, u', v, by simpa using found, (passArgument_frame first).trans frame,
                passed⟩

/-- Each parameter of a successful call was checked against the argument at its
position, in a state with the caller's loans. -/
theorem invoke_at {signature : Signature} {s after : State} {arguments : List Argument}
    (h : invoke signature s arguments = some after) {i : Nat} {p : Parameter}
    (hp : signature.parameters[i]? = some p) :
    ∃ argument u v, arguments[i]? = some argument ∧ CallFrame s u ∧
      passArgument u p argument = some v := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, first, _⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨argument, u, v, found, frame, passed⟩ := passArguments_at first hp
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp hp
  refine ⟨argument, u, v, ?_, frame, passed⟩
  rwa [List.getElem?_take_of_lt bound] at found

theorem passBorrow_facts {u v : State} {count id : Nat} {writing : Bool}
    (h : passBorrow u count writing id = some v) :
    ∃ lender, findLoan u id = some lender ∧ count ≤ lender.region.count ∧
      Access u.loans id lender.region writing := by
  obtain ⟨lender, found, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, extent, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, access, _⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨lender, found, of_decide_eq_true (require_some extent),
    require_access access⟩

theorem receipt_facts {u v : State} {holder family count : Nat} {kind : TransferKind}
    (h : receipt u holder family kind count = some v) :
    ∃ tr ∈ u.transfers, tr.holder = holder ∧ tr.kind = kind ∧ count ≤ tr.region.count := by
  obtain ⟨tr, found, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, checks, _⟩ := Option.bind_eq_some_iff.mp rest
  have c := require_some checks
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
  exact ⟨tr, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, c.1.2, c.2⟩

/-- Where a region of a callee's input storage lies in its caller: inside the
lent region at the region's offset, or, for a whole view, the whole lent span. -/
def place (p : Parameter) (lent x : Region) : Region :=
  match p with
  | .viewed _ | .optionalViewed _ => lent
  | _ => instantiateView lent x.first x.count

/-- What a lending parameter receives from a successful argument check: nothing
for a null argument, a usable loan covering every region within the extent, or
an owned transfer of at least the extent. -/
theorem lent_storage {u v : State} {p : Parameter} {argument : Argument} {count : Nat}
    {canWrite : Bool} (lent : lends p = some (count, canWrite))
    (passed : passArgument u p argument = some v) :
    argument = .null ∨
    (∃ id lender, (argument = .loan id ∨ argument = .maybe id) ∧ findLoan u id = some lender ∧
      Access u.loans id lender.region canWrite ∧
      ∀ x : Region, x.finish ≤ count → lender.region.Contains (place p lender.region x)) ∨
    (∃ holder transfer, argument = .owned holder ∧ transfer ∈ u.transfers ∧
      transfer.holder = holder ∧ transfer.kind = .owned ∧ count ≤ transfer.region.count) := by
  cases p with
  | borrowed _ _ =>
      simp only [lends, Option.some.injEq, Prod.mk.injEq] at lent
      obtain ⟨rfl, rfl⟩ := lent
      cases argument <;> simp only [passArgument] at passed <;> try contradiction
      obtain ⟨lender, found, fits, access⟩ := passBorrow_facts passed
      exact Or.inr (Or.inl ⟨_, lender, Or.inl rfl, found, access,
        fun x inside => instantiateView_contained fits inside⟩)
  | optionalBorrowed _ _ =>
      simp only [lends, Option.some.injEq, Prod.mk.injEq] at lent
      obtain ⟨rfl, rfl⟩ := lent
      cases argument <;> simp only [passArgument] at passed <;> try contradiction
      · obtain ⟨lender, found, fits, access⟩ := passBorrow_facts passed
        exact Or.inr (Or.inl ⟨_, lender, Or.inl rfl, found, access,
          fun x inside => instantiateView_contained fits inside⟩)
      · obtain ⟨lender, found, fits, access⟩ := passBorrow_facts passed
        exact Or.inr (Or.inl ⟨_, lender, Or.inr rfl, found, access,
          fun x inside => instantiateView_contained fits inside⟩)
      · exact Or.inl rfl
  | viewed _ =>
      simp only [lends, Option.some.injEq, Prod.mk.injEq] at lent
      obtain ⟨rfl, rfl⟩ := lent
      cases argument <;> simp only [passArgument] at passed <;> try contradiction
      obtain ⟨lender, found, _, access⟩ := passBorrow_facts passed
      exact Or.inr (Or.inl ⟨_, lender, Or.inl rfl, found, access,
        fun _ _ => Region.contains_refl _⟩)
  | optionalViewed _ =>
      simp only [lends, Option.some.injEq, Prod.mk.injEq] at lent
      obtain ⟨rfl, rfl⟩ := lent
      cases argument <;> simp only [passArgument] at passed <;> try contradiction
      · obtain ⟨lender, found, _, access⟩ := passBorrow_facts passed
        exact Or.inr (Or.inl ⟨_, lender, Or.inl rfl, found, access,
          fun _ _ => Region.contains_refl _⟩)
      · obtain ⟨lender, found, _, access⟩ := passBorrow_facts passed
        exact Or.inr (Or.inl ⟨_, lender, Or.inr rfl, found, access,
          fun _ _ => Region.contains_refl _⟩)
      · exact Or.inl rfl
  | owned _ _ =>
      simp only [lends, Option.some.injEq, Prod.mk.injEq] at lent
      obtain ⟨rfl, rfl⟩ := lent
      cases argument <;> simp only [passArgument] at passed <;> try contradiction
      obtain ⟨transfer, present, holds, kind, fits⟩ := receipt_facts passed
      exact Or.inr (Or.inr ⟨_, transfer, rfl, present, holds, kind, fits⟩)
  | optionalOwned _ _ =>
      simp only [lends, Option.some.injEq, Prod.mk.injEq] at lent
      obtain ⟨rfl, rfl⟩ := lent
      cases argument <;> simp only [passArgument] at passed <;> try contradiction
      · obtain ⟨transfer, present, holds, kind, fits⟩ := receipt_facts passed
        exact Or.inr (Or.inr ⟨_, transfer, rfl, present, holds, kind, fits⟩)
      · exact Or.inl rfl
  | _ => simp [lends] at lent

/-! ## What a plan transition changes -/

/-- The loans after a transition: inside an old loan with no more right, or the
loan of a fresh root. -/
def LoansFrame (s : State) (a : Action) (t : State) : Prop :=
  ∀ l ∈ t.loans,
    (∃ old ∈ s.loans, old.region.Contains l.region ∧ (l.mode = .exclusive → old.mode = .exclusive)) ∨
    (∃ count origin family, a = .root l.id count l.mode origin family ∧
      l.region = ⟨l.id, 0, count⟩ ∧ fresh s l.id = true ∧ l.id ≠ 0)

/-- The allocations after a transition: old ones, or a fresh root's. -/
def AllocationsFrame (s : State) (a : Action) (t : State) : Prop :=
  ∀ x ∈ t.allocations, x ∈ s.allocations ∨
    ∃ mode family, a = .root x.root x.count mode x.origin family ∧ x.root ≠ 0

/-- The transfers after a transition: old ones, released storage, or an owned
handoff whose root no allocation keeps. -/
def TransfersFrame (s : State) (a : Action) (t : State) : Prop :=
  ∀ tr ∈ t.transfers, tr ∈ s.transfers ∨ tr.kind = .released ∨
    (∃ holder family, a = .handoff holder family) ∧ ∀ x ∈ t.allocations, x.root ≠ tr.region.root

/-- A suspended root stays suspended unless the transition replaces or restores
storage. -/
def SuspendedFrame (s : State) (a : Action) (t : State) : Prop :=
  ∀ root, suspendedRoot s.suspended root = true →
    suspendedRoot t.suspended root = true ∨ (∃ view holder family, a = .replace view holder family) ∨
      ∃ view, a = .restore view

structure TransitionFrame (s : State) (a : Action) (t : State) : Prop where
  loans : LoansFrame s a t
  allocations : AllocationsFrame s a t
  transfers : TransfersFrame s a t
  suspended : SuspendedFrame s a t

theorem TransitionFrame.of_sub {s t : State} {a : Action}
    (loans : ∀ l ∈ t.loans, l ∈ s.loans) (allocations : ∀ x ∈ t.allocations, x ∈ s.allocations)
    (transfers : t.transfers = s.transfers) (suspended : t.suspended = s.suspended) :
    TransitionFrame s a t where
  loans l mem := Or.inl ⟨l, loans l mem, Region.contains_refl _, fun e => e⟩
  allocations x mem := Or.inl (allocations x mem)
  transfers tr mem := Or.inl (by rw [← transfers]; exact mem)
  suspended root held := Or.inl (by rw [suspended]; exact held)

theorem transition_frame {s t : State} {a : Action} (valid : Valid s)
    (h : transition s a = some t) : TransitionFrame s a t := by
  cases a with
  | root _ count mode origin family =>
      obtain ⟨_, admissible, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj rest
      have checks := require_some admissible
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at checks
      refine ⟨?_, ?_, fun _ mem => Or.inl mem, fun _ held => Or.inl held⟩
      · intro l mem
        rcases List.mem_append.mp mem with old | new
        · exact Or.inl ⟨l, old, Region.contains_refl _, fun e => e⟩
        · rw [List.mem_singleton] at new
          subst new
          exact Or.inr ⟨count, origin, family, rfl, rfl, checks.1.2, checks.1.1⟩
      · intro x mem
        rcases List.mem_append.mp mem with old | new
        · exact Or.inl old
        · rw [List.mem_singleton] at new
          subst new
          exact Or.inr ⟨mode, family, rfl, checks.1.1⟩
  | borrow _ _ _ mode =>
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, usable, rest⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj rest
      have access := require_access usable
      refine ⟨?_, fun _ mem => Or.inl mem, fun _ mem => Or.inl mem, fun _ held => Or.inl held⟩
      intro l mem
      rcases List.mem_append.mp mem with old | new
      · exact Or.inl ⟨l, old, Region.contains_refl _, fun e => e⟩
      · rw [List.mem_singleton] at new
        subst new
        obtain ⟨owner, present, _, contains, rights, _⟩ := access
        refine Or.inl ⟨owner, present, contains, fun exclusive => rights ?_⟩
        have same : mode = .exclusive := exclusive
        simp [same]
  | access _ _ _ =>
      obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj same
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | view _ _ _ _ =>
      obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj same
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | endLoan _ =>
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      exact TransitionFrame.of_sub (fun _ m => (List.mem_filter.mp m).1)
        (fun _ m => (List.mem_filter.mp m).1) rfl rfl
  | move _ _ =>
      obtain ⟨l, found, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      have present := List.mem_of_find?_eq_some found
      refine ⟨?_, fun _ mem => Or.inl mem, fun _ mem => Or.inl mem, fun _ held => Or.inl held⟩
      intro x mem
      rcases List.mem_append.mp mem with kept | moved
      · exact Or.inl ⟨x, (List.mem_filter.mp kept).1, Region.contains_refl _, fun e => e⟩
      · rw [List.mem_singleton] at moved
        subst moved
        exact Or.inl ⟨l, present, Region.contains_refl _, fun e => e⟩
  | restrict id region =>
      obtain ⟨l, found, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, bounds, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      have present := List.mem_of_find?_eq_some found
      have identity : l.id = id := by simpa using List.find?_some found
      have inside : l.region.Contains region := (containsB_iff _ _).mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (require_some bounds)).1).2
      refine ⟨?_, fun _ mem => Or.inl mem, fun _ mem => Or.inl mem, fun _ held => Or.inl held⟩
      intro x mem
      obtain ⟨loan, kept, rfl⟩ := List.mem_map.mp mem
      refine Or.inl ?_
      try dsimp only
      split
      · rename_i hit
        have equal : loan = l := List.inj_on_of_nodup_map valid.loanIds kept present
          ((beq_iff_eq.mp hit).trans identity.symm)
        subst equal
        exact ⟨loan, kept, inside, fun e => e⟩
      · exact ⟨loan, kept, Region.contains_refl _, fun e => e⟩
  | release _ _ =>
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      refine ⟨fun l mem => Or.inl ⟨l, mem, Region.contains_refl _, fun e => e⟩,
        fun _ mem => Or.inl (List.mem_filter.mp mem).1, ?_, fun _ held => Or.inl held⟩
      intro tr mem
      rcases List.mem_append.mp mem with old | new
      · exact Or.inl old
      · rw [List.mem_singleton] at new
        subst new
        exact Or.inr (Or.inl rfl)
  | give _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => (List.mem_filter.mp m).1)
        (fun _ m => (List.mem_filter.mp m).1) rfl rfl
  | handoff holder family =>
      obtain ⟨token, _, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨l, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, rooted, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      have root : l.region.root = token.root := by
        have checks := require_some rooted
        simp only [Bool.and_eq_true, beq_iff_eq] at checks
        exact checks.1
      refine ⟨fun x m => Or.inl ⟨x, (List.mem_filter.mp m).1, Region.contains_refl _, fun e => e⟩,
        fun _ m => Or.inl (List.mem_filter.mp m).1, ?_, fun _ held => Or.inl held⟩
      intro tr mem
      rcases List.mem_append.mp mem with old | new
      · exact Or.inl old
      · rw [List.mem_singleton] at new
        subst new
        refine Or.inr (Or.inr ⟨⟨holder, family, rfl⟩, ?_⟩)
        intro x kept
        have apart := (List.mem_filter.mp kept).2
        simp only [bne_iff_ne, ne_eq] at apart
        show x.root ≠ l.region.root
        rw [root]
        exact apart
  | result _ _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | nullResult =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | fieldResult _ _ _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | nullFieldResult _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | recordResult _ _ _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | nullRecordResult _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl
  | recordGive _ _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => (List.mem_filter.mp m).1)
        (fun _ m => (List.mem_filter.mp m).1) rfl rfl
  | replace view holder family =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact ⟨fun x m => Or.inl ⟨x, (List.mem_filter.mp m).1, Region.contains_refl _, fun e => e⟩,
        fun _ m => Or.inl (List.mem_filter.mp m).1, fun _ m => Or.inl m,
        fun _ _ => Or.inr (Or.inl ⟨view, holder, family, rfl⟩)⟩
  | vacate _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      refine ⟨fun x m => Or.inl ⟨x, m, Region.contains_refl _, fun e => e⟩, fun _ m => Or.inl m,
        ?_, ?_⟩
      · intro tr mem
        rcases List.mem_append.mp mem with old | new
        · exact Or.inl old
        · rw [List.mem_singleton] at new
          subst new
          exact Or.inr (Or.inl rfl)
      · intro r held
        refine Or.inl ?_
        simp only [suspendedRoot, List.any_append, Bool.or_eq_true] at held ⊢
        exact Or.inl held
  | restore view =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact ⟨fun x m => Or.inl ⟨x, m, Region.contains_refl _, fun e => e⟩, fun _ m => Or.inl m,
        fun _ m => Or.inl m, fun _ _ => Or.inr (Or.inr ⟨view, rfl⟩)⟩
  | nullOwner _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => (List.mem_filter.mp m).1) rfl rfl
  | invoke _ _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact TransitionFrame.of_sub (fun _ m => m) (fun _ m => m) rfl rfl

/-- The step of a checked function: a plan transition, whose roots claiming to be
inputs were checked against the interface, or a call by its contract. -/
theorem enabledCore_cases {callables : List Callable} {f : Function} {s t : State} {a : Action}
    (h : enabledCore callables f s a = some t) :
    (∃ name arguments callee, a = .invoke name arguments ∧
      callables.find? (fun c => c.name == name) = some callee ∧
      invoke callee.signature s arguments = some t) ∨
    (apply s a = some t ∧ ∀ id count mode origin family, a = .root id count mode origin family →
      (origin == .input || f.inputs.contains id || (f.ambient.map Prod.fst).contains id) = true →
      inputRoot f id count mode origin family = true) := by
  cases a with
  | invoke name arguments =>
      obtain ⟨callee, found, called⟩ := Option.bind_eq_some_iff.mp h
      exact Or.inl ⟨name, arguments, callee, rfl, found, called⟩
  | root _ _ _ _ _ =>
      refine Or.inr ?_
      simp only [enabledCore] at h
      split at h
      · obtain ⟨_, claimed, applied⟩ := Option.bind_eq_some_iff.mp h
        refine ⟨applied, fun _ _ _ _ _ same _ => ?_⟩
        cases same
        exact require_some claimed
      · rename_i unclaimed
        refine ⟨h, fun _ _ _ _ _ same claims => ?_⟩
        cases same
        exact absurd claims unclaimed
  | _ => exact Or.inr ⟨h, (fun _ _ _ _ _ same _ => by cases same)⟩

theorem enabled_frame {callables : List Callable} {f : Function} {s t : State} {a : Action}
    (valid : Valid s) (step : enabled callables f s a = some t) :
    (TransitionFrame s a t ∧ ∀ id count mode origin family, a = .root id count mode origin family →
        (origin == .input || f.inputs.contains id || (f.ambient.map Prod.fst).contains id) = true →
        inputRoot f id count mode origin family = true) ∨
    (∃ name arguments, ∃ callee : Callable, a = .invoke name arguments ∧
      invoke callee.signature s arguments = some t) := by
  obtain ⟨_, _, core⟩ := Option.bind_eq_some_iff.mp step
  rcases enabledCore_cases core with ⟨name, arguments, callee, rfl, _, called⟩ | ⟨applied, claims⟩
  · exact Or.inr ⟨name, arguments, callee, rfl, called⟩
  · exact Or.inl ⟨transition_frame valid (apply_transition applied), claims⟩

/-! ## (a) Reach -/

/-- An allocation a checked function may hold: static storage, an input's storage
at the extent its parameter declares, or an allocation of its own. -/
def Held (f : Function) (a : Allocation) : Prop :=
  a.root = 0 ∨
  (a.root ≠ 0 ∧ ∃ (i : Nat) (p : Parameter) (canWrite : Bool),
    f.signature.parameters[i]? = some p ∧ f.inputs[i]? = some a.root ∧
    lends p = some (a.count, canWrite)) ∨
  (a.root ∉ f.inputs ∧ a.origin ≠ .input)

/-- A root through which a checked function may write: never static storage, and
an input only if its parameter lends it for writing. -/
def WritableRoot (f : Function) (root : Nat) : Prop :=
  root ≠ 0 ∧ (root ∈ f.inputs → ∃ (i : Nat) (p : Parameter) (count : Nat),
    f.signature.parameters[i]? = some p ∧ f.inputs[i]? = some root ∧ lends p = some (count, true))

/-- The invariant behind (a). -/
structure Confined (f : Function) (s : State) : Prop where
  valid : Valid s
  held : ∀ a ∈ s.allocations, Held f a
  writable : ∀ l ∈ s.loans, l.mode = .exclusive → WritableRoot f l.region.root

theorem initial_confined (f : Function) : Confined f initial where
  valid := initial_valid
  held := by
    intro a mem
    simp only [initial, List.mem_singleton] at mem
    subst mem
    exact Or.inl rfl
  writable := by
    intro l mem exclusive
    simp only [initial, List.mem_singleton] at mem
    subst mem
    cases exclusive

/-- The interface check of a root claiming to be an input: a declared input of
that extent, exclusive only if the parameter lends it for writing. -/
theorem inputRoot_lends {f : Function} (noAmbient : f.ambient = []) {id count : Nat} {mode : Mode}
    {origin : Origin} {family : Nat} (rooted : inputRoot f id count mode origin family = true) :
    ∃ (i : Nat) (p : Parameter) (canWrite : Bool), f.signature.parameters[i]? = some p ∧
      f.inputs[i]? = some id ∧ lends p = some (count, canWrite) ∧
      (mode = .exclusive → canWrite = true) := by
  simp only [inputRoot, noAmbient, List.any_nil, Bool.or_false, List.any_eq_true] at rooted
  obtain ⟨⟨p, _⟩, member, holds⟩ := rooted
  obtain ⟨i, slot⟩ := List.mem_iff_getElem?.mp member
  rw [List.getElem?_zip_eq_some] at slot
  simp only [Bool.and_eq_true, beq_iff_eq] at holds
  obtain ⟨same, kind⟩ := holds
  subst same
  refine ⟨i, p, ?_⟩
  cases p with
  | borrowed _ writing =>
      simp only [Bool.and_eq_true, beq_iff_eq] at kind
      obtain ⟨⟨⟨counted, moded⟩, _⟩, _⟩ := kind
      refine ⟨writing, slot.1, slot.2, by simp [lends, counted], fun exclusive => ?_⟩
      cases writing
      · simp [exclusive] at moded
      · rfl
  | optionalBorrowed _ writing =>
      simp only [Bool.and_eq_true, beq_iff_eq] at kind
      obtain ⟨⟨⟨counted, moded⟩, _⟩, _⟩ := kind
      refine ⟨writing, slot.1, slot.2, by simp [lends, counted], fun exclusive => ?_⟩
      cases writing
      · simp [exclusive] at moded
      · rfl
  | viewed writing =>
      simp only [Bool.and_eq_true, beq_iff_eq] at kind
      obtain ⟨⟨⟨counted, moded⟩, _⟩, _⟩ := kind
      refine ⟨writing, slot.1, slot.2, by simp [lends, counted], fun exclusive => ?_⟩
      cases writing
      · simp [exclusive] at moded
      · rfl
  | optionalViewed writing =>
      simp only [Bool.and_eq_true, beq_iff_eq] at kind
      obtain ⟨⟨⟨counted, moded⟩, _⟩, _⟩ := kind
      refine ⟨writing, slot.1, slot.2, by simp [lends, counted], fun exclusive => ?_⟩
      cases writing
      · simp [exclusive] at moded
      · rfl
  | owned _ _ =>
      simp only [Bool.and_eq_true, beq_iff_eq] at kind
      obtain ⟨⟨⟨counted, _⟩, _⟩, _⟩ := kind
      exact ⟨true, slot.1, slot.2, by simp [lends, counted], fun _ => rfl⟩
  | optionalOwned _ _ =>
      simp only [Bool.and_eq_true, beq_iff_eq] at kind
      obtain ⟨⟨⟨counted, _⟩, _⟩, _⟩ := kind
      exact ⟨true, slot.1, slot.2, by simp [lends, counted], fun _ => rfl⟩
  | _ => simp at kind

theorem enabled_confined {callables : List Callable} {f : Function} (noAmbient : f.ambient = [])
    {s t : State} {a : Action} (step : enabled callables f s a = some t)
    (confined : Confined f s) : Confined f t := by
  have valid := enabled_valid step confined.valid
  rcases enabled_frame confined.valid step with ⟨frame, claims⟩ | ⟨_, _, _, rfl, called⟩
  · refine ⟨valid, ?_, ?_⟩
    · intro x mem
      rcases frame.allocations x mem with old | ⟨_, _, isRoot, nonzero⟩
      · exact confined.held x old
      · by_cases claimed : (x.origin == .input || f.inputs.contains x.root ||
            (f.ambient.map Prod.fst).contains x.root) = true
        · obtain ⟨i, p, canWrite, param, input, lent, _⟩ :=
            inputRoot_lends noAmbient (claims _ _ _ _ _ isRoot claimed)
          exact Or.inr (Or.inl ⟨nonzero, i, p, canWrite, param, input, lent⟩)
        · simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, not_or] at claimed
          exact Or.inr (Or.inr ⟨claimed.1.2, claimed.1.1⟩)
    · intro l mem exclusive
      rcases frame.loans l mem with ⟨old, present, contains, rights⟩ |
          ⟨count, origin, _, isRoot, region, _, nonzero⟩
      · have writable := confined.writable old present (rights exclusive)
        rw [contains.1] at writable
        exact writable
      · rw [region]
        by_cases claimed : (origin == .input || f.inputs.contains l.id ||
            (f.ambient.map Prod.fst).contains l.id) = true
        · obtain ⟨i, p, _, param, input, lent, rights⟩ :=
            inputRoot_lends noAmbient (claims _ _ _ _ _ isRoot claimed)
          refine ⟨nonzero, fun _ => ⟨i, p, count, param, input, ?_⟩⟩
          rw [lent, rights exclusive]
        · simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, not_or] at claimed
          exact ⟨nonzero, fun member => absurd member claimed.1.2⟩
  · have frame := invoke_frame called
    refine ⟨valid, ?_, ?_⟩
    · intro x mem
      rw [frame.allocations] at mem
      exact confined.held x mem
    · intro l mem
      rw [frame.loans] at mem
      exact confined.writable l mem

/-- Every reachable state of an admitted function is confined. -/
theorem admitted_confined {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s : State}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial s) : Confined f s :=
  path.invariant
    (fun _ _ _ step confined =>
      enabled_confined (admitted_has_no_ambient_authority admitted) step confined)
    (initial_confined f)

theorem admitted_inputsValid {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) : inputsValid f = true := by
  cases valid : inputsValid f
  · simp [admitFunction, valid] at admitted
  · rfl

theorem filter_nonzero_index_unique {l : List Nat} (nodup : (l.filter (· != 0)).Nodup)
    {i j r : Nat} (hi : l[i]? = some r) (hj : l[j]? = some r) (nonzero : r ≠ 0) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a rest ih =>
      by_cases zero : a = 0
      · have tail : (rest.filter (· != 0)).Nodup := by
          simpa [List.filter_cons, zero] using nodup
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            exact absurd (hi ▸ zero) nonzero
        | succ _ =>
            cases j with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                exact absurd (hj ▸ zero) nonzero
            | succ _ =>
                simp only [List.getElem?_cons_succ] at hi hj
                exact congrArg (· + 1) (ih tail hi hj)
      · have whole : (a :: rest.filter (· != 0)).Nodup := by
          simpa [List.filter_cons, zero] using nodup
        have tail := (List.nodup_cons.mp whole).2
        have fresh := (List.nodup_cons.mp whole).1
        cases i with
        | zero =>
            cases j with
            | zero => rfl
            | succ _ =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
                simp only [List.getElem?_cons_succ] at hj
                subst hi
                exact absurd (List.mem_filter.mpr ⟨List.mem_of_getElem? hj, by simpa using zero⟩) fresh
        | succ _ =>
            cases j with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                simp only [List.getElem?_cons_succ] at hi
                subst hj
                exact absurd (List.mem_filter.mpr ⟨List.mem_of_getElem? hi, by simpa using zero⟩) fresh
            | succ _ =>
                simp only [List.getElem?_cons_succ] at hi hj
                exact congrArg (· + 1) (ih tail hi hj)

/-- An admitted function names each nonzero input once. -/
theorem admitted_input_index_unique {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {i j r : Nat}
    (hi : f.inputs[i]? = some r) (hj : f.inputs[j]? = some r) (nonzero : r ≠ 0) : i = j := by
  have valid := admitted_inputsValid admitted
  simp only [inputsValid, Bool.and_eq_true] at valid
  exact filter_nonzero_index_unique ((uniqueIds_iff _).mp valid.1.2) hi hj nonzero

theorem confined_loan_reach {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s : State} (confined : Confined f s)
    {l : Loan} (live : l ∈ s.loans) : Reach f s l.region (l.mode == .exclusive) := by
  obtain ⟨a, allocated, contains⟩ := confined.valid.covered l live
  have rootEq : a.root = l.region.root := contains.1
  have bound : l.region.finish ≤ a.count := by
    have := contains.2.2
    simpa [Allocation.region, Region.finish] using this
  have shared : l.region.root = 0 → (l.mode == .exclusive) = false := by
    intro zero
    cases mode : l.mode with
    | shared => rfl
    | exclusive => exact absurd zero (confined.writable l live mode).1
  rcases confined.held a allocated with zero | ⟨nonzero, i, p, canWrite, param, input, lent⟩ |
      ⟨fresh, origin⟩
  · have zero' : l.region.root = 0 := rootEq ▸ zero
    exact Or.inl ⟨zero', shared zero'⟩
  · rw [rootEq] at nonzero input
    refine Or.inr (Or.inl ⟨nonzero, i, p, a.count, canWrite, param, input, lent, bound, ?_⟩)
    intro writes
    have exclusive : l.mode = .exclusive := by simpa using writes
    obtain ⟨_, inputs⟩ := confined.writable l live exclusive
    obtain ⟨_, _, _, param', input', lent'⟩ := inputs (List.mem_of_getElem? input)
    have same := admitted_input_index_unique admitted input input' nonzero
    subst same
    rw [param] at param'
    cases param'
    rw [lent] at lent'
    cases lent'
    rfl
  · by_cases zero : l.region.root = 0
    · exact Or.inl ⟨zero, shared zero⟩
    · rw [rootEq] at fresh
      exact Or.inr (Or.inr ⟨zero, fresh, a, allocated, rootEq, origin⟩)

/-- (a), for the storage a function holds: in every reachable state of an
admitted function, every loan is static storage held for reading, an input's
storage within its declared extent and right, or the function's own
allocation. -/
theorem admitted_loan_reach {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s : State}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial s)
    {l : Loan} (live : l ∈ s.loans) : Reach f s l.region (l.mode == .exclusive) :=
  confined_loan_reach admitted (admitted_confined admitted path) live

/-- Every region an enabled action names lies in a live loan with the right the
action uses. -/
theorem named_covered {callables : List Callable} {f : Function} {s next : State} {a : Action}
    (step : enabled callables f s a = some next) {x : Region} {writing : Bool}
    (mem : (x, writing) ∈ named a) :
    ∃ l ∈ s.loans, l.region.Contains x ∧ (writing = true → l.mode = .exclusive) := by
  obtain ⟨_, _, core⟩ := Option.bind_eq_some_iff.mp step
  have usable : ∀ {id : Nat}, Access s.loans id x writing →
      ∃ l ∈ s.loans, l.region.Contains x ∧ (writing = true → l.mode = .exclusive) := by
    intro _ access
    obtain ⟨l, live, _, contains, rights, _⟩ := access
    exact ⟨l, live, contains, rights⟩
  cases a with
  | borrow _ _ _ _ =>
      simp only [named, List.mem_singleton, Prod.mk.injEq] at mem
      obtain ⟨rfl, rfl⟩ := mem
      have transition := apply_transition core
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp transition
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, allowed, _⟩ := Option.bind_eq_some_iff.mp rest
      exact usable (require_access allowed)
  | access _ _ _ =>
      simp only [named, List.mem_singleton, Prod.mk.injEq] at mem
      obtain ⟨rfl, rfl⟩ := mem
      have transition := apply_transition core
      obtain ⟨_, allowed, _⟩ := Option.bind_eq_some_iff.mp transition
      exact usable (require_access allowed)
  | view _ _ _ _ =>
      simp only [named, List.mem_singleton, Prod.mk.injEq] at mem
      obtain ⟨rfl, rfl⟩ := mem
      exact usable (admitted_view_exact core).2
  | restrict _ _ =>
      simp only [named, List.mem_singleton, Prod.mk.injEq] at mem
      obtain ⟨rfl, rfl⟩ := mem
      obtain ⟨l, live, _, contains, _⟩ := restriction_never_widens core
      exact ⟨l, live, contains, (fun h => by cases h)⟩
  | result _ _ _ =>
      simp only [named, List.mem_singleton, Prod.mk.injEq] at mem
      obtain ⟨rfl, rfl⟩ := mem
      have transition := apply_transition core
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp transition
      obtain ⟨_, allowed, _⟩ := Option.bind_eq_some_iff.mp rest
      exact usable (require_access allowed)
  | fieldResult _ _ _ _ =>
      simp only [named, List.mem_singleton, Prod.mk.injEq] at mem
      obtain ⟨rfl, rfl⟩ := mem
      have transition := apply_transition core
      obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp transition
      obtain ⟨_, allowed, _⟩ := Option.bind_eq_some_iff.mp rest
      exact usable (require_access allowed)
  | recordResult _ _ _ _ =>
      simp only [named, List.mem_singleton, Prod.mk.injEq] at mem
      obtain ⟨rfl, rfl⟩ := mem
      exact usable (recordResult_external_lifetime core).1
  | _ => simp [named] at mem

/-- (a) Reach: every access, borrow, view, restriction and result of an admitted
function, at every reachable point, names static storage only for reading, an
input's storage within the extent and right its parameter declares, or an
allocation of the function's own. -/
theorem admitted_reach {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s next : State} {a : Action}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial s)
    (step : enabled callables f s a = some next) {x : Region} {writing : Bool}
    (mem : (x, writing) ∈ named a) : Reach f s x writing := by
  obtain ⟨l, live, contains, rights⟩ := named_covered step mem
  exact reach_sub (admitted_loan_reach admitted path live) contains
    (fun w => by simp [rights w])

/-- Every loan an enabled call lends is live and not released for replacement. -/
theorem enabled_lends_live {callables : List Callable} {f : Function} {s next : State}
    {name : String} {arguments : List Argument}
    (step : enabled callables f s (.invoke name arguments) = some next) {id : Nat}
    (lent : id ∈ lentLoans arguments) :
    ∃ l ∈ s.loans, l.id = id ∧ suspendedRoot s.suspended l.region.root = false := by
  obtain ⟨_, allowed, _⟩ := Option.bind_eq_some_iff.mp step
  have whole := require_some allowed
  simp only [wholeAction, Option.any_eq_true] at whole
  obtain ⟨_, _, checked⟩ := whole
  obtain ⟨argument, member, lending⟩ := List.mem_filterMap.mp lent
  obtain ⟨index, slot⟩ := List.mem_iff_getElem?.mp member
  have inZip : (argument, index) ∈ arguments.zipIdx := List.mem_zipIdx_iff_getElem?.mpr slot
  have entry := List.all_eq_true.mp checked _ inZip
  cases argument with
  | loan id' =>
      have same : id' = id := Option.some.inj lending
      subst same
      simp only at entry
      cases found : findLoan s id' with
      | none => simp [found] at entry
      | some l =>
          simp only [found, Bool.and_eq_true, Bool.not_eq_true'] at entry
          exact ⟨l, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, entry.1⟩
  | maybe id' =>
      have same : id' = id := Option.some.inj lending
      subst same
      simp only at entry
      cases found : findLoan s id' with
      | none => simp [found] at entry
      | some l =>
          simp only [found, Bool.and_eq_true, Bool.not_eq_true'] at entry
          exact ⟨l, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, entry.1⟩
  | _ => simp at lending

/-! ## Suspension -/

/-- Storage released to be replaced is named by no enabled action. -/
theorem suspended_storage_unnamed {callables : List Callable} {f : Function} {s next : State}
    {a : Action} (step : enabled callables f s a = some next) {x : Region} {writing : Bool}
    (mem : (x, writing) ∈ named a) : suspendedRoot s.suspended x.root = false := by
  obtain ⟨_, allowed, _⟩ := Option.bind_eq_some_iff.mp step
  have whole := require_some allowed
  cases a <;> simp only [named, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil] at mem
  all_goals
    obtain ⟨rfl, -⟩ := mem
    simp only [wholeAction, Bool.and_eq_true, Bool.not_eq_true'] at whole
    exact whole.2

theorem suspendedRoot_roots {l l' : List Suspension}
    (same : l.map Suspension.root = l'.map Suspension.root) (root : Nat) :
    suspendedRoot l root = suspendedRoot l' root := by
  have through : ∀ m : List Suspension,
      suspendedRoot m root = (m.map Suspension.root).any (fun r => r == root) := by
    intro m
    simp [suspendedRoot, Function.comp_def]
  rw [through l, through l', same]

/-- Storage released to be replaced stays released through every step that
neither replaces nor restores storage. -/
theorem suspension_persists {callables : List Callable} {f : Function} {s next : State}
    {a : Action} (valid : Valid s) (step : enabled callables f s a = some next) {root : Nat}
    (suspended : suspendedRoot s.suspended root = true)
    (notReplaced : ∀ view holder family, a ≠ .replace view holder family)
    (notRestored : ∀ view, a ≠ .restore view) :
    suspendedRoot next.suspended root = true := by
  rcases enabled_frame valid step with ⟨frame, _⟩ | ⟨_, _, _, _, called⟩
  · rcases frame.suspended root suspended with kept | ⟨view, holder, family, same⟩ | ⟨view, same⟩
    · exact kept
    · exact absurd same (notReplaced view holder family)
    · exact absurd same (notRestored view)
  · rw [suspendedRoot_roots (invoke_frame called).suspended]
    exact suspended

/-! ## Storage handed to a call -/

/-- No loan lies on storage whose owner was handed to a call. -/
def TransfersUnlent (s : State) : Prop :=
  ∀ tr ∈ s.transfers, tr.kind = .owned → ∀ l ∈ s.loans, l.region.root ≠ tr.region.root

theorem enabled_transfers_unlent {callables : List Callable} {g : Function} {s t : State}
    {a : Action} (valid : Valid s) (step : enabled callables g s a = some t)
    (unlent : TransfersUnlent s) : TransfersUnlent t := by
  have valid' := enabled_valid step valid
  rcases enabled_frame valid step with ⟨frame, _⟩ | ⟨_, _, _, _, called⟩
  · intro tr mem owned l live
    rcases frame.transfers tr mem with old | released | ⟨_, apart⟩
    · rcases frame.loans l live with ⟨o, present, contains, _⟩ |
          ⟨_, _, _, _, region, freshness, _⟩
      · rw [← contains.1]
        exact unlent tr old owned o present
      · rw [region]
        show l.id ≠ tr.region.root
        intro same
        have absent := (Bool.and_eq_true_iff.mp freshness).2
        simp only [Bool.not_eq_true', List.any_eq_false] at absent
        exact absent tr old (by simp [same])
    · rw [owned] at released
      cases released
    · obtain ⟨x, allocated, contains⟩ := valid'.covered l live
      exact fun same => apart x allocated (contains.1.trans same)
  · have frame := invoke_frame called
    intro tr mem owned l live
    rw [frame.loans] at live
    exact unlent tr (frame.transfers tr mem) owned l live

/-- In every reachable state of any checked function, no loan lies on storage
handed to a call. -/
theorem reachable_transfers_unlent {callables : List Callable} {g : Function} {s : State}
    (path : PermissionFlow.Prefix (enabled callables g) g.body initial s) : TransfersUnlent s :=
  (path.invariant (property := fun s => Valid s ∧ TransfersUnlent s)
    (fun _ _ _ step both => ⟨enabled_valid step both.1, enabled_transfers_unlent both.1 step both.2⟩)
    ⟨initial_valid, by intro tr mem; simp [initial] at mem⟩).2

/-! ## (b) The caller-side frame -/

/-- A callee region on input `i` lies at `placed` in its caller: inside a loan the
call lends, or inside storage an owned argument hands over. -/
inductive Placed (f : Function) (s : State) (arguments : List Argument) (x placed : Region) : Prop
  | loan {i id : Nat} {p : Parameter} {argument : Argument} {lender : Loan}
      (parameter : f.signature.parameters[i]? = some p) (input : f.inputs[i]? = some x.root)
      (nonzero : x.root ≠ 0) (passed : arguments[i]? = some argument)
      (lending : argument = .loan id ∨ argument = .maybe id)
      (found : findLoan s id = some lender) (location : placed = place p lender.region x)
  | owned {i holder : Nat} {p : Parameter} {transfer : Transfer}
      (parameter : f.signature.parameters[i]? = some p) (input : f.inputs[i]? = some x.root)
      (nonzero : x.root ≠ 0) (passed : arguments[i]? = some (Argument.owned holder))
      (present : transfer ∈ s.transfers) (holds : transfer.holder = holder)
      (kind : transfer.kind = .owned)
      (location : placed = instantiateView transfer.region x.first x.count)

/-- (b), where the callee's storage is: every loan an admitted callee holds, at
every reachable point, is static storage held for reading, caller storage an
argument lends or hands over, an input bound to a null argument, or the callee's
own allocation. -/
theorem callee_storage_in_caller {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s after : State} {arguments : List Argument}
    (called : invoke f.signature s arguments = some after) {t : State}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial t) {l : Loan}
    (live : l ∈ t.loans) :
    (l.region.root = 0 ∧ l.mode = .shared) ∨ (∃ placed, Placed f s arguments l.region placed) ∨
    (∃ i : Nat, f.inputs[i]? = some l.region.root ∧ arguments[i]? = some Argument.null) ∨
    (l.region.root ≠ 0 ∧ l.region.root ∉ f.inputs) := by
  rcases admitted_loan_reach admitted path live with ⟨zero, reading⟩ |
      ⟨nonzero, i, _, _, _, parameter, input, lent, _, _⟩ | ⟨nonzero, fresh, _⟩
  · refine Or.inl ⟨zero, ?_⟩
    cases mode : l.mode
    · rfl
    · rw [mode] at reading
      simp at reading
  · obtain ⟨_, u, _, passed, frame, passedArg⟩ := invoke_at called parameter
    rcases lent_storage lent passedArg with null | ⟨id, _, lending, found, _, _⟩ |
        ⟨_, _, owned, present, holds, kind, _⟩
    · subst null
      exact Or.inr (Or.inr (Or.inl ⟨i, input, passed⟩))
    · have findSame : findLoan u id = findLoan s id := by simp only [findLoan, frame.loans]
      rw [findSame] at found
      exact Or.inr (Or.inl ⟨_, Placed.loan parameter input nonzero passed lending found rfl⟩)
    · subst owned
      exact Or.inr (Or.inl ⟨_, Placed.owned parameter input nonzero passed
        (frame.transfers _ present) holds kind rfl⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨nonzero, fresh⟩))

/-- (b), reach through lent loans only: a callee region on an input a loan
argument lends lies inside that loan in the caller, and its use there, with the
callee's right, is authorized in the caller's whole loan context through that
loan. -/
theorem callee_access_authorized {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s after : State} {arguments : List Argument}
    (called : invoke f.signature s arguments = some after) {t : State}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial t) {l : Loan}
    (live : l ∈ t.loans) {i id : Nat} {p : Parameter} {argument : Argument} {lender : Loan}
    (parameter : f.signature.parameters[i]? = some p) (input : f.inputs[i]? = some l.region.root)
    (nonzero : l.region.root ≠ 0) (passed : arguments[i]? = some argument)
    (lending : argument = .loan id ∨ argument = .maybe id) (found : findLoan s id = some lender) :
    lender.region.Contains (place p lender.region l.region) ∧
      Access s.loans id (place p lender.region l.region) (l.mode == .exclusive) := by
  obtain ⟨_, u, _, passed', frame, passedArg⟩ := invoke_at called parameter
  rw [passed] at passed'
  cases passed'
  rcases admitted_loan_reach admitted path live with ⟨zero, _⟩ |
      ⟨_, _, _, _, _, param, input', lent, bound, rights⟩ | ⟨_, fresh, _⟩
  · exact absurd zero nonzero
  · have same := admitted_input_index_unique admitted input input' nonzero
    subst same
    rw [parameter] at param
    cases param
    rcases lent_storage lent passedArg with null | ⟨id', _, lending', found', access, inside⟩ |
        ⟨_, _, owned, _⟩
    · rcases lending with rfl | rfl <;> cases null
    · have sameId : id' = id := by
        rcases lending with rfl | rfl <;> rcases lending' with h | h <;> cases h <;> rfl
      subst sameId
      have findSame : findLoan u id' = findLoan s id' := by simp only [findLoan, frame.loans]
      rw [findSame, found] at found'
      cases found'
      rw [frame.loans] at access
      have contained := inside l.region bound
      refine ⟨contained, ?_⟩
      have sub := access_subfootprint regionGeometry access contained
      cases mode : l.mode
      · exact access_reading sub
      · have writable := rights (by simp [mode])
        rw [writable] at sub
        exact sub
    · rcases lending with rfl | rfl <;> cases owned
  · exact absurd (List.mem_of_getElem? input) fresh

/-- (b) The caller-side frame. Across a call of an admitted function, a caller
loan the call does not lend stays in the caller's state, and no callee region
placed in the caller conflicts with it: wherever the callee or the caller may
write, the two are disjoint. -/
theorem caller_frame {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s after : State} {arguments : List Argument}
    (valid : Valid s) (unlent : TransfersUnlent s)
    (called : invoke f.signature s arguments = some after) {t : State}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial t) {l : Loan}
    (live : l ∈ t.loans) {placed : Region} (here : Placed f s arguments l.region placed)
    {o : Loan} (kept : o ∈ s.loans) (unpassed : o.id ∉ lentLoans arguments)
    {R : Region} {writing : Bool} (usable : Access s.loans o.id R writing)
    (conflict : l.mode = .exclusive ∨ writing = true) :
    o ∈ after.loans ∧ placed.Disjoint R := by
  refine ⟨by rw [(invoke_frame called).loans]; exact kept, ?_⟩
  cases here with
  | @loan _ id p argument lender parameter input nonzero passed lending found location =>
      subst location
      obtain ⟨_, authorized⟩ := callee_access_authorized admitted called path live parameter input
        nonzero passed lending found
      have lentId : id ∈ lentLoans arguments := List.mem_filterMap.mpr
        ⟨argument, List.mem_of_getElem? passed, by rcases lending with rfl | rfl <;> rfl⟩
      have different : id ≠ o.id := fun same => unpassed (same ▸ lentId)
      rcases conflict with exclusive | writes
      · have writer : Access s.loans id (place p lender.region l.region) true := by
          rw [exclusive] at authorized
          exact authorized
        exact exclusive_access_disjoint valid.ordered different writer usable
      · rw [writes] at usable
        exact Region.disjoint_symm
          (exclusive_access_disjoint valid.ordered (Ne.symm different) usable authorized)
  | @owned _ _ _ transfer _ _ _ _ present _ kind location =>
      subst location
      obtain ⟨other, live', _, contains⟩ := access_has_live_loan usable
      exact Or.inl (fun same => unlent transfer present kind other live' (contains.1.trans same.symm))

/-- The strongest separation among the arguments of one call: callee storage lent
through two different loans is disjoint wherever either is written. One loan lent
twice for writing is refused by the call contract (`lentOnce`,
`FrameControls.lent_twice_refused`). -/
theorem distinct_lenders_separate {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s after : State} {arguments : List Argument}
    (valid : Valid s) (called : invoke f.signature s arguments = some after) {t : State}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial t) {l l' : Loan}
    (live : l ∈ t.loans) (live' : l' ∈ t.loans)
    {i j id id' : Nat} {p q : Parameter} {argument argument' : Argument} {lender lender' : Loan}
    (parameter : f.signature.parameters[i]? = some p) (input : f.inputs[i]? = some l.region.root)
    (nonzero : l.region.root ≠ 0) (passed : arguments[i]? = some argument)
    (lending : argument = .loan id ∨ argument = .maybe id) (found : findLoan s id = some lender)
    (parameter' : f.signature.parameters[j]? = some q)
    (input' : f.inputs[j]? = some l'.region.root) (nonzero' : l'.region.root ≠ 0)
    (passed' : arguments[j]? = some argument')
    (lending' : argument' = .loan id' ∨ argument' = .maybe id')
    (found' : findLoan s id' = some lender') (different : id ≠ id')
    (conflict : l.mode = .exclusive ∨ l'.mode = .exclusive) :
    (place p lender.region l.region).Disjoint (place q lender'.region l'.region) := by
  have one := (callee_access_authorized admitted called path live parameter input nonzero passed
    lending found).2
  have other := (callee_access_authorized admitted called path live' parameter' input' nonzero'
    passed' lending' found').2
  rcases conflict with exclusive | exclusive
  · have writer : Access s.loans id (place p lender.region l.region) true := by
      rw [exclusive] at one
      exact one
    exact exclusive_access_disjoint valid.ordered different writer other
  · have writer : Access s.loans id' (place q lender'.region l'.region) true := by
      rw [exclusive] at other
      exact other
    exact Region.disjoint_symm
      (exclusive_access_disjoint valid.ordered (Ne.symm different) writer one)

theorem place_contains (p : Parameter) (lent : Region) {outer x : Region}
    (inside : outer.Contains x) : (place p lent outer).Contains (place p lent x) := by
  cases p with
  | viewed _ | optionalViewed _ => exact Region.contains_refl _
  | _ =>
      obtain ⟨_, lower, upper⟩ := inside
      simp only [Region.finish] at upper
      refine ⟨rfl, ?_, ?_⟩
      · show lent.first + outer.first ≤ lent.first + x.first
        omega
      · show lent.first + x.first + x.count ≤ lent.first + outer.first + outer.count
        omega

/-- (b) for every action: a region an admitted callee's enabled access, borrow,
view, restriction or result names, placed in the caller, is disjoint from every
region a caller loan the call does not lend can use, wherever either side may
write. -/
theorem callee_action_framed {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {s after : State} {arguments : List Argument}
    (valid : Valid s) (unlent : TransfersUnlent s)
    (called : invoke f.signature s arguments = some after) {t next : State} {a : Action}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial t)
    (step : enabled callables f t a = some next) {x : Region} {right : Bool}
    (mem : (x, right) ∈ named a) {placed : Region} (here : Placed f s arguments x placed)
    {o : Loan} (kept : o ∈ s.loans) (unpassed : o.id ∉ lentLoans arguments)
    {R : Region} {writing : Bool} (usable : Access s.loans o.id R writing)
    (conflict : right = true ∨ writing = true) : placed.Disjoint R := by
  obtain ⟨l, live, contains, rights⟩ := named_covered step mem
  have root : l.region.root = x.root := contains.1
  have loanConflict : l.mode = .exclusive ∨ writing = true := by
    rcases conflict with w | w
    · exact Or.inl (rights w)
    · exact Or.inr w
  cases here with
  | @loan _ _ p _ lender parameter input nonzero passed lending found location =>
      subst location
      have outer : Placed f s arguments l.region (place p lender.region l.region) :=
        Placed.loan parameter (root ▸ input) (root ▸ nonzero) passed lending found rfl
      exact Region.disjoint_subregions
        (caller_frame admitted valid unlent called path live outer kept unpassed usable loanConflict).2
        (place_contains p lender.region contains) (Region.contains_refl R)
  | @owned _ _ _ transfer parameter input nonzero passed present holds kind location =>
      subst location
      have outer : Placed f s arguments l.region
          (instantiateView transfer.region l.region.first l.region.count) :=
        Placed.owned parameter (root ▸ input) (root ▸ nonzero) passed present holds kind rfl
      exact Region.disjoint_subregions
        (caller_frame admitted valid unlent called path live outer kept unpassed usable loanConflict).2
        (place_contains (.borrowed 0 false) transfer.region contains) (Region.contains_refl R)

/-! ## Calls inside an admitted module, and closed calls across units -/

theorem module_member_admitted {m : Module} (admitted : admit m = true) {f : Function}
    (member : f ∈ m.functions) : admitFunction m.callables f = true := by
  simp only [admit, Bool.and_eq_true] at admitted
  exact List.all_eq_true.mp admitted.2 f member

theorem module_callable {m : Module} (admitted : admit m = true) {f : Function}
    (member : f ∈ m.functions) :
    m.callables.find? (fun c => c.name == f.name) = some ⟨f.name, f.signature⟩ := by
  have names : m.callables.map Callable.name = m.names := by
    simp [Module.callables, Module.names, Function.comp_def]
  have unique : (m.callables.map Callable.name).Nodup := by
    rw [names]
    simp only [admit, Bool.and_eq_true, decide_eq_true_eq] at admitted
    exact admitted.1.1.2
  have present : (⟨f.name, f.signature⟩ : Callable) ∈ m.callables :=
    List.mem_append_right _ (List.mem_map.mpr ⟨f, member, rfl⟩)
  cases found : m.callables.find? (fun c => c.name == f.name) with
  | none =>
      have := List.find?_eq_none.mp found _ present
      simp at this
  | some c =>
      have mem := List.mem_of_find?_eq_some found
      have same : c.name = f.name := by simpa using List.find?_some found
      rw [List.inj_on_of_nodup_map unique mem present same]

/-- In an admitted module, a call of a member is that member's contract. -/
theorem module_call_contract {m : Module} (admitted : admit m = true) {g f : Function}
    {s after : State} {arguments : List Argument} (member : f ∈ m.functions)
    (step : enabled m.callables g s (.invoke f.name arguments) = some after) :
    invoke f.signature s arguments = some after := by
  obtain ⟨_, _, core⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, found, called⟩ := Option.bind_eq_some_iff.mp core
  rw [module_callable admitted member] at found
  cases found
  exact called

/-- (b) inside an admitted module, with no further hypothesis: at any reachable
call of a member, a caller loan the call does not lend is kept, and every callee
region placed in the caller is disjoint from it wherever either side may write. -/
theorem module_call_frame {m : Module} (admitted : admit m = true) {g f : Function}
    (member : f ∈ m.functions) {s after : State} {arguments : List Argument}
    (reached : PermissionFlow.Prefix (enabled m.callables g) g.body initial s)
    (step : enabled m.callables g s (.invoke f.name arguments) = some after)
    {o : Loan} (kept : o ∈ s.loans) (unpassed : o.id ∉ lentLoans arguments) :
    o ∈ after.loans ∧
    ∀ {t : State}, PermissionFlow.Prefix (enabled m.callables f) f.body initial t →
      ∀ {l : Loan}, l ∈ t.loans → ∀ {placed : Region}, Placed f s arguments l.region placed →
        ∀ {R : Region} {writing : Bool}, Access s.loans o.id R writing →
          (l.mode = .exclusive ∨ writing = true) → placed.Disjoint R := by
  have called := module_call_contract admitted member step
  have valid : Valid s :=
    reached.invariant (fun _ _ _ step valid => enabled_valid step valid) initial_valid
  refine ⟨by rw [(invoke_frame called).loans]; exact kept, ?_⟩
  intro _ path _ live _ here _ _ usable conflict
  exact (caller_frame (module_member_admitted admitted member) valid
    (reachable_transfers_unlent reached) called path live here kept unpassed usable conflict).2

/-- A closed call across units is the contract of the admitted body that closes
it, so the caller-side frame applies to that body. -/
theorem closed_call_contract {definitions : List Composition.Definition}
    {assumption : Composition.Assumption} {definition : Composition.Definition}
    (accepted : Composition.classify definitions assumption = some (.closed definition))
    {body : Composition.CheckedBody} (stored : definition.body = some body)
    (s : State) (arguments : List Argument) :
    Composition.invokeResolution assumption (.closed definition) s arguments =
      invoke body.fn.signature s arguments := by
  obtain ⟨_, _, certifiedDefinition, _⟩ := Composition.closed_has_evidence accepted
  obtain ⟨_, stored', _, signature⟩ := Composition.certified_body certifiedDefinition
  rw [stored] at stored'
  cases stored'
  show invoke definition.contract.signature s arguments = _
  rw [signature]

end Mettapedia.Ownership.Frame
