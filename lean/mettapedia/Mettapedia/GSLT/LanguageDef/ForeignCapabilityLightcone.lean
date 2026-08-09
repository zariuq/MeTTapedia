import Mettapedia.Machines.ConeDuality
import Mathlib.Data.Multiset.AddSub

/-!
# Foreign capabilities as located causal authority

This module separates immutable foreign values from identity-bearing resources.
A resource handle is interpretable only where a matching live lease is present.
Without such authority the boundary returns the original atom unchanged: it
does not manufacture an error or an empty relational branch.

The state has two layers:

* an append-only event history, which is monotone along the forward cone;
* a current authority frontier, which can grow, move, share, or shrink.

Thus release preserves knowledge that release occurred while ending operational
authority.  Transfer and sharing are located transitions suitable for a future
rho/channel realization.  Borrowing is delimited: its lease exists only inside
the supplied continuation and cannot appear in the returned frontier.

No project-specific axioms are introduced.
-/

namespace Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

open Mettapedia.Machines
open Set

universe uProvider uResource uLocation uAtom uOperation uResult uFault

/-- Resource permissions have distinct structural laws.  Owned authority may
move, shared authority may be copied deliberately, and a borrow is scoped. -/
inductive Permission where
  | owned
  | shared
  | borrowed
  deriving DecidableEq, Repr

/-- A nominal resource identity.  Provider and generation are part of the
identity, so a slot reused by one provider does not revive an old handle. -/
structure Handle (Provider : Type uProvider) (Resource : Type uResource) where
  provider : Provider
  resource : Resource
  generation : Nat
  deriving DecidableEq, Repr

/-- One located authority occurrence.  Multiplicity is intentional: shared
leases held at two locations are two occurrences, not one structural fact. -/
structure Lease (Provider : Type uProvider) (Resource : Type uResource)
    (Location : Type uLocation) where
  handle : Handle Provider Resource
  holder : Location
  permission : Permission
  deriving DecidableEq, Repr

/-- The live authority frontier is order-insensitive but occurrence-sensitive. -/
abbrev Frontier (Provider : Type uProvider) (Resource : Type uResource)
    (Location : Type uLocation) := Multiset (Lease Provider Resource Location)

/-- Executable authority test over the three permission constructors. -/
def authorizedB {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    (frontier : Frontier Provider Resource Location) (holder : Location)
    (handle : Handle Provider Resource) : Bool :=
  decide (({ handle := handle, holder := holder, permission := .owned } :
      Lease Provider Resource Location) ∈ frontier) ||
  decide (({ handle := handle, holder := holder, permission := .shared } :
      Lease Provider Resource Location) ∈ frontier) ||
  decide (({ handle := handle, holder := holder, permission := .borrowed } :
      Lease Provider Resource Location) ∈ frontier)

/-- A handle is understood at a location exactly when one live lease occurrence
for that nominal handle is present there. -/
def Authorized {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    (frontier : Frontier Provider Resource Location) (holder : Location)
    (handle : Handle Provider Resource) : Prop :=
  authorizedB frontier holder handle = true

/-- The boundary keeps inert syntax, successful values, and genuine faults
separate.  Relational emptiness belongs to the surrounding occurrence bag and
is deliberately not represented by this type. -/
inductive BoundaryOutcome (Atom : Type uAtom) (Result : Type uResult)
    (Fault : Type uFault) where
  | inert (original : Atom)
  | returned (result : Result)
  | fault (fault : Fault)
  deriving DecidableEq, Repr

/-- Interpret a foreign operation only in the presence of located authority.
The native operation may return a value or a genuine host fault; lack of
authority always preserves the original atom. -/
def dispatch {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation} {Atom : Type uAtom}
    {Operation : Type uOperation} {Result : Type uResult} {Fault : Type uFault}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    (run : Operation → Handle Provider Resource → Except Fault Result)
    (frontier : Frontier Provider Resource Location) (holder : Location)
    (handle : Handle Provider Resource) (operation : Operation)
    (original : Atom) : BoundaryOutcome Atom Result Fault :=
  match authorizedB frontier holder handle with
  | true =>
    match run operation handle with
    | .ok result => .returned result
    | .error fault => .fault fault
  | false => .inert original

/-- The central MeTTa law: absent authority declines interpretation and leaves
the original syntax inert. -/
theorem dispatch_eq_inert_of_not_authorized
    {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation} {Atom : Type uAtom}
    {Operation : Type uOperation} {Result : Type uResult} {Fault : Type uFault}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    (run : Operation → Handle Provider Resource → Except Fault Result)
    (frontier : Frontier Provider Resource Location) (holder : Location)
    (handle : Handle Provider Resource) (operation : Operation)
    (original : Atom) (unavailable : ¬ Authorized frontier holder handle) :
    dispatch run frontier holder handle operation original = .inert original := by
  have unavailableB : authorizedB frontier holder handle = false :=
    Bool.eq_false_of_not_eq_true unavailable
  simp [dispatch, unavailableB]

/-- A host fault is observable only after authority has admitted the call. -/
theorem dispatch_eq_fault_of_authorized
    {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation} {Atom : Type uAtom}
    {Operation : Type uOperation} {Result : Type uResult} {Fault : Type uFault}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    (run : Operation → Handle Provider Resource → Except Fault Result)
    (frontier : Frontier Provider Resource Location) (holder : Location)
    (handle : Handle Provider Resource) (operation : Operation)
    (original : Atom) {fault : Fault}
    (available : Authorized frontier holder handle)
    (fails : run operation handle = .error fault) :
    dispatch run frontier holder handle operation original = .fault fault := by
  simp [Authorized] at available
  simp [dispatch, available, fails]

/-- Persistent transitions append exact causal events. -/
inductive Action (Provider : Type uProvider) (Resource : Type uResource)
    (Location : Type uLocation) where
  | release (lease : Lease Provider Resource Location)
  | transfer (lease : Lease Provider Resource Location) (target : Location)
  | share (lease : Lease Provider Resource Location) (target : Location)
  deriving DecidableEq, Repr

/-- A world retains exact history separately from its currently live leases. -/
structure World (Provider : Type uProvider) (Resource : Type uResource)
    (Location : Type uLocation) where
  frontier : Frontier Provider Resource Location
  history : List (Action Provider Resource Location)
  deriving DecidableEq

/-- Located resource transitions.  Transfer cannot persist a borrow, and share
is available only for explicitly shared authority. -/
inductive Step {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location] :
    World Provider Resource Location →
      Action Provider Resource Location →
      World Provider Resource Location → Prop where
  | release (world) (lease) (present : lease ∈ world.frontier) :
      Step world (.release lease)
        { frontier := Multiset.erase world.frontier lease
          history := world.history ++ [.release lease] }
  | transfer (world) (lease) (target)
      (present : lease ∈ world.frontier)
      (persistent : lease.permission ≠ .borrowed) :
      Step world (.transfer lease target)
        { frontier := { lease with holder := target } ::ₘ
            Multiset.erase world.frontier lease
          history := world.history ++ [.transfer lease target] }
  | share (world) (lease) (target)
      (present : lease ∈ world.frontier)
      (copyable : lease.permission = .shared) :
      Step world (.share lease target)
        { frontier := { lease with holder := target } ::ₘ world.frontier
          history := world.history ++ [.share lease target] }

/-- Forget the action label to obtain the production relation used by the
generic lightcone construction. -/
def StepRel {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    (source target : World Provider Resource Location) : Prop :=
  ∃ action, Step source action target

/-- Every persistent transition appends one event to causal history. -/
theorem step_history_prefix
    {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    {source target : World Provider Resource Location}
    {action : Action Provider Resource Location}
    (step : Step source action target) :
    source.history.IsPrefix target.history := by
  cases step <;> simp

/-- Exact history remains monotone along every finite resource path, even
though the current authority frontier may shrink after release. -/
theorem reaches_history_prefix
    {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    {source target : World Provider Resource Location}
    (path : Reaches StepRel source target) :
    source.history.IsPrefix target.history := by
  induction path with
  | refl => exact List.prefix_refl _
  | tail _ edge induction =>
      obtain ⟨_, labelled⟩ := edge
      exact induction.trans (step_history_prefix labelled)

/-- Lightcone form of causal-history persistence. -/
theorem futureCone_preserves_history
    {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation}
    [DecidableEq Provider] [DecidableEq Resource] [DecidableEq Location]
    {source target : World Provider Resource Location}
    (future : target ∈ forwardCone StepRel ({source} : Set _)) :
    source.history.IsPrefix target.history := by
  obtain ⟨origin, atSource, path⟩ := future
  simp only [Set.mem_singleton_iff] at atSource
  subst origin
  exact reaches_history_prefix path

/-- A borrow is a delimited observation: it is present for the continuation,
but the returned persistent frontier is definitionally the original one. -/
structure BorrowObservation
    (Provider : Type uProvider) (Resource : Type uResource)
    (Location : Type uLocation) (Result : Type uResult) where
  during : Result
  after : Frontier Provider Resource Location

/-- Run a continuation with a temporary borrowed lease. -/
def withBorrow
    {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation} {Result : Type uResult}
    (frontier : Frontier Provider Resource Location)
    (lease : Lease Provider Resource Location) (borrower : Location)
    (body : Frontier Provider Resource Location → Result) :
    BorrowObservation Provider Resource Location Result :=
  let borrowedLease : Lease Provider Resource Location :=
    { handle := lease.handle
      holder := borrower
      permission := .borrowed }
  { during := body (borrowedLease ::ₘ frontier)
    after := frontier }

@[simp] theorem withBorrow_does_not_escape
    {Provider : Type uProvider} {Resource : Type uResource}
    {Location : Type uLocation} {Result : Type uResult}
    (frontier : Frontier Provider Resource Location)
    (lease : Lease Provider Resource Location) (borrower : Location)
    (body : Frontier Provider Resource Location → Result) :
    (withBorrow frontier lease borrower body).after = frontier :=
  rfl

/-! ## Executable positive and negative canaries -/

private def demoHandle : Handle Bool Nat :=
  { provider := true, resource := 7, generation := 1 }

private def nextGenerationHandle : Handle Bool Nat :=
  { provider := true, resource := 7, generation := 2 }

private def demoOwned : Lease Bool Nat Bool :=
  { handle := demoHandle, holder := false, permission := .owned }

private def demoShared : Lease Bool Nat Bool :=
  { handle := demoHandle, holder := false, permission := .shared }

private def successfulRun (_ : Unit) (handle : Handle Bool Nat) :
    Except String Nat :=
  .ok handle.resource

private def failingRun (_ : Unit) (_ : Handle Bool Nat) :
    Except String Nat :=
  .error "host-fault"

/-- Positive: a live located capability authorizes interpretation. -/
example :
    dispatch successfulRun ({demoOwned} : Frontier Bool Nat Bool)
      false demoHandle () "original" = .returned 7 := by
  simp [dispatch, authorizedB, demoOwned, demoHandle, successfulRun]

/-- Negative: the same handle outside its authority location stays inert. -/
example :
    dispatch successfulRun ({demoOwned} : Frontier Bool Nat Bool)
      true demoHandle () "original" = .inert "original" := by
  simp [dispatch, authorizedB, demoOwned, demoHandle]

/-- Negative: an old generation stays inert after slot reuse. -/
example :
    dispatch successfulRun
      ({{ handle := nextGenerationHandle, holder := false,
          permission := .owned }} : Frontier Bool Nat Bool)
      false demoHandle () "old-generation" = .inert "old-generation" := by
  simp [dispatch, authorizedB, demoHandle, nextGenerationHandle]

/-- A singleton release is a real causal step whose target has no authority. -/
example : Step
    ({ frontier := {demoOwned}, history := [] } : World Bool Nat Bool)
    (.release demoOwned)
    ({ frontier := 0, history := [.release demoOwned] } : World Bool Nat Bool) := by
  simpa using Step.release
    ({ frontier := {demoOwned}, history := [] } : World Bool Nat Bool)
    demoOwned (by simp)

/-- After release, the exact same syntax is inert rather than an error or an
empty relational result. -/
example :
    dispatch successfulRun (0 : Frontier Bool Nat Bool)
      false demoHandle () "stale-call" = .inert "stale-call" := by
  simp [dispatch, authorizedB]

/-- A fault is exposed when and only when a live lease authorizes the call. -/
example :
    dispatch failingRun ({demoOwned} : Frontier Bool Nat Bool)
      false demoHandle () "call" = .fault "host-fault" := by
  simp [dispatch, authorizedB, demoOwned, demoHandle, failingRun]

example :
    dispatch failingRun (0 : Frontier Bool Nat Bool)
      false demoHandle () "call" = .inert "call" := by
  simp [dispatch, authorizedB]

/-- Transfer moves an owned capability instead of duplicating it. -/
example : Step
    ({ frontier := {demoOwned}, history := [] } : World Bool Nat Bool)
    (.transfer demoOwned true)
    ({ frontier := {{ demoOwned with holder := true }},
       history := [.transfer demoOwned true] } : World Bool Nat Bool) := by
  simpa using Step.transfer
    ({ frontier := {demoOwned}, history := [] } : World Bool Nat Bool)
    demoOwned true (by simp) (by decide)

/-- Sharing is explicitly available for shared permission and preserves both
located authority occurrences. -/
example : Step
    ({ frontier := {demoShared}, history := [] } : World Bool Nat Bool)
    (.share demoShared true)
    ({ frontier := { { demoShared with holder := true }, demoShared },
       history := [.share demoShared true] } : World Bool Nat Bool) := by
  simpa using Step.share
    ({ frontier := {demoShared}, history := [] } : World Bool Nat Bool)
    demoShared true (by simp) rfl

/-- The borrow is visible during its continuation. -/
example :
    (withBorrow (0 : Frontier Bool Nat Bool) demoOwned true
      (fun frontier => Authorized frontier true demoHandle)).during := by
  simp [withBorrow, Authorized, authorizedB, demoOwned, demoHandle]

/-- The borrow cannot escape into the returned persistent frontier. -/
example :
    (withBorrow (0 : Frontier Bool Nat Bool) demoOwned true
      (fun frontier => Authorized frontier true demoHandle)).after = 0 :=
  rfl

end Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
