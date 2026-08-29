import Mettapedia.GSLT.Core.GivenClauseLoop

/-!
# Observation-indexed default control

This module separates three questions which an evaluator must not collapse:

* what the consumer observes;
* whether simultaneous activation is semantically serializable;
* how much passive work the controller selects at one boundary.

The default dispatch is consequently neither depth-first nor breadth-first.
First-result and finite-prefix demands constrain the readout but do not choose
a branch discipline.  Direct single-path execution requires a separate
branching certificate; complete batching requires an observation-relative
serializability certificate.  All other branching scopes retain a
mechanism-neutral controlled frontier.

A graded guard is carried by the observation demand but does not by itself
grant batching, pruning, or transition authority.  A future weighted `where`
surface may inhabit this parameter without changing the control law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ObservationDemandControl

universe uGuard uItem uState uView

/-- The amount and order of an answer observation. -/
inductive CompletionDemand where
  | first
  | finitePrefix (count : Nat)
  | completeBag
  | orderedStream
  | undetermined
deriving DecidableEq, Repr

/-- Consumer demand together with an optional semantic guard.  The guard is
kept abstract: Boolean guards, semiring grades, intervals, and evidence
thresholds need not share a representation. -/
structure ObservationDemand (Guard : Type uGuard) where
  completion : CompletionDemand
  guard : Option Guard := none
deriving Repr

/-- Bulk activation requires a semantic certificate.  Syntactic expansion or
the presence of a grade is not such a certificate. -/
inductive BatchAuthority where
  | singletonOnly
  | serializable
deriving DecidableEq, Repr

/-- Direct execution is licensed only when the scope has at most one live
successor path.  First-answer demand alone is not such a license. -/
inductive BranchAuthority where
  | general
  | singlePath
deriving DecidableEq, Repr

/-- Strategy-neutral activation shape chosen at a scope boundary.  Readout
limits remain in `CompletionDemand`; they are not frontier batch sizes. -/
inductive ActivationShape where
  | none
  | singlePath
  | controlled
  | bulk
deriving DecidableEq, Repr

structure Plan where
  readout : CompletionDemand
  activation : ActivationShape
deriving DecidableEq, Repr

/-- Exact scope-entry dispatch.  `controlled` leaves the concrete branching
discipline open; it does not imply FIFO, DFS, fairness, or a storage format.
`first` stops after a witness; it does not commit to a branch beforehand. -/
def dispatch {Guard : Type uGuard}
    (demand : ObservationDemand Guard)
    (branchAuthority : BranchAuthority)
    (batchAuthority : BatchAuthority) : Plan :=
  let activation :=
    match demand.completion with
    | .finitePrefix 0 => .none
    | .completeBag =>
        match branchAuthority, batchAuthority with
        | .singlePath, _ => .singlePath
        | .general, .serializable => .bulk
        | .general, .singletonOnly => .controlled
    | _ =>
        match branchAuthority with
        | .singlePath => .singlePath
        | .general => .controlled
  { readout := demand.completion, activation := activation }

/-- A static analysis either establishes the exact consuming frame or admits
that it does not know.  Unknown demand never guesses a more aggressive mode. -/
inductive StaticDemand (Guard : Type uGuard) where
  | exact (demand : ObservationDemand Guard)
  | unknown
deriving Repr

def dispatchStatic {Guard : Type uGuard}
    (summary : StaticDemand Guard)
    (branchAuthority : BranchAuthority)
    (batchAuthority : BatchAuthority) : Plan :=
  match summary with
  | .exact demand => dispatch demand branchAuthority batchAuthority
  | .unknown => { readout := .undetermined, activation := .controlled }

/-- A decidable audit of the authority exercised by a dispatch result. -/
def ActivationLawful {Guard : Type uGuard}
    (demand : ObservationDemand Guard)
    (branchAuthority : BranchAuthority)
    (batchAuthority : BatchAuthority)
    (shape : ActivationShape) : Prop :=
  match shape with
  | .none => demand.completion = .finitePrefix 0
  | .singlePath =>
      branchAuthority = .singlePath ∧
        demand.completion ≠ .finitePrefix 0
  | .bulk =>
      branchAuthority = .general ∧
        demand.completion = .completeBag ∧
        batchAuthority = .serializable
  | .controlled =>
      branchAuthority = .general ∧
        demand.completion ≠ .finitePrefix 0 ∧
        (demand.completion ≠ .completeBag ∨
          batchAuthority = .singletonOnly)

def PlanLawful {Guard : Type uGuard}
    (demand : ObservationDemand Guard)
    (branchAuthority : BranchAuthority)
    (batchAuthority : BatchAuthority)
    (plan : Plan) : Prop :=
  plan.readout = demand.completion ∧
    ActivationLawful demand branchAuthority batchAuthority plan.activation

/-- The dispatcher never grants an observation or batch authority which the
scope did not provide. -/
theorem dispatch_lawful {Guard : Type uGuard}
    (demand : ObservationDemand Guard)
    (branchAuthority : BranchAuthority)
    (batchAuthority : BatchAuthority) :
    PlanLawful demand branchAuthority batchAuthority
      (dispatch demand branchAuthority batchAuthority) := by
  rcases demand with ⟨completion, guard⟩
  constructor
  · rfl
  cases completion with
  | first => cases branchAuthority <;> simp [dispatch, ActivationLawful]
  | finitePrefix count =>
      cases count with
      | zero => simp [dispatch, ActivationLawful]
      | succ count => cases branchAuthority <;> simp [dispatch, ActivationLawful]
  | completeBag =>
      cases branchAuthority <;> cases batchAuthority <;>
        simp [dispatch, ActivationLawful]
  | orderedStream =>
      cases branchAuthority <;> simp [dispatch, ActivationLawful]
  | undetermined =>
      cases branchAuthority <;> simp [dispatch, ActivationLawful]

/-- Runtime observation frames are exact inputs to the same dispatcher; no
second policy semantics is introduced for dynamic scopes. -/
theorem exact_static_dispatch {Guard : Type uGuard}
    (demand : ObservationDemand Guard)
    (branchAuthority : BranchAuthority)
    (batchAuthority : BatchAuthority) :
    dispatchStatic (.exact demand) branchAuthority batchAuthority =
      dispatch demand branchAuthority batchAuthority :=
  rfl

/-- Conservative static uncertainty retains the open controlled boundary. -/
theorem unknown_static_dispatch {Guard : Type uGuard}
    (branchAuthority : BranchAuthority)
    (batchAuthority : BatchAuthority) :
    dispatchStatic (StaticDemand.unknown (Guard := Guard))
        branchAuthority batchAuthority =
      { readout := .undetermined, activation := .controlled } :=
  rfl

/-- A grade may refine later selection, but cannot manufacture a bulk license. -/
theorem guard_does_not_grant_bulk {Guard : Type uGuard}
    (guard : Guard) :
    dispatch
        ({ completion := .completeBag
           guard := some guard } : ObservationDemand Guard)
        .general .singletonOnly =
      { readout := .completeBag, activation := .controlled } :=
  rfl

/-! ## Observation-relative batch serializability -/

/-- Sequential activation of an authored batch. -/
def activateAll {State : Type uState} {Item : Type uItem}
    (step : State -> Item -> State) (initial : State) :
    List Item -> State :=
  List.foldl step initial

/-- Every serial ordering of the same occurrence batch has the same declared
observation.  This is the semantic license required by `.serializable`. -/
def SerializableAt {State : Type uState} {Item : Type uItem}
    {View : Type uView} (observe : State -> View)
    (step : State -> Item -> State) (initial : State)
    (batch : List Item) : Prop :=
  ∀ ordering, ordering.Perm batch ->
    observe (activateAll step initial ordering) =
      observe (activateAll step initial batch)

private theorem activateAll_append
    (initial batch : List Nat) :
    activateAll (fun state item => state ++ [item]) initial batch =
      initial ++ batch := by
  induction batch generalizing initial with
  | nil => simp [activateAll]
  | cons item tail inductionHypothesis =>
      change activateAll (fun state item => state ++ [item])
        (initial ++ [item]) tail = initial ++ item :: tail
      rw [inductionHypothesis]
      simp [List.append_assoc]

/-- Positive witness: append activation is serializable for a bag observer. -/
theorem append_is_serializable_for_bag
    (initial batch : List Nat) :
    SerializableAt
      (fun state : List Nat => (state : Multiset Nat))
      (fun state item => state ++ [item]) initial batch := by
  intro ordering permutation
  rw [activateAll_append, activateAll_append]
  have multisetEquality :
      (ordering : Multiset Nat) = (batch : Multiset Nat) :=
    Quot.sound permutation
  exact congrArg (fun suffix : Multiset Nat =>
    (initial : Multiset Nat) + suffix) multisetEquality

/-- Negative witness: the same activation is not serializable for an ordered
stream observer. -/
theorem append_not_serializable_for_stream :
    ¬ SerializableAt
        (fun state : List Nat => state)
        (fun state item => state ++ [item]) [] [1, 2] := by
  intro serializable
  have swapped := serializable [2, 1]
    (by decide : [2, 1].Perm [1, 2])
  simp [activateAll] at swapped

/-! ## Dispatch canaries -/

/-- First-answer demand stops the readout after a witness but does not commit
to the first branch before a witness exists. -/
theorem branching_first_remains_controlled {Guard : Type uGuard}
    (guard : Option Guard) :
    dispatch
        ({ completion := .first, guard := guard } :
          ObservationDemand Guard)
        .general .singletonOnly =
      { readout := .first, activation := .controlled } := by
  rfl

/-- A separate single-path certificate licenses frontier-free execution. -/
theorem single_path_first_uses_single_path {Guard : Type uGuard}
    (guard : Option Guard) :
    dispatch
        ({ completion := .first, guard := guard } :
          ObservationDemand Guard)
        .singlePath .singletonOnly =
      { readout := .first, activation := .singlePath } := by
  rfl

/-- A finite answer prefix is a readout limit, not a frontier batch size. -/
theorem branching_prefix_remains_controlled {Guard : Type uGuard}
    (guard : Option Guard) :
    dispatch
        ({ completion := .finitePrefix 2, guard := guard } :
          ObservationDemand Guard)
        .general .singletonOnly =
      { readout := .finitePrefix 2, activation := .controlled } := by
  rfl

theorem complete_serializable_uses_bulk {Guard : Type uGuard}
    (guard : Option Guard) :
    dispatch
        ({ completion := .completeBag, guard := guard } :
          ObservationDemand Guard)
        .general .serializable =
      { readout := .completeBag, activation := .bulk } := by
  rfl

theorem complete_unlicensed_remains_controlled {Guard : Type uGuard}
    (guard : Option Guard) :
    dispatch
        ({ completion := .completeBag, guard := guard } :
          ObservationDemand Guard)
        .general .singletonOnly =
      { readout := .completeBag, activation := .controlled } := by
  rfl

theorem zero_prefix_activates_nothing {Guard : Type uGuard}
    (guard : Option Guard) :
    dispatch
        ({ completion := .finitePrefix 0, guard := guard } :
          ObservationDemand Guard)
        .singlePath .serializable =
      { readout := .finitePrefix 0, activation := .none } := by
  rfl

#print axioms dispatch_lawful
#print axioms exact_static_dispatch
#print axioms unknown_static_dispatch
#print axioms guard_does_not_grant_bulk
#print axioms append_is_serializable_for_bag
#print axioms append_not_serializable_for_stream
#print axioms branching_first_remains_controlled
#print axioms single_path_first_uses_single_path
#print axioms branching_prefix_remains_controlled
#print axioms complete_serializable_uses_bulk
#print axioms complete_unlicensed_remains_controlled
#print axioms zero_prefix_activates_nothing

end Mettapedia.GSLT.Core.ObservationDemandControl
