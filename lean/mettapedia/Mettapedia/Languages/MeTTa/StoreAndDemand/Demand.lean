import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Machines.HEProducerCompletion
import Mettapedia.Machines.Cursor.OwnedLifecycle

/-!
# Dialect observations of first-answer demand

The finite search contracts consume the existing `LibTransform.Search`; they do
not assume a rollback store. The independent cursor contract in
`Machines/StoreAndDemand/FirstAnswer.lean` covers arbitrary live producers and
scheduler suspension. A full collection here is a completed observation, not a
claim that every language computation terminates.

HE's error-valued frontier and PeTTa's raised-fault continuation are kept separate.
No theorem moves HE operand evaluation or preferred-success completion across
a first-demand boundary. Storage cancellation uses the existing owned lifecycle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.Demand

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform
open Mettapedia.Machines

variable {World Answer Candidate : Type}

/-- Collection publishes the whole completed answer list and the reached world. -/
def collapse (producer : Search World Answer) : Search World (List Answer) := fun world =>
  let result := (producer world).drain
  .answer result.1 result.2 .done

theorem collapse_once (producer : Search World Answer) (world : World) :
    (collapse (Search.once producer) world).drain =
      match producer world with
      | .done after => ([[]], after)
      | .answer value after _ => ([[value]], after) := by
  unfold collapse Search.once
  cases producer world <;> rfl

/-- Every continuation after the selected answer is erased by the first-answer consumer. -/
theorem once_ignores_suffix (value : Answer) (world : World)
    (first second : World → Trace World Answer) :
    Search.once (fun _ => .answer value world first) world =
      Search.once (fun _ => .answer value world second) world := rfl

/-- An answerless branch can still change the world seen by the next branch. -/
theorem silent_branch_continues_from_reached_world
    (branch : Candidate → Search World Answer) (candidate : Candidate) (rest : List Candidate)
    (before after : World) (silent : branch candidate before = .done after) :
    ((Search.superpose (candidate :: rest)).bind branch) before =
      ((Search.superpose rest).bind branch) after := by
  simp [Search.superpose, Search.bind, Trace.bind, Trace.append, silent]

/-- A whole prefix of answerless branches preserves its accumulated effects. -/
theorem silent_prefix (branch : Candidate → Search World Answer)
    (effect : Candidate → World → World) (earlier later : List Candidate) (world : World)
    (silent : ∀ candidate ∈ earlier, ∀ state, branch candidate state = .done (effect candidate state)) :
    ((Search.superpose (earlier ++ later)).bind branch) world =
      ((Search.superpose later).bind branch)
        (earlier.foldl (fun state candidate => effect candidate state) world) := by
  induction earlier generalizing world with
  | nil => rfl
  | cons candidate rest ih =>
      rw [List.cons_append, silent_branch_continues_from_reached_world branch candidate
        (rest ++ later) world (effect candidate world) (silent candidate List.mem_cons_self world)]
      exact ih _ (fun candidate member => silent candidate (List.mem_cons_of_mem _ member))

/-- Permuting pure values preserves their complete bag and leaves the world unchanged. -/
theorem pure_complete_bag (first second : List Answer) (world : World)
    (sameBag : first.Perm second) :
    ((Search.superpose first world).drain.1).Perm ((Search.superpose second world).drain.1) ∧
      (Search.superpose first world).drain.2 = (Search.superpose second world).drain.2 := by
  simpa using And.intro sameBag (rfl : world = world)

/-- Operand preparation can be required before a choice producer becomes available. -/
def oncePrepared (prepare : World → List Answer × World) : Search World Answer := fun world =>
  let prepared := prepare world
  Search.once (Search.superpose prepared.1) prepared.2

theorem preparation_effects_precede_first (prepare : World → List Answer × World)
    (before after : World) (value : Answer) (rest : List Answer)
    (prepared : prepare before = (value :: rest, after)) :
    (oncePrepared prepare before).drain = ([value], after) := by
  simp [oncePrepared, prepared, Search.once, Search.superpose]

namespace Controls

/-- Candidate zero performs an effect but yields nothing; candidate two is an unused tail. -/
def branch : Nat → Search Nat Nat
  | 0 => fun world => .done (world + 1)
  | 1 => fun world => .answer 7 (world + 10) .done
  | _ => fun world => .answer 8 (world + 1000) .done

theorem first_answer_is_not_first_candidate :
    (Search.once ((Search.superpose [0, 1, 2]).bind branch) 0).drain = ([7], 11) := rfl

theorem full_drain_runs_later_effects :
    (((Search.superpose [0, 1, 2]).bind branch) 0).drain = ([7, 8], 1011) := rfl

theorem collapse_once_retains_earlier_effects :
    (collapse (Search.once ((Search.superpose [0, 1, 2]).bind branch)) 0).drain =
      ([[7]], 11) := rfl

/-- Equal bags do not license changing the first answer. -/
theorem bag_equality_does_not_preserve_first :
    ([1, 2] : List Nat).Perm [2, 1] ∧
      (Search.once (Search.superpose [1, 2]) ()).drain ≠
        (Search.once (Search.superpose [2, 1]) ()).drain := by
  exact ⟨List.Perm.swap _ _ _, by decide⟩

def orderedEffect : Bool → Search Nat Nat
  | false => fun world => .answer 7 (world * 2) .done
  | true => fun world => .answer 7 (world + 1) .done

/-- Even equal complete answer lists do not erase order-sensitive store effects. -/
theorem complete_bag_does_not_preserve_effects :
    (((Search.superpose [false, true]).bind orderedEffect) 1).drain = ([7, 7], 3) ∧
    (((Search.superpose [true, false]).bind orderedEffect) 1).drain = ([7, 7], 4) := by
  exact ⟨rfl, rfl⟩

end Controls

section Errors

variable {Fault Value State Pause Result : Type}

def isError : Except Fault Value → Bool
  | .error _ => true
  | .ok _ => false

/-- At an HE preferred-success boundary an error remains an ordinary value if all rows err. -/
theorem he_all_errors_keep_multiplicity (faults : List Fault) :
    HEProducerCompletion.reference (isError (Value := Value)) true (faults.map Except.error) =
      faults.map Except.error := by
  induction faults with
  | nil => rfl
  | cons fault rest ih => simp [HEProducerCompletion.reference, isError, List.any_map]

theorem he_later_success_displaces_error (fault : Fault) (value : Value) :
    HEProducerCompletion.reference isError true [Except.error fault, Except.ok value] =
      [Except.ok value] := rfl

/-- Selecting the raw first row before HE completion would return a different result. -/
theorem he_error_prefix_is_not_completed_first (fault : Fault) (value : Value) :
    ([Except.error fault, Except.ok value].head?) ≠
      (HEProducerCompletion.reference isError true [Except.error fault, Except.ok value]).head? := by
  simp [HEProducerCompletion.reference, isError]

/-- PeTTa raising invokes the fault continuation, not the ordinary answer continuation. -/
def raise (fault : Fault) : OrderedProtocol.Kernel State World Fault Pause Result :=
  fun _ _ _ _ onFault _ world => onFault fault world

theorem petta_raise_stops_sequence (fault : Fault)
    (later : OrderedProtocol.Kernel State World Fault Pause Result) :
    OrderedProtocol.sequence (raise fault) later = raise fault := rfl

end Errors

section Ownership

open Mettapedia.Machines.Cursor.OwnedLifecycle
open Mettapedia.Machines.ResourceOwnership

variable {Owner Address Payload : Type} [DecidableEq Owner] [DecidableEq Address]

/-- Publish the selected answer before closing its producer. Earlier world effects and all
selected cells survive, including duplicate answer occurrences backed by one object. -/
theorem publish_then_close
    (session : Session Owner Address Payload World) (dead : Finset Owner) (caller : Owner)
    (answers : List Address) (outside : caller ∉ dead)
    (allocated : ∀ address ∈ answers, address ∈ session.heap.allocated) :
    (commit session dead caller answers).world = session.world ∧
      observe (commit session dead caller answers).heap answers = observe session.heap answers ∧
      ∀ owner address, owner ∈ dead →
        (owner, address) ∉ (commit session dead caller answers).roots := by
  refine ⟨commit_world _ _ _ _, commit_preserves_selected_observation _ _ _ _ outside allocated, ?_⟩
  intro owner address gone
  simp [Mettapedia.Machines.Cursor.OwnedLifecycle.commit, commitRoots, mem_cancel, gone]

/-- Closing reclaims an abandoned cell only if no surviving owner or published answer reaches it. -/
theorem close_reclaims_unused_without_rollback
    (session : Session Owner Address Payload World) (dead : Finset Owner) (caller : Owner)
    (answers : List Address) (outside : caller ∉ dead) (unused : Address)
    (notOuter : ¬ Live session.heap (cancel session.roots dead) unused)
    (notAnswer : ¬ Live session.heap (answerRoots caller answers) unused) :
    (commit session dead caller answers).heap.lookup unused = none ∧
      (commit session dead caller answers).world = session.world :=
  ⟨commit_reclaims_unprotected session dead caller answers outside unused notOuter notAnswer,
   commit_world session dead caller answers⟩

end Ownership
end Mettapedia.Languages.MeTTa.StoreAndDemand.Demand
