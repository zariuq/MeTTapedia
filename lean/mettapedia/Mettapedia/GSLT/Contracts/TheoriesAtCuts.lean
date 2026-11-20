import Mettapedia.GSLT.Contracts.ReadWindowCuts

/-!
# A theory-qualified read at one actual cut

Resolving a space can discover both a backing store and a comparison
port. The ordered reply of a read depends on these three coordinates:
the resolution, the chosen declaration, and the actual rows. A
previous version of each separately is not a read of their joint state.

This profile uses a pure Boolean ground test on occurrences. It
instantiates the existing read-window theorem; it does not prescribe
the equality, lock, lookup scheme, or snapshot acquisition mechanism.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.TheoriesAtCuts

open Mettapedia.Machines.ReadOnlyQuery (Program run)
open Mettapedia.GSLT.Contracts.ReadWindowCuts

universe u

variable {Alias Slot Space Row Term : Type u}

inductive Request (Alias Slot Space : Type u) where
  | resolve (key : Alias)
  | test (key : Slot)
  | rows (key : Space)

inductive Reply (Slot Space Row Term : Type u) where
  | resolution (chosen : Option (Slot × Space))
  | comparison (test : Term → Term → Bool)
  | occurrences (rows : List (Row × Term))

structure World (Alias Slot Space Row Term : Type u) where
  resolve : Alias → Option (Slot × Space)
  comparison : Slot → Term → Term → Bool
  occurrences : Space → List (Row × Term)

namespace World

def view (store : World Alias Slot Space Row Term) :
    Request Alias Slot Space → Reply Slot Space Row Term
  | .resolve key => .resolution (store.resolve key)
  | .test slot => .comparison (store.comparison slot)
  | .rows space => .occurrences (store.occurrences space)

def answer (store : World Alias Slot Space Row Term) (aliasKey : Alias) (query : Term) :
    Option (List Row) :=
  (store.resolve aliasKey).map fun (port, space) =>
    ((store.occurrences space).filter fun entry => store.comparison port query entry.2).map Prod.fst

end World

def query (aliasKey : Alias) (call : Term) :
    Program (Request Alias Slot Space) (Reply Slot Space Row Term) (Option (List Row)) :=
  .read (.resolve aliasKey) fun
    | .resolution (some (port, space)) =>
      .read (.test port) fun
        | .comparison test => .read (.rows space) fun
          | .occurrences rows =>
              .pure (some ((rows.filter fun entry => test call entry.2).map Prod.fst))
          | _ => .pure none
        | _ => .pure none
    | _ => .pure none

theorem query_answer (store : World Alias Slot Space Row Term) (aliasKey : Alias) (call : Term) :
    (run store.view (query aliasKey call)).answer = store.answer aliasKey call := by
  cases resolution : store.resolve aliasKey with
  | none => simp [query, run, World.view, World.answer, resolution]
  | some keys =>
      obtain ⟨port, space⟩ := keys
      simp [query, run, World.view, World.answer, resolution]

theorem query_reads_of_resolved (store : World Alias Slot Space Row Term)
    {aliasKey : Alias} {port : Slot} {space : Space} (call : Term)
    (resolved : store.resolve aliasKey = some (port, space)) :
    ((run store.view (query aliasKey call)).reads.map Prod.fst) =
      [.resolve aliasKey, .test port, .rows space] := by
  simp [query, run, World.view, resolved]

theorem query_reads_of_unresolved (store : World Alias Slot Space Row Term)
    {aliasKey : Alias} (call : Term) (missing : store.resolve aliasKey = none) :
    ((run store.view (query aliasKey call)).reads.map Prod.fst) = [.resolve aliasKey] := by
  simp [query, run, World.view, missing]

/-- The three possibly discovered coordinates may be sampled in
different windows. If their validations overlap, the result and the
ordered transcript belong to one actual state, using the same
declarations and rows at that state. -/
theorem query_on_actual_cut {Stamp : Type*} [PartialOrder Stamp] {steps : Nat}
    (history : Cut steps → World Alias Slot Space Row Term)
    (stamp : Cut steps → Request Alias Slot Space → Stamp)
    (monotone : ∀ (i : Fin steps) key, stamp i.castSucc key ≤ stamp i.succ key)
    (frame : ∀ (i : Fin steps) key, stamp i.castSucc key = stamp i.succ key →
      (history i.castSucc).view key = (history i.succ).view key)
    (aliasKey : Alias) (call : Term)
    (reads : List (Request Alias Slot Space × Window (Cut steps))) (answer : Option (List Row))
    (capture : Captured (fun cut => (history cut).view) (query aliasKey call) reads answer)
    (valid : ∀ entry ∈ reads, stamp entry.2.start entry.1 = stamp entry.2.finish entry.1)
    (cross : Window.CrossOrdered (reads.map Prod.snd)) :
    ∃ cut : Cut steps, (history cut).answer aliasKey call = answer ∧
      (run (history cut).view (query aliasKey call)).reads =
        recordedReads (fun cut => (history cut).view) reads := by
  let footprint := fun key : Request Alias Slot Space => ({key} : Set (Request Alias Slot Space))
  have license : Discipline (fun cut => (history cut).view) footprint stamp :=
    ⟨monotone, fun i key same => frame i key (same (Set.mem_singleton key))⟩
  have checks : ∀ entry ∈ reads,
      Set.EqOn (stamp entry.2.start) (stamp entry.2.finish) (footprint entry.1) := by
    intro entry member key inFootprint
    have eq : key = entry.1 := inFootprint
    exact eq.symm ▸ valid entry member
  have replay := capture.replay_at_jointStart license checks cross
  let cut := Window.jointStart (reads.map Prod.snd)
  refine ⟨cut, ?_, congrArg (fun result => result.reads) replay⟩
  exact (query_answer (history cut) aliasKey call).symm.trans
    (congrArg (fun result => result.answer) replay)

namespace Controls

private abbrev ExampleWorld := World Unit Unit Unit Nat Bool
private def before : ExampleWorld :=
  ⟨fun _ => some ((), ()), fun _ a b => a == b, fun _ => [(7, true)]⟩
private def after : ExampleWorld :=
  ⟨before.resolve, fun _ _ _ => true, fun _ => []⟩
private def torn : ExampleWorld :=
  ⟨before.resolve, after.comparison, before.occurrences⟩

theorem neither_live_state_has_a_match :
    before.answer () false = some [] ∧ after.answer () false = some [] := ⟨rfl, rfl⟩

theorem mixing_valid_coordinates_invents_match :
    torn.answer () false = some [7] ∧
      ¬ ∃ cut : Bool, (if cut then after else before).answer () false = some [7] := by
  constructor
  · rfl
  · rintro ⟨cut, answer⟩
    cases cut <;> cases answer

end Controls

#print axioms query_reads_of_resolved
#print axioms query_reads_of_unresolved
#print axioms query_on_actual_cut
#print axioms Controls.mixing_valid_coordinates_invents_match

end Mettapedia.GSLT.Contracts.TheoriesAtCuts
