import Mettapedia.Machines.HybridStorePublication
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ImmediatePublication

/-!
# Mixed-storage publication agrees with ordered transform deletion

The hybrid representation observes a bag. The ordered occurrence model retains
the stronger order information. This adapter proves that their deletion results
have the same bag when their input representations agree. It does not infer an
order from the hybrid bag or change scoped unification into value equality.
The studied fragment is completed exact-key selection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HybridImmediateRemoval

open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open PeTTaStoreSelection (atomFrames)

variable {O : Type} [DecidableEq O] (label : O → Atom)

def Represents (world : PreparedStoreProtocol.World O) (store : HybridShapeStore.Store Atom) : Prop :=
  HybridShapeStore.denote store = (world.rows.map label : Multiset Atom)

theorem accepted_bag_exact (world : PreparedStoreProtocol.World O)
    (store : HybridShapeStore.Store Atom) (keys : List Atom) (capacity count : Nat)
    (representation : Represents label world store)
    (accepted : (HybridStorePublication.removeAll (fun atom => decide (atom ∈ keys)) capacity store).1 =
      some count) :
    HybridShapeStore.denote
        (HybridStorePublication.removeAll (fun atom => decide (atom ∈ keys)) capacity store).2 =
      ((ImmediateStorePublication.immediate label world ⟨.erase keys, true⟩).2.rows.map label : Multiset Atom) := by
  have result := (HybridStorePublication.accepted_observation _ capacity store count accepted).1
  rw [result, representation]
  simp [ImmediateStorePublication.immediate, PreparedStoreProtocol.Admissible,
    PreparedStoreProtocol.Operation.made, ImmediateStorePublication.directRows,
    Multiset.filter_coe, List.filter_map, Function.comp_def]

/-- Successful hybrid deletion refines the bag projection of an actual
admitted ordered tcalc effect; the target is not another hybrid interpreter. -/
theorem accepted_realized (world : PreparedStoreProtocol.World O)
    (store : HybridShapeStore.Store Atom) (keys : List Atom) (capacity count : Nat)
    (representation : Represents label world store)
    (accepted : (HybridStorePublication.removeAll (fun atom => decide (atom ∈ keys)) capacity store).1 =
      some count)
    (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ permitted : (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, world.rows))
        (ImmediatePublication.request (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label world (.erase keys)),
      HybridShapeStore.denote
          (HybridStorePublication.removeAll (fun atom => decide (atom ∈ keys)) capacity store).2 =
        ((((OrderedStore.step atomFrames PUnit.unit label).result
          (ImmediatePublication.request (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label world (.erase keys)) permitted).2.map label) :
          Multiset Atom) := by
  have allowed : PreparedStoreProtocol.Admissible world (.erase keys : PreparedStoreProtocol.Operation O Atom) := by
    simp [PreparedStoreProtocol.Admissible, PreparedStoreProtocol.Operation.made]
  refine ⟨ImmediatePublication.admitted atomFrames PUnit.unit label world (.erase keys)
    allowed knowledge consistent, ?_⟩
  rw [ImmediatePublication.result_exact atomFrames PUnit.unit label world ⟨.erase keys, true⟩
    rfl allowed knowledge consistent]
  exact accepted_bag_exact label world store keys capacity count representation accepted

namespace Controls

def value (occurrence : Nat) : Atom := if occurrence < 2 then .symbol "a" else .symbol "b"
def world : PreparedStoreProtocol.World Nat := ⟨3, [0, 1, 2], by decide⟩
def mixed : HybridShapeStore.Store Atom := ⟨{.symbol "a"}, {.symbol "a", .symbol "b"}⟩

theorem input_has_two_distinct_occurrences_of_one_value : Represents value world mixed := by
  unfold Represents
  decide

theorem refusal_and_success_keep_their_distinct_observations :
    (HybridStorePublication.removeAll (· == .symbol "a") 0 mixed).1 = none ∧
      (HybridStorePublication.removeAll (· == .symbol "a") 1 mixed).1 = some 2 := by decide

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.HybridImmediateRemoval
