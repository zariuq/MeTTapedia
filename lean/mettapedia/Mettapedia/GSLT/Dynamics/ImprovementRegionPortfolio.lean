import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.Machines.ImprovementSourceProgram

/-!
# Keyed upsert as a completed-block portfolio instance

The source runs read/erase/put primitives; the worker runs a keyed upsert.
Both execute through the existing primitive-program interpreter. The boundary
retains the entire answer packet, resulting store, completion or residual and
source debit. The local theorem does not identify intermediate pause points,
nor replace the source driver's round count with a solver iteration count.

The input store is isolated for this completed block. A concurrent physical
implementation still needs the validation and publication law; this adapter
does not declare all remove/add sequences atomic.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.Improvement

open Mettapedia.Machines
open KeyedImprovement KeyedImprovement.SourceProgram
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Cursor.PrimitiveProgram

variable {Key : Type} [DecidableEq Key]

abbrev Result (Key : Type) :=
  Nat × ((Except Empty (List Key) ⊕ Except Empty (Prog Op Ret (List Key))) × Store Key Nat)

def questions (Key : Type) : RegionObservations.Family (Result Key) where
  Question := Result Key → Bool
  Answer _ := Bool
  read question result := question result

def boundary (key : Key) (candidate : Nat) :
    Boundary (Store Key Nat) (Result Key) (Result Key) where
  source store := direct (step key) (sourceCharge key) 4 (.ok (source key candidate)) store
  summarize := id
  future := questions Key
  sufficient _ _ same _ := congrArg _ same

def region (key : Key) (candidate : Nat) : CertifiedRegion (boundary key candidate) Nat where
  regime := 0
  Artifact := Result Key
  attempt store := .committed (direct (step key) (sourceCharge key) 2 (.ok (native key candidate)) store)
  decode := id
  restores _ _ impossible := by cases impossible
  exact store _ committed := by
    cases committed
    exact (completed_source_native store key candidate).symm

theorem every_selected_route_preserves_source_debit (key : Key) (candidate : Nat)
    (store : Store Key Nat) (routes : List (Candidate (boundary key candidate) Nat)) :
    (RegionPortfolio.execute store routes).1 =
      (KeyedImprovement.Information.sourcePlan candidate (store key)).debit := by
  rw [RegionPortfolio.execute_exact]
  change (direct (step key) (sourceCharge key) 4 (.ok (source key candidate)) store).1 = _
  rw [source_completed]

theorem every_selected_route_preserves_store (key : Key) (candidate : Nat)
    (store : Store Key Nat) (routes : List (Candidate (boundary key candidate) Nat)) :
    (RegionPortfolio.execute store routes).2.2 = (improve store key candidate).1 := by
  rw [RegionPortfolio.execute_exact]
  change (direct (step key) (sourceCharge key) 4 (.ok (source key candidate)) store).2.2 = _
  rw [source_completed]

theorem every_selected_route_preserves_answers (key : Key) (candidate : Nat)
    (store : Store Key Nat) (routes : List (Candidate (boundary key candidate) Nat)) :
    (RegionPortfolio.execute store routes).2.1 =
      .inl (.ok (answers key (improve store key candidate).2)) := by
  rw [RegionPortfolio.execute_exact]
  change (direct (step key) (sourceCharge key) 4 (.ok (source key candidate)) store).2.1 = _
  rw [source_completed]

namespace Controls

def ten : Store Unit Nat := fun _ => some 10

def cheap : Candidate (boundary () 7) Nat := ⟨region () 7, fun _ => ⟨1, 1⟩, 0⟩

theorem stores_seven_and_retains_three_source_calls :
    (RegionPortfolio.execute ten [cheap]).2.2 () = some 7 ∧
      (RegionPortfolio.execute ten [cheap]).1 = 3 := by decide

theorem unchanged_is_an_empty_answer_packet :
    (region () 12).execute ten |>.2.1 = .inl (.ok []) := by rfl

theorem intermediate_observation_remains_outside_atomic_admission :
    (direct (step ()) (sourceCharge ()) 2 (.ok (source () 7)) ten).2.2 () = none ∧
      (direct (step ()) (sourceCharge ()) 1 (.ok (native () 7)) ten).2.2 () = some 7 := by decide

end Controls

#print axioms region
#print axioms every_selected_route_preserves_source_debit
#print axioms every_selected_route_preserves_store
#print axioms every_selected_route_preserves_answers

end Mettapedia.GSLT.Dynamics.ObservationQualified.Improvement
