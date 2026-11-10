import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Optional recording of admitted store runs

The existing indexed step run is the semantic input. The recording traversal
appends one user-selected receipt per event. The plain traversal retains no
receipt list. Their state observations agree; receipt-sensitive observations
need not. The result does not erase a record that an evaluator consults to
choose its next step, nor does it certify native storage or machine code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.RunReceipts

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uReceipt uObservation

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)
  {Receipt : Type uReceipt}

/-- Receipt construction is explicit and can depend on the source state and firing. -/
def recorded (receipt : (s : State) → Firing s → Receipt) :
    {s : State} → P.Run s → List Receipt → State × List Receipt
  | s, .nil _, prior => (s, prior)
  | s, .cons firing _ rest, prior => recorded receipt rest (prior ++ [receipt s firing])

/-- Direct traversal has no recording parameter or accumulator. -/
def plain : {s : State} → P.Run s → State
  | s, .nil _ => s
  | _, .cons _ _ rest => plain rest

theorem plain_last {s : State} (run : P.Run s) : plain P run = run.last := by
  induction run with
  | nil => rfl
  | cons firing admitted rest ih => exact ih

/-- Recording preserves the source-indexed event order and the final state. -/
theorem recorded_exact (receipt : (s : State) → Firing s → Receipt)
    {s : State} (run : P.Run s) (prior : List Receipt) :
    recorded P receipt run prior =
      (run.last, prior ++ run.word.map (fun event => receipt event.1 event.2)) := by
  induction run generalizing prior with
  | nil => simp [recorded, Step.Run.last, Step.Run.word]
  | cons firing admitted rest ih =>
      simp [recorded, Step.Run.last, Step.Run.word, ih, List.append_assoc]

/-- Every state-only observation is preserved when receipt construction is omitted. -/
theorem erase_unobserved_receipts {Observation : Type uObservation}
    (observe : State → Observation) (receipt : (s : State) → Firing s → Receipt)
    {s : State} (run : P.Run s) (prior : List Receipt) :
    observe (recorded P receipt run prior).1 = observe (plain P run) := by
  rw [recorded_exact, plain_last]

/-- Receipt lists compose across the actual state reached by the first run. -/
theorem recorded_append (receipt : (s : State) → Firing s → Receipt)
    {s : State} (first : P.Run s) (second : P.Run first.last) (prior : List Receipt) :
    recorded P receipt (first.append second) prior =
      recorded P receipt second (recorded P receipt first prior).2 := by
  simp [recorded_exact, Step.Run.last_append, Step.Run.word_append, List.map_append,
    List.append_assoc]

/-- A record-count observer distinguishes recording a nonempty run from erasure. -/
theorem observed_receipts_cannot_be_erased
    (receipt : (s : State) → Firing s → Receipt)
    {s : State} (run : P.Run s) (prior : List Receipt) (nonempty : run.word ≠ []) :
    (recorded P receipt run prior).2.length ≠ prior.length := by
  rw [recorded_exact]
  simp only [List.length_append, List.length_map]
  have positive : 0 < run.word.length := List.length_pos_iff.mpr nonempty
  omega

/-- Logical work grades are independent of whether optional receipts are materialized. -/
def spent (charge : (s : State) → Firing s → Nat) {s : State} (run : P.Run s) : Nat :=
  Multiplicative.toAdd (run.account (fun s firing => Multiplicative.ofAdd (charge s firing)))

theorem spent_append (charge : (s : State) → Firing s → Nat)
    {s : State} (first : P.Run s) (second : P.Run first.last) :
    spent P charge (first.append second) = spent P charge first + spent P charge second := by
  simp [spent, Step.Run.account_append]

theorem spent_prefix_le (charge : (s : State) → Firing s → Nat)
    {s : State} (first : P.Run s) (second : P.Run first.last) :
    spent P charge first ≤ spent P charge (first.append second) := by
  rw [spent_append]
  omega

/-- Omitting a receipt does not erase the event's occurrence-store transition. -/
theorem plain_first_store {s : State} (firing : Firing s) (admitted : P.Admits firing) :
    P.present (plain P (.cons firing admitted (.nil _))) =
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire
        (P.present s) ((P.selection firing).commit (T := Unit)) := by
  exact P.present_result firing admitted

end Mettapedia.Languages.MeTTa.StoreAndDemand.RunReceipts
