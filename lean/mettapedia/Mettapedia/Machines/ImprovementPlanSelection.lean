import Mettapedia.Machines.ImprovementSourceProgram

/-!
# Choosing between source improvement and atomic upsert

Both plans execute the primitive programs already related by the source bridge.
This module gives their exact costs in an explicit primitive-price model, then
chooses the cheaper plan after accounting for target setup. Admission inspection
is paid by both choices and is not silently discarded.

The result is optimal among these two modeled plans, not among all programs.
Measured native prices and conversion costs must justify an implementation's
instantiation. Source semantic debit is a different observation from this cost.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement.PlanSelection

open Cursor.PrimitiveProgram Information SourceProgram

structure Prices where
  read : Nat
  erase : Nat
  put : Nat
  upsert : Nat
  setup : Nat
  inspection : Nat
  deriving DecidableEq

def physicalCharge {Key : Type} (prices : Prices) (_store : Store Key Nat) : Op → Nat
  | .read => prices.read
  | .erase _ => prices.erase
  | .put _ => prices.put
  | .upsert _ => prices.upsert

def sourceWork (prices : Prices) : SourcePlan → Nat
  | .keep => prices.read
  | .insertMissing => prices.read + prices.put
  | .replaceExisting => prices.read + prices.erase + prices.put

variable {Key : Type} [DecidableEq Key]

theorem source_physical (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat) :
    direct (step key) (physicalCharge prices) 4 (.ok (source key candidate)) store =
      (sourceWork prices (sourcePlan candidate (store key)),
        (.inl (.ok (answers key (improve store key candidate).2)), (improve store key candidate).1)) := by
  cases old : store key with
  | none => simp [direct, source, step, physicalCharge, sourceWork, sourcePlan, improve, old, answers]
  | some previous =>
    by_cases better : candidate < previous <;>
      simp [direct, source, step, physicalCharge, sourceWork, sourcePlan, improve,
        old, better, answers, Nat.add_assoc]

theorem native_physical (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat) :
    direct (step key) (physicalCharge prices) 2 (.ok (native key candidate)) store =
      (prices.upsert,
        (.inl (.ok (answers key (improve store key candidate).2)), (improve store key candidate).1)) := by
  simp [direct, native, step, physicalCharge, answers]

def selectNative (prices : Prices) (plan : SourcePlan) : Bool :=
  decide (prices.setup + prices.upsert ≤ sourceWork prices plan)

def selected (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat) :=
  if selectNative prices (sourcePlan candidate (store key)) then
    let result := direct (step key) (physicalCharge prices) 2 (.ok (native key candidate)) store
    (prices.inspection + prices.setup + result.1, result.2)
  else
    let result := direct (step key) (physicalCharge prices) 4 (.ok (source key candidate)) store
    (prices.inspection + result.1, result.2)

theorem selected_exact (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat) :
    selected prices store key candidate =
      (prices.inspection + min (sourceWork prices (sourcePlan candidate (store key)))
        (prices.setup + prices.upsert),
        (.inl (.ok (answers key (improve store key candidate).2)), (improve store key candidate).1)) := by
  unfold selected selectNative
  by_cases cheaper : prices.setup + prices.upsert ≤ sourceWork prices (sourcePlan candidate (store key))
  · simp [cheaper, native_physical, Nat.add_assoc]
  · simp [cheaper, source_physical, min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge cheaper))]

theorem selection_preserves_returns (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat) :
    (selected prices store key candidate).2 =
      (.inl (.ok (answers key (improve store key candidate).2)), (improve store key candidate).1) := by
  rw [selected_exact]

theorem cost_le_source_plus_inspection (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat) :
    (selected prices store key candidate).1 ≤
      prices.inspection + sourceWork prices (sourcePlan candidate (store key)) := by
  rw [selected_exact]
  exact Nat.add_le_add_left (min_le_left _ _) _

theorem cost_le_native_plus_inspection (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat) :
    (selected prices store key candidate).1 ≤ prices.inspection + prices.setup + prices.upsert := by
  rw [selected_exact, Nat.add_assoc]
  exact Nat.add_le_add_left (min_le_right _ _) _

/-- A strict total-cost saving requires paying for inspection too. -/
theorem profitable_native_is_selected (prices : Prices) (store : Store Key Nat) (key : Key) (candidate : Nat)
    (profitable : prices.inspection + prices.setup + prices.upsert <
      sourceWork prices (sourcePlan candidate (store key))) :
    selectNative prices (sourcePlan candidate (store key)) = true ∧
    (selected prices store key candidate).1 < sourceWork prices (sourcePlan candidate (store key)) := by
  have cheaper : prices.setup + prices.upsert ≤ sourceWork prices (sourcePlan candidate (store key)) := by omega
  constructor
  · simp [selectNative, cheaper]
  · rw [selected_exact]
    simp only [min_eq_right cheaper]
    omega

namespace Controls

theorem profitable_replacement :
    (selected ⟨8, 5, 7, 2, 1, 1⟩ (fun _ : Unit => some 10) () 7).1 = 4 := by decide

theorem setup_can_defeat_native :
    selectNative ⟨1, 1, 1, 1, 100, 1⟩ .replaceExisting = false := by decide

theorem inspection_is_real_overhead :
    (selected ⟨1, 1, 1, 1, 100, 1⟩ (fun _ : Unit => some 10) () 7).1 = 4 ∧
    sourceWork ⟨1, 1, 1, 1, 100, 1⟩ .replaceExisting = 3 := by decide

end Controls
end Mettapedia.Machines.KeyedImprovement.PlanSelection
