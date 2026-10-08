import Mettapedia.CategoryTheory.RunAccount
import Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational

/-!
# Writer interpretation of funded Cost schedules

The existing source-target indexed schedules retain funded operational waves.
Configurations with schedules as runs form a category, and the occurrence
receipt is an account of its runs.  Empty execution is pure return, and
chronological composition is interpreted by the multiplication of the concrete
free-action writer monad: both are the general laws of reading an account.

This interpretation observes the occurrence bag and the terminal configuration.
The input still retains wave order and funding evidence.  It does not assert
that an unfunded wrapper simulates a base rewrite, or give the authored language
transformer a monad structure.
-/

open _root_.CategoryTheory
open Mettapedia.Algebra
open Mettapedia.Effects
open Mettapedia.CategoryTheory.WriterActionAdjunction
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

set_option autoImplicit false

universe u

namespace Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule

/-- Chronological composition adds the complete receipts, preserving the
multiplicity of every occurrence label. -/
theorem receipt_append {Ground : Type u}
    {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    (first.append second).receipt = first.receipt + second.receipt := by
  induction first with
  | refl =>
      simp [OperationalSchedule.append, OperationalSchedule.receipt]
  | cons step rest inductionHypothesis =>
      rcases step with ⟨headReceipt, head⟩
      simp only [OperationalSchedule.append, Route.append, OperationalSchedule.receipt]
      have tailLaw := inductionHypothesis second
      change OperationalSchedule.receipt (Route.append rest second) =
        OperationalSchedule.receipt rest + second.receipt at tailLaw
      rw [tailLaw]
      exact (add_assoc _ _ _).symm

end Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule

namespace Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter

/-- Accounts retain every occurrence label, including repeated labels. -/
abbrev Account (Ground : Type u) :=
  Multiplicative (Multiset (SpendEvent Ground (CostName Ground)))

/-- Configurations, with funded schedules as the runs between them. -/
def ScheduleState (Ground : Type u) : Type u := CostConfig Ground

instance scheduleStateCategory (Ground : Type u) : Category (ScheduleState Ground) where
  Hom source target := OperationalSchedule Ground source target
  id config := OperationalSchedule.nil config
  comp first second := first.append second
  id_comp schedule := Route.refl_append schedule
  comp_id schedule := Route.append_refl schedule
  assoc first second third := Route.append_assoc first second third

/-- The occurrence receipt is an account of schedules. -/
def receiptAccount (Ground : Type u) : RunAccount (ScheduleState Ground) (Account Ground) where
  of schedule := Multiplicative.ofAdd (OperationalSchedule.receipt schedule)
  of_id _ := rfl
  of_comp first second :=
    congrArg Multiplicative.ofAdd (OperationalSchedule.receipt_append first second)

/-- Funded execution returns its terminal configuration together with its
complete occurrence receipt.  Source and target remain indices of the input. -/
def interpret {Ground : Type u} {source target : CostConfig Ground}
    (execution : OperationalSchedule Ground source target) :
    (writerMonad (Account Ground)).obj (CostConfig Ground) :=
  (receiptAccount Ground).read
    (⟨execution, target⟩ : Execution (ScheduleState Ground) source target (CostConfig Ground))

/-- The unit law concerns empty computation at one configuration. -/
theorem interpret_nil {Ground : Type u} (config : CostConfig Ground) :
    interpret (OperationalSchedule.nil config) =
      (writerMonad (Account Ground)).η.app (CostConfig Ground) config :=
  (receiptAccount Ground).read_pure (C := ScheduleState Ground) config config

/-- The actual funded schedule composition is read by writer multiplication. -/
theorem interpret_append {Ground : Type u}
    {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    interpret (first.append second) =
      (writerMonad (Account Ground)).μ.app (CostConfig Ground)
        (Multiplicative.ofAdd first.receipt, interpret second) :=
  (receiptAccount Ground).read_bind
    (⟨first, middle⟩ : Execution (ScheduleState Ground) source middle (CostConfig Ground))
    (fun _ => (⟨second, target⟩ :
      Execution (ScheduleState Ground) middle target (CostConfig Ground)))

/-- The established exactly indexed schedule supplies precisely this account,
with its original occurrence count and wave count still retained in the input. -/
theorem interpret_ofIndexed {Ground : Type u}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    {eventCount waveCount : Nat}
    (schedule : ParallelCostSchedule source eventReceipt target eventCount waveCount) :
    interpret (OperationalSchedule.ofIndexed schedule) =
      (Multiplicative.ofAdd eventReceipt, target) := by
  change (Multiplicative.ofAdd
      (OperationalSchedule.receipt (OperationalSchedule.ofIndexed schedule)), target) = _
  rw [OperationalSchedule.receipt_ofIndexed]

/-- Every actual funded wave has the account supplied by its operational
receipt, regardless of how many concurrent occurrences it contains. -/
theorem interpret_oneWave {Ground : Type u}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source eventReceipt target) :
    interpret (oneWave step) = (Multiplicative.ofAdd eventReceipt, target) := by
  change (Multiplicative.ofAdd (OperationalSchedule.receipt (oneWave step)), target) = _
  simp [oneWave, OperationalSchedule.receipt]

end Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter
