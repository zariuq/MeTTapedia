import Mettapedia.CategoryTheory.WriterActionAdjunction
import Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational

/-!
# Writer interpretation of funded Cost schedules

The existing source-target indexed schedules retain funded operational waves.
Their occurrence receipts form an account monoid.  Empty execution is pure
return, and chronological composition is interpreted by the multiplication
of the concrete free-action writer monad.

This interpretation observes the occurrence bag and the terminal configuration.
The input still retains wave order and funding evidence.  It does not assert
that an unfunded wrapper simulates a base rewrite, or give the authored language
transformer a monad structure.
-/

open Mettapedia.Algebra
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

/-- Funded execution returns its terminal configuration together with its
complete occurrence receipt.  Source and target remain indices of the input. -/
def interpret {Ground : Type u} {source target : CostConfig Ground}
    (execution : OperationalSchedule Ground source target) :
    (writerMonad (Account Ground)).obj (CostConfig Ground) :=
  (Multiplicative.ofAdd execution.receipt, target)

/-- The unit law concerns empty computation at one configuration. -/
theorem interpret_nil {Ground : Type u} (config : CostConfig Ground) :
    interpret (OperationalSchedule.nil config) =
      (writerMonad (Account Ground)).η.app (CostConfig Ground) config := rfl

/-- The actual funded schedule composition is read by writer multiplication. -/
theorem interpret_append {Ground : Type u}
    {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    interpret (first.append second) =
      (writerMonad (Account Ground)).μ.app (CostConfig Ground)
        (Multiplicative.ofAdd first.receipt, interpret second) := by
  change (Multiplicative.ofAdd (first.append second).receipt, target) =
    (Multiplicative.ofAdd first.receipt * Multiplicative.ofAdd second.receipt, target)
  rw [OperationalSchedule.receipt_append]
  rfl

/-- The established exactly indexed schedule supplies precisely this account,
with its original occurrence count and wave count still retained in the input. -/
theorem interpret_ofIndexed {Ground : Type u}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    {eventCount waveCount : Nat}
    (schedule : ParallelCostSchedule source eventReceipt target eventCount waveCount) :
    interpret (OperationalSchedule.ofIndexed schedule) =
      (Multiplicative.ofAdd eventReceipt, target) := by
  unfold interpret
  rw [OperationalSchedule.receipt_ofIndexed]

/-- Every actual funded wave has the account supplied by its operational
receipt, regardless of how many concurrent occurrences it contains. -/
theorem interpret_oneWave {Ground : Type u}
    {source target : CostConfig Ground}
    {eventReceipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source eventReceipt target) :
    interpret (oneWave step) = (Multiplicative.ofAdd eventReceipt, target) := by
  simp [interpret, oneWave, OperationalSchedule.receipt]

#print axioms OperationalSchedule.receipt_append
#print axioms interpret_nil
#print axioms interpret_append
#print axioms interpret_ofIndexed
#print axioms interpret_oneWave

end Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter
