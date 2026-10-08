import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-!
# The observation boundary of unlabelled rho reduction

Two terminal processes are strongly bisimilar when the only observation is
the unlabelled reduction relation. An input and zero supply such a pair,
but a matching output in parallel distinguishes them. The proof uses the
actual COMM receipt, including its semantic substitution, and irreducibility
modulo the full structural congruence.

This is the established COMM-only rho profile. It does not add the separate
book Drop rule or identify reduction bisimilarity with a barbed or labelled
interface equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionObservationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Reduction

/-- Every actual COMM derivation requires at least an input and an output,
even when structural equivalences surround the supplied derivation. -/
theorem ioCount_at_least_two {source target : Pattern} (step : Reduces source target) :
    2 ≤ ioCount source := by
  induction step with
  | comm =>
      simp only [ioCount, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil]
      omega
  | @equiv source source' target target' before _ _ ih =>
      rw [ioCount_SC before]
      exact ih
  | par _ ih =>
      simp only [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp only [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

/-- Small complete syntax inventories rule out every structurally equivalent
COMM source, rather than merely failing one syntactic redex matcher. -/
theorem normalForm_of_ioCount_lt_two {process : Pattern} (small : ioCount process < 2) :
    NormalForm process := by
  rintro ⟨target, ⟨step⟩⟩
  have required := ioCount_at_least_two step
  omega

/-- The same inventory excludes a step of the actual authored, canonically
quotiented rho GSLT. This uses its earned soundness map to core receipts. -/
theorem no_declared_step_of_ioCount_lt_two
    {source : LanguageDefGSLT.RhoProcess} (small : ioCount source.1 < 2)
    (target : LanguageDefGSLT.RhoProcess) :
    ¬ LanguageDefGSLT.rhoLanguageDefGSLT.Step source target := by
  intro step
  exact normalForm_of_ioCount_lt_two small
    ⟨target.1, LanguageDefGSLT.rhoLanguageDefGSLT_step_sound step⟩

/-- Strong bisimulation for exactly the unlabelled, receipt-erased reduction
observation. The two transfer clauses retain actual endpoint choices. -/
def IsReductionBisimulation (relation : Pattern → Pattern → Prop) : Prop :=
  ∀ {first second}, relation first second →
    (∀ {next}, Nonempty (Reduces first next) →
      ∃ other, Nonempty (Reduces second other) ∧ relation next other) ∧
    (∀ {next}, Nonempty (Reduces second next) →
      ∃ other, Nonempty (Reduces first other) ∧ relation other next)

def ReductionBisimilar (first second : Pattern) : Prop :=
  ∃ relation, IsReductionBisimulation relation ∧ relation first second

/-- All terminal processes have the same unlabelled reduction behavior. -/
theorem terminal_bisimilar {first second : Pattern}
    (firstTerminal : NormalForm first) (secondTerminal : NormalForm second) :
    ReductionBisimilar first second := by
  refine ⟨fun p q => NormalForm p ∧ NormalForm q, ?_, firstTerminal, secondTerminal⟩
  intro p q terminals
  constructor
  · intro next step
    exact False.elim (terminals.1 ⟨next, step⟩)
  · intro next step
    exact False.elim (terminals.2 ⟨next, step⟩)

/-- This observation does preserve existence of an immediate reduction. -/
theorem bisimilar_canStep {first second : Pattern}
    (same : ReductionBisimilar first second) : CanStep first ↔ CanStep second := by
  obtain ⟨relation, transfer, related⟩ := same
  constructor
  · rintro ⟨next, step⟩
    obtain ⟨other, nextStep, _⟩ := (transfer related).1 step
    exact ⟨other, nextStep⟩
  · rintro ⟨next, step⟩
    obtain ⟨other, nextStep, _⟩ := (transfer related).2 step
    exact ⟨other, nextStep⟩

def zero : Pattern := .apply "PZero" []
def channel : Pattern := .apply "NQuote" [zero]
def waitingInput : Pattern := .apply "PInput" [channel, .lambda none zero]
def matchingOutput : Pattern := .apply "POutput" [channel, zero]
def withOutput (process : Pattern) : Pattern :=
  .collection .hashBag [matchingOutput, process] none

/-- The displayed processes have no loose object-language indices. -/
theorem examples_closed :
    zero.isWellScopedAt 0 = true ∧ waitingInput.isWellScopedAt 0 = true ∧
      matchingOutput.isWellScopedAt 0 = true := by
  decide

theorem zero_terminal : NormalForm zero :=
  normalForm_of_ioCount_lt_two (by simp [zero, ioCount])

theorem waitingInput_terminal : NormalForm waitingInput :=
  normalForm_of_ioCount_lt_two (by simp [waitingInput, channel, zero, ioCount])

theorem outputWithZero_terminal : NormalForm (withOutput zero) :=
  normalForm_of_ioCount_lt_two (by simp [withOutput, matchingOutput, channel, zero, ioCount])

theorem zero_waitingInput_bisimilar : ReductionBisimilar zero waitingInput :=
  terminal_bisimilar zero_terminal waitingInput_terminal

/-- The positive control is a complete supplied receipt of the actual core
COMM rule, with the actual semantic contractum. -/
def inputWithOutput_step :
    Reduces (withOutput waitingInput)
      (.collection .hashBag [semanticCommSubst zero zero] none) := by
  simpa only [withOutput, waitingInput, matchingOutput, List.append_nil] using
    (@Reduces.comm channel zero zero [])

theorem inputWithOutput_canStep : CanStep (withOutput waitingInput) :=
  ⟨_, ⟨inputWithOutput_step⟩⟩

/-- Adding the same matching output breaks the previously proved strong
reduction bisimilarity. This is a concrete failure of parallel congruence. -/
theorem parallel_distinguishes :
    ¬ ReductionBisimilar (withOutput zero) (withOutput waitingInput) := by
  intro same
  exact outputWithZero_terminal ((bisimilar_canStep same).mpr inputWithOutput_canStep)

theorem reduction_bisimilarity_not_parallel_congruence :
    ¬ ∀ first second, ReductionBisimilar first second →
      ReductionBisimilar (withOutput first) (withOutput second) := by
  intro congruence
  exact parallel_distinguishes (congruence zero waitingInput zero_waitingInput_bisimilar)

/-- The independent immediate-step observation separates the two supplied
parallel processes, even though both unextended processes are terminal. -/
theorem declared_context_observation :
    ¬ CanStep (withOutput zero) ∧ CanStep (withOutput waitingInput) :=
  ⟨outputWithZero_terminal, inputWithOutput_canStep⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionObservationBoundary
