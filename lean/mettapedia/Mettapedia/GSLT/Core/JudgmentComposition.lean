import Mettapedia.GSLT.Core.ProofRelevantJudgment

/-!
# Sequential composition of evidence-dependent judgments

The first judgment returns an intermediate value and its evidence. The next
premise may depend on both. A two-phase operational presentation keeps that
evidence in the pending state instead of replacing it by successful support.

Complete finite routes of this presentation are equivalent to the composite
judgment's evidence, including both selected witnesses. This is a composition
contract for separately justified services, not an algorithm for deciding an
arbitrary premise or a native-runtime realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofRelevantJudgment

open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Ultrainfinite

universe u

variable {Input Middle Output : Type u}

/-- The remaining premise may inspect the exact first-stage evidence. -/
abbrev Continuation (first : Judgment Input Middle) (Output : Type u) :=
  (input : Input) -> (middle : Middle) ->
    first.Evidence input middle -> Output -> Type u

/-- Composition retains the intermediate value and both proof objects. -/
def Judgment.bind (first : Judgment Input Middle)
    (next : Continuation first Output) : Judgment Input Output where
  Evidence input output :=
    Sigma fun middle => Sigma fun evidence : first.Evidence input middle =>
      next input middle evidence output

/-- An exact service replacement remains exact under a dependent consumer
when that consumer transports along the selected evidence map. Endpoints
are fixed here; a cross-language endpoint translation needs its own laws. -/
def bindExactEquivalence {first replacement : Judgment Input Middle}
    (selected : ExactEquivalence first replacement)
    {next : Continuation first Output}
    {nextReplacement : Continuation replacement Output}
    (remaining : ∀ input middle (evidence : first.Evidence input middle) output,
      next input middle evidence output ≃
        nextReplacement input middle (selected.evidenceEquiv input middle evidence) output) :
    ExactEquivalence (first.bind next) (replacement.bind nextReplacement) where
  evidenceEquiv input output := Equiv.sigmaCongrRight fun middle =>
    Equiv.sigmaCongr (selected.evidenceEquiv input middle)
      (fun evidence => remaining input middle evidence output)

namespace Sequential

variable (first : Judgment Input Middle) (next : Continuation first Output)

/-- A pending query has retained the first witness but not discharged the
second premise. It is not an accepted answer. -/
inductive State (first : Judgment Input Middle)
    (next : Continuation first Output) where
  | query (input : Input)
  | pending (input : Input) (middle : Middle)
      (evidence : first.Evidence input middle)
  | answer (input : Input) (output : Output)

/-- The two independently specified stages of judgment execution. -/
inductive Step : State first next -> State first next -> Type u where
  | selected {input : Input} {middle : Middle}
      (evidence : first.Evidence input middle) :
      Step (.query input) (.pending input middle evidence)
  | discharged {input : Input} {middle : Middle}
      {evidence : first.Evidence input middle} {output : Output}
      (remaining : next input middle evidence output) :
      Step (.pending input middle evidence) (.answer input output)

/-- The semantic machine does not infer a missing second premise from a
successful first-stage selection. -/
def theory : GSLT where
  Term := State first next
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := Nonempty (Step first next source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def system : ProofRelevantGSLT where
  theory := theory first next
  steps := { Evidence := Step first next, erases_iff := fun _ _ => Iff.rfl }

/-- The same generic finite-route type used by other proof-relevant GSLTs. -/
abbrev Run (input : Input) (output : Output) :=
  Route (Step first next) (.query input) (.answer input output)

/-- Schedule the first witness before discharging its dependent premise. -/
def runOfEvidence {input : Input} {output : Output}
    (evidence : (first.bind next).Evidence input output) :
    Run first next input output :=
  .cons (.selected evidence.2.1)
    (.cons (.discharged evidence.2.2) (.refl _))

/-- Invert arbitrary complete routes, not only the routes built above. -/
def evidenceOfRun {input : Input} {output : Output}
    (run : Run first next input output) :
    (first.bind next).Evidence input output := by
  cases run with
  | cons selected tail =>
    cases selected with
    | selected evidence =>
      cases tail with
      | cons discharged tail =>
        cases discharged with
        | discharged remaining =>
          cases tail with
          | refl => exact ⟨_, evidence, remaining⟩
          | cons impossible _ => cases impossible

@[simp] theorem evidenceOfRun_runOfEvidence {input : Input} {output : Output}
    (evidence : (first.bind next).Evidence input output) :
    evidenceOfRun first next (runOfEvidence first next evidence) = evidence := by
  rcases evidence with ⟨middle, evidence, remaining⟩
  rfl

@[simp] theorem runOfEvidence_evidenceOfRun {input : Input} {output : Output}
    (run : Run first next input output) :
    runOfEvidence first next (evidenceOfRun first next run) = run := by
  cases run with
  | cons selected tail =>
    cases selected with
    | selected evidence =>
      cases tail with
      | cons discharged tail =>
        cases discharged with
        | discharged remaining =>
          cases tail with
          | refl => rfl
          | cons impossible _ => cases impossible

/-- Complete operational routes retain exactly the composite evidence. -/
def evidenceRunEquiv (input : Input) (output : Output) :
    (first.bind next).Evidence input output ≃ Run first next input output where
  toFun := runOfEvidence first next
  invFun := evidenceOfRun first next
  left_inv := evidenceOfRun_runOfEvidence first next
  right_inv := runOfEvidence_evidenceOfRun first next

/-- No hidden extra phase is present in any complete run. -/
theorem run_length {input : Input} {output : Output}
    (run : Run first next input output) : run.length = 2 := by
  rw [← runOfEvidence_evidenceOfRun first next run]
  rfl

/-- The derived run view uses the complete routes of the two-phase machine. -/
def runJudgment : Judgment Input Output where
  Evidence := Run first next

/-- This exact change of evidence presentation supplies the existing
proof-relevant translation and semantic cover APIs. -/
def exactRunView : ExactEquivalence (first.bind next) (runJudgment first next) where
  evidenceEquiv := evidenceRunEquiv first next

theorem accepted_iff_run (input : Input) (output : Output) :
    (first.bind next).theory.Step (.query input) (.answer input output) ↔
      Nonempty (Run first next input output) := by
  rw [Judgment.query_step_answer_iff]
  exact ⟨fun ⟨evidence⟩ => ⟨runOfEvidence first next evidence⟩,
    fun ⟨run⟩ => ⟨evidenceOfRun first next run⟩⟩

/-- If no selected witness can discharge the premise, selection alone
cannot produce a complete run. -/
theorem no_run_of_no_discharge {input : Input} {output : Output}
    (missing : ∀ middle (evidence : first.Evidence input middle),
      IsEmpty (next input middle evidence output)) :
    IsEmpty (Run first next input output) where
  false run := by
    rcases evidenceOfRun first next run with ⟨middle, evidence, remaining⟩
    exact (missing middle evidence).false remaining

end Sequential

/-! ## Evidence-dependent dispatch controls -/

namespace CompositionCanary

/-- Two distinct explanations for selecting the same intermediate value. -/
inductive Selection where
  | direct
  | fallback
deriving DecidableEq

def selection : Judgment Nat Nat where
  Evidence input middle := Selection × PLift (middle = input)

/-- Only direct selection licenses the increment. The fallback receipt is
not interchangeable with a direct receipt despite identical value endpoints. -/
def increment : Continuation selection Nat :=
  fun _ middle evidence output =>
    PLift (evidence.1 = .direct ∧ output = middle + 1)

def directRun (input : Nat) : Sequential.Run selection increment input (input + 1) :=
  Sequential.runOfEvidence selection increment
    ⟨input, ⟨.direct, ⟨rfl⟩⟩, ⟨rfl, rfl⟩⟩

theorem directRun_length (input : Nat) : (directRun input).length = 2 :=
  Sequential.run_length selection increment (directRun input)

/-- Any accepted output, including one from an arbitrary run, is the genuine
increment rather than merely some value with the right type. -/
theorem run_output (input output : Nat)
    (run : Sequential.Run selection increment input output) :
    output = input + 1 := by
  rcases Sequential.evidenceOfRun selection increment run with
    ⟨middle, ⟨selected, ⟨same⟩⟩, ⟨_, result⟩⟩
  exact result.trans (congrArg (fun n => n + 1) same)

theorem wrong_output_rejected (input : Nat) :
    IsEmpty (Sequential.Run selection increment input input) where
  false run := Nat.ne_add_one input (run_output input input run)

/-- Erasing which receipt was selected would lose this premise distinction. -/
theorem fallback_cannot_discharge (input output : Nat) :
    IsEmpty (increment input input ⟨.fallback, ⟨rfl⟩⟩ output) where
  false remaining := by
    have impossible := remaining.down.1
    cases impossible

/-! The existing nonidentity Bool/Option receipt equivalence also composes
with a consumer of the retained receipt, not only with its support. -/

def readBooleanReceipt : Continuation Canary.twoEvidence Bool :=
  fun _ _ evidence output => PLift (output = evidence)

def readOptionalReceipt : Continuation Canary.optionalEvidence Bool :=
  fun _ _ evidence output => PLift (output = evidence.isSome)

def receiptReplacement :
    ExactEquivalence (Canary.twoEvidence.bind readBooleanReceipt)
      (Canary.optionalEvidence.bind readOptionalReceipt) :=
  bindExactEquivalence Canary.exact (by
    intro input middle evidence output
    cases evidence <;> exact Equiv.refl _)

/-- The replacement really changes evidence representation while retaining
the Boolean result established by the dependent second premise. -/
theorem receiptReplacement_keeps_result :
    (receiptReplacement.evidenceEquiv () true
      ⟨(), true, ⟨rfl⟩⟩).2.1 = some () := rfl

end CompositionCanary

#print axioms bindExactEquivalence
#print axioms Sequential.evidenceRunEquiv
#print axioms Sequential.run_length
#print axioms Sequential.exactRunView
#print axioms Sequential.accepted_iff_run
#print axioms Sequential.no_run_of_no_discharge
#print axioms CompositionCanary.run_output
#print axioms CompositionCanary.wrong_output_rejected
#print axioms CompositionCanary.fallback_cannot_discharge
#print axioms CompositionCanary.receiptReplacement_keeps_result

end Mettapedia.GSLT.ProofRelevantJudgment
