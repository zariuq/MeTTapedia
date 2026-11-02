import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationWordBridge
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Source-derived additive word workers in an observation-qualified portfolio

Classification consumes the actual source Atom expressions and the existing
PeTTa elaborator. The resulting region executes the independent UInt64 worker,
with changed-program and overflow refusal. The fallback uses the current IR
program and registers, never the saved source body. The selected single-step
result is connected to the original PeTTa `PureReturns` judgment.

This covers the existing additive source fragment and value-observed IR batch.
It does not extend extraction to arbitrary fold bodies or identify IR steps
with source evaluator budgets. Those remain separate parts of the compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationPortfolio

open Mettapedia.GSLT.Dynamics.ObservationQualified
open Mettapedia.GSLT.Dynamics.RegionObservations
open Mettapedia.GSLT.Dynamics.PartialRegionPlan
open Mettapedia.Machines.AdditiveFoldInference
open Mettapedia.Machines.InferredWordFold
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open AggregationSource MeTTaIL.WireKit Eval

abbrev Input (n : Nat) := World n × List Nat

def registerQuestions (n : Nat) : Family (Registers n) where
  Question := Fin n
  Answer _ := Nat
  read coordinate registers := registers coordinate

def boundary (n : Nat) : Boundary (Input n) (Registers n) (Registers n) where
  source input := sourceRun input.1.program input.2 input.1.registers
  summarize := id
  future := registerQuestions n
  sufficient _ _ same coordinate := congrFun same coordinate

def wordRegion {n : Nat} {saved : Program n} (certificate : Certificate saved) :
    CertifiedRegion (boundary n) Nat where
  regime := 0
  Artifact := Registers n
  attempt input := match cachedValues certificate input.1 input.2 with
    | none => .declined input
    | some values => .committed values
  decode := id
  restores input restored declined := by
    cases result : cachedValues certificate input.1 input.2 with
    | none => simpa [result] using declined.symm
    | some values => simp [result] at declined
  exact input values committed := by
    cases result : cachedValues certificate input.1 input.2 with
    | none => simp [result] at committed
    | some answer =>
        have same : answer = values := by simpa [result] using committed
        subst values
        exact cachedValues_correct certificate input.1 input.2 answer result

def sourceCandidate {n : Nat} {environment : Environment n} {source : Fin n → Atom}
    (certificate : SourceCertificate environment source) (estimate : Input n → Estimate)
    (ordinal : Nat) : Candidate (boundary n) Nat :=
  ⟨wordRegion certificate.additive, estimate, ordinal⟩

/-- Proof-producing source recognition, rather than a name-based shortcut.
Unsupported source syntax produces no candidate and ordinary execution stays
available. The estimate supplies no part of the source derivation. -/
def classify {n : Nat} (environment : Environment n) (source : Fin n → Atom)
    (estimate : Input n → Estimate) (ordinal : Nat) : Option (Candidate (boundary n) Nat) :=
  (inferSource environment source).map fun certificate => sourceCandidate certificate estimate ordinal

theorem classify_none_of_unsupported {n : Nat} (environment : Environment n)
    (source : Fin n → Atom) (estimate : Input n → Estimate) (ordinal : Nat)
    (unsupported : inferSource environment source = none) :
    classify environment source estimate ordinal = none := by simp [classify, unsupported]

theorem changed_program_declines {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (input : Input n) (changed : input.1.program ≠ saved) :
    (wordRegion certificate).attempt input = .declined input := by
  simp [wordRegion, changed_declaration_declines certificate input.1 input.2 changed]

theorem portfolio_uses_current_program {n : Nat} (input : Input n)
    (candidates : List (Candidate (boundary n) Nat)) :
    RegionPortfolio.execute input candidates = sourceRun input.1.program input.2 input.1.registers :=
  RegionPortfolio.execute_exact input candidates

/-- This is an operational source theorem for one extracted coordinate.
The source judgment is independent of both portfolio selection and the word
implementation; it preserves the PeTTa store and one answer occurrence. -/
theorem selected_coordinate_returns {n : Nat} {environment : Environment n}
    {source : Fin n → Atom} (certificate : SourceCertificate environment source)
    (program : SpaceSemantics.Program) (caller : Subst) (state : Effects.State)
    (registers : Registers n) (input : Nat)
    (captured : Captured environment caller registers input)
    (candidates : List (Candidate (boundary n) Nat)) (coordinate : Fin n) :
    PureReturns program caller state (source coordinate) state
      (number ((RegionPortfolio.execute (⟨certificate.program, registers⟩, [input]) candidates) coordinate)) := by
  rw [portfolio_uses_current_program]
  exact (certificate.elaborated coordinate).returns program caller state registers input captured

namespace Controls

def certificate := AggregationWordBridge.Controls.certificate

def candidate : Candidate (boundary 1) Nat := sourceCandidate certificate (fun _ => ⟨1, 16⟩) 0

theorem inferred_source_is_in_the_portfolio :
    (classify AggregationSource.Controls.environment AggregationSource.Controls.counter
      (fun _ => ⟨1, 16⟩) 0).isSome = true := by decide

theorem changed_spelling_still_classifies :
    (classify AggregationSource.Controls.environment AggregationSource.Controls.reassociated
      (fun _ => ⟨1, 16⟩) 0).isSome = true := by decide

theorem selected_source_returns_six (program : SpaceSemantics.Program) (state : Effects.State) :
    PureReturns program AggregationWordBridge.Controls.caller state
      (AggregationSource.Controls.counter 0) state (number 6) := by
  have source := selected_coordinate_returns certificate program
    AggregationWordBridge.Controls.caller state (fun _ => 5) 7
    AggregationWordBridge.Controls.capture_valid [candidate] 0
  exact source

theorem overflow_fallback_does_not_wrap :
    (RegionPortfolio.execute
      (⟨Mettapedia.Machines.InferredWordFold.Controls.counter, fun _ => UInt64.size - 1⟩, [9])
      [⟨wordRegion Mettapedia.Machines.InferredWordFold.Controls.proof, fun _ => ⟨0, 0⟩, 0⟩]) 0
      = UInt64.size := by
  rw [portfolio_uses_current_program]
  decide

end Controls

#print axioms wordRegion
#print axioms selected_coordinate_returns
#print axioms Controls.selected_source_returns_six
#print axioms Controls.overflow_fallback_does_not_wrap

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationPortfolio
