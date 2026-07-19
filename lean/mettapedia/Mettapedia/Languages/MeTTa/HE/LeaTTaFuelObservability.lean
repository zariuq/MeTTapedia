import Mettapedia.Languages.MeTTa.HE.HumanEvalOutcome
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.Substitution

/-!
# LeaTTa fuel-observability counterexample

The minimal LeaTTa evaluator exposes fuel exhaustion as a language-level
`StackOverflow` atom.  Even the inert symbol `a` produces that atom at fuel
zero but evaluates normally at fuel one.  The fuel-free human evaluator has no
corresponding derivation from `a`, so unrestricted arbitrary-fuel soundness is
false for the current executable.

This module is a counterexample and permanent canary only.  It makes no change
to the executable and assumes no proposed repair.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaFuelObservability

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanEvalSpec
open HumanEvalOutcome
open HumanTypeSpec

private def q4LeaEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [] []

private def q4LeaStackOverflow : Metta.Atom :=
  .expr [.sym "Error", .sym "a", .sym "StackOverflow"]

private def q4HEStackOverflow : Atom :=
  .expression [.symbol "Error", .symbol "a", .symbol "StackOverflow"]

private def q4NoHost : HumanGroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

/-- At fuel zero, an inert symbol becomes a visible `StackOverflow` result. -/
theorem fuelZero_symbol_stackOverflow :
    (Metta.Minimal.mettaEval q4LeaEnv 0 Metta.Minimal.St.init []
      (.sym "a")).1 = [(q4LeaStackOverflow, [])] := by
  simp [q4LeaEnv, q4LeaStackOverflow, Metta.Minimal.mettaEval,
    Metta.instantiate_nil]

/-- One unit of fuel is already enough for the same inert symbol to remain
unchanged. -/
theorem fuelOne_symbol_normal :
    (Metta.Minimal.mettaEval q4LeaEnv 1 Metta.Minimal.St.init []
      (.sym "a")).1 = [(.sym "a", [])] := by
  have hNotEmpty :
      (Metta.Atom.sym "NotReducible" != Metta.Atom.sym "Empty") = true := rfl
  have hNotReducible :
      (Metta.Atom.sym "NotReducible" ==
        Metta.Atom.sym "NotReducible") = true := rfl
  simp [q4LeaEnv, Metta.Minimal.mettaEval, Metta.instantiate_nil,
    Metta.Minimal.interpretFuel, Metta.Minimal.interpretStack1,
    Metta.Minimal.atomToStack, Metta.Minimal.evalOp, Metta.Minimal.queryOp,
    Metta.Minimal.candidatesW, Metta.Minimal.MinEnv.candidates,
    Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules,
    Metta.Minimal.isFinal, Metta.Minimal.finalPair,
    Metta.Minimal.notReducibleA, Metta.Minimal.emptyA, Metta.Minimal.finItem,
    Metta.Minimal.isVariableHeaded, Metta.Minimal.isEmbeddedOp,
    Metta.Minimal.headKey, Metta.Minimal.World.empty, Metta.Minimal.St.init,
    Metta.Minimal.varsCopy, Metta.Minimal.returnsAtom,
    hNotEmpty, hNotReducible]

/-- Fuel is observable even on an inert closed symbol. -/
theorem symbol_results_depend_on_fuel :
    (Metta.Minimal.mettaEval q4LeaEnv 0 Metta.Minimal.St.init []
      (.sym "a")).1 ≠
    (Metta.Minimal.mettaEval q4LeaEnv 1 Metta.Minimal.St.init []
      (.sym "a")).1 := by
  rw [fuelZero_symbol_stackOverflow, fuelOne_symbol_normal]
  simp [q4LeaStackOverflow]

/-- The fuel-zero executable run lands in the resource-exhaustion lane. -/
theorem fuelZero_symbol_classified_resourceExhausted :
    (Metta.Minimal.mettaEval q4LeaEnv 0 Metta.Minimal.St.init []
      (.sym "a")).1.map classifyLeaTTaResult =
        [.resourceExhausted (.sym "a") []] := by
  rw [fuelZero_symbol_stackOverflow]
  rfl

/-- The fuel-one executable run lands in the semantic-result lane. -/
theorem fuelOne_symbol_classified_semantic :
    (Metta.Minimal.mettaEval q4LeaEnv 1 Metta.Minimal.St.init []
      (.sym "a")).1.map classifyLeaTTaResult =
        [.semantic (.sym "a", [])] := by
  rw [fuelOne_symbol_normal]
  rfl

private theorem stackOverflow_not_typeCast :
    ¬TypeCastRel Space.empty (.symbol "a") Atom.undefinedType Bindings.empty
      (q4HEStackOverflow, Bindings.empty) := by
  intro h
  cases h

/-- The fuel-zero result is not merely another permitted human outcome: the
fuel-free evaluator has no derivation from the inert symbol to `StackOverflow`.
-/
theorem fuelZero_symbol_not_humanEval :
    ¬HumanEval Space.empty q4NoHost []
      (.symbol "a") Atom.undefinedType Bindings.empty
      (q4HEStackOverflow, Bindings.empty) := by
  rintro ⟨hraw, _⟩
  cases hraw <;>
    simp_all [q4HEStackOverflow, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  apply stackOverflow_not_typeCast
  assumption

end Mettapedia.Languages.MeTTa.HE.LeaTTaFuelObservability
