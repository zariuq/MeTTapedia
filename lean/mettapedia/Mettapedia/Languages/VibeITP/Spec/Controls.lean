import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mettapedia.Languages.VibeITP.Spec.Encode

/-!
# Vibe-ITP specification: positive and negative controls

Small certificates, printed with `encodeFile`, with their verdicts decided by
kernel evaluation of `checkRun`.  Symbol slots 13 and above are user slots;
term, theorem, and challenge slots start empty.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.Controls

open Mettapedia.Languages.VibeITP.Spec

private def run (setup proofs : List (List Instr)) : Verdict :=
  checkRun (setup.map encodeFile) (proofs.map encodeFile)

/-! ## Positive controls -/

/-- Setup declares a propositional variable `A`, the axiom `A → A`, and the
same statement as a challenge; the proof phase satisfies it directly. -/
private def axiomSetup : List Instr :=
  [.fvarNew 0 13, .termNewApp 13 [] 1, .termNewApp 2 [1, 1] 2,
   .addAxiom 2 1, .challengeAdd 2 0]

theorem axiom_satisfies_challenge :
    run [axiomSetup] [[.challengeSatisfy 0 1]] = .proofs 1 0 0 := by decide +kernel

theorem axiom_run_succeeds :
    (run [axiomSetup] [[.challengeSatisfy 0 1]]).success = true := by decide +kernel

/-- Modus ponens from the axioms `A → B` and `A`. -/
private def mpSetup : List Instr :=
  [.fvarNew 0 13, .fvarNew 0 14, .termNewApp 13 [] 1, .termNewApp 14 [] 2,
   .termNewApp 2 [1, 2] 3, .addAxiom 3 1, .addAxiom 1 2, .challengeAdd 2 0]

theorem modus_ponens_proves_challenge :
    run [mpSetup] [[.modusPonens 1 2 3, .challengeSatisfy 0 3]] =
      .proofs 1 0 0 := by decide +kernel

/-- Second-order instantiation: from the axiom `P(a)` with `P` unary,
instantiate `P` by the one-parameter value `x ↦ x → x`, giving `a → a`. -/
private def instSetup : List Instr :=
  [.fvarNew 1 13, .fvarNew 0 14, .termNewApp 14 [] 1, .termNewApp 13 [1] 2,
   .addAxiom 2 1, .termNewBVar 0 3, .termNewApp 2 [3, 3] 4,
   .termNewApp 2 [1, 1] 5, .challengeAdd 5 0]

theorem instantiation_plugs_argument :
    run [instSetup] [[.thmInstantiate 1 13 4 2, .challengeSatisfy 0 2]] =
      .proofs 1 0 0 := by decide +kernel

/-- Instantiation under a binder shifts the plugged argument.  With a
declared constant `ex` binding one variable, from the axiom `ex(x : P(x))`,
instantiating the unary `P` by `y ↦ ex(z : y)` yields `ex(x : ex(z : x))`:
the argument `x` is bound variable 0 at the occurrence and variable 1 under
the value's own binder. -/
private def binderSetup : List Instr :=
  [.constNew [1] 15, .fvarNew 1 13, .termNewBVar 0 1, .termNewApp 13 [1] 2,
   .termNewApp 15 [2] 3, .addAxiom 3 1, .termNewBVar 1 4, .termNewApp 15 [4] 5,
   .termNewApp 15 [5] 6, .challengeAdd 6 0]

theorem instantiation_under_binder :
    run [binderSetup] [[.thmInstantiate 1 13 5 2, .challengeSatisfy 0 2]] =
      .proofs 1 0 0 := by decide +kernel

/-- Wrapping addition: `litAdd(2^64 - 1, 1) = 0`. -/
private def maxWord : Nat := wordBound - 1

private def addSetup : List Instr :=
  [.termNewLiteral (natLiteral maxWord) 1, .termNewLiteral (natLiteral 1) 2,
   .termNewApp 6 [1, 2] 3, .termNewLiteral (natLiteral 0) 4,
   .termNewApp 3 [3, 4] 5, .challengeAdd 5 0]

theorem literal_addition_wraps :
    run [addSetup] [[.litAdd maxWord 1 1, .challengeSatisfy 0 1]] =
      .proofs 1 0 0 := by decide +kernel

/-- A definition by a closed body, used to satisfy its own defining equation
registered as a challenge: `c(x : P(x)) = P(0)`. -/
private def defSetup : List Instr :=
  [.fvarNew 1 13, .termNewLiteral (natLiteral 0) 1, .termNewApp 13 [1] 2,
   .defineConst [13] [0] 2 14 1,
   .termNewBVar 0 3, .termNewApp 13 [3] 4, .termNewApp 14 [4] 5,
   .termNewApp 3 [5, 2] 6, .challengeAdd 6 0]

theorem definition_equation_satisfies :
    run [defSetup] [[.challengeSatisfy 0 1]] = .proofs 1 0 0 := by decide +kernel

/-- Without a proof phase the run stops after setup with its open challenges. -/
theorem setup_only_run : run [axiomSetup] [] = .setupOnly 1 := by decide +kernel

/-- An empty proof phase leaves the challenge open: no error, no success. -/
theorem open_challenge_is_not_success :
    run [axiomSetup] [[]] = .proofs 1 0 1 ∧
      (run [axiomSetup] [[]]).success = false := by decide +kernel

/-- A proof-phase registration is accepted and counted separately. -/
theorem proof_phase_registration :
    run [axiomSetup] [[.challengeAdd 2 1, .challengeSatisfy 0 1,
      .challengeSatisfy 1 1]] = .proofs 1 1 0 := by decide +kernel

/-- Swaps accept empty slots; a builtin moved out of the protected range can
be freed. -/
theorem swap_then_free_builtin :
    run [[.symbolSwap 2 20, .symbolFree 20]] [] = .setupOnly 0 := by decide +kernel

/-! ## Negative controls -/

theorem truncated_word_is_malformed :
    checkRun [[0, 255]] [] = .malformed 0 .truncatedInteger := by decide +kernel

theorem truncated_literal_is_malformed :
    checkRun [[5, 3, 1]] [] = .malformed 0 .truncatedBytes := by decide +kernel

theorem unknown_opcode_is_malformed :
    checkRun [[26]] [] = .malformed 0 (.unknownOpcode 26) := by decide +kernel

/-- A malformed later file is reported before any error of an earlier file. -/
theorem malformed_precedes_semantic_errors :
    checkRun [encodeFile [.symbolFree 3]] [[26]] = .malformed 1 (.unknownOpcode 26) := by
  decide +kernel

theorem protected_symbol_cannot_be_freed :
    run [[.symbolFree 5]] [] = .rejected 0 0 .protectedSymbol := by decide +kernel

theorem protected_slot_even_when_empty :
    run [[.symbolSwap 5 20, .symbolFree 5]] [] = .rejected 0 1 .protectedSymbol := by decide +kernel

theorem freeing_empty_slot :
    run [[.symbolFree 20]] [] = .rejected 0 0 (.alreadyEmpty .symbol) := by decide +kernel

theorem occupied_destination :
    run [[.fvarNew 0 13, .fvarNew 0 13]] [] = .rejected 0 1 (.occupied .symbol) := by decide +kernel

theorem missing_symbol :
    run [[.termNewApp 13 [] 1]] [] = .rejected 0 0 (.missing .symbol) := by decide +kernel

theorem marker_not_applicable :
    run [[.termNewApp 0 [] 1]] [] = .rejected 0 0 .notApplicable := by decide +kernel

theorem arity_mismatch :
    run [[.fvarNew 1 13, .termNewApp 13 [] 1]] [] = .rejected 0 1 .arityMismatch := by decide +kernel

theorem axiom_in_proof_phase :
    run [axiomSetup] [[.addAxiom 2 2]] = .rejected 1 0 .axiomInProofs := by decide +kernel

theorem modus_ponens_in_setup :
    run [mpSetup ++ [.modusPonens 1 2 3]] [] =
      .rejected 0 8 (.inferenceInSetup .modusPonens) := by decide +kernel

theorem satisfy_in_setup :
    run [axiomSetup ++ [.challengeSatisfy 0 1]] [] = .rejected 0 5 .satisfyInSetup := by decide +kernel

theorem modus_ponens_premise_mismatch :
    run [mpSetup] [[.modusPonens 1 1 3]] = .rejected 1 0 .theoremFailed := by decide +kernel

theorem open_axiom_refused :
    run [[.termNewBVar 0 1, .addAxiom 1 1]] [] = .rejected 0 1 .theoremFailed := by decide +kernel

theorem value_too_deep_for_arity :
    run [instSetup] [[.thmInstantiate 1 14 4 2]] = .rejected 1 0 .theoremFailed := by decide +kernel

theorem constant_cannot_be_instantiated :
    run [binderSetup] [[.thmInstantiate 1 15 5 2]] = .rejected 1 0 .theoremFailed := by decide +kernel

theorem literal_order_requires_less :
    run [axiomSetup] [[.litLt 5 5 2]] = .rejected 1 0 .theoremFailed := by decide +kernel

theorem division_by_zero_refused :
    run [axiomSetup] [[.litDiv 5 0 2]] = .rejected 1 0 .theoremFailed := by decide +kernel

theorem byte_index_bounded :
    run [[.termNewLiteral [7, 8] 1]] [[.litGet 1 2 1]] = .rejected 1 0 .theoremFailed := by
  decide +kernel

theorem byte_index_in_range :
    run [[.termNewLiteral [7, 8] 1]] [[.litGet 1 1 1]] = .proofs 0 0 0 := by decide +kernel

theorem open_definition_body_refused :
    run [[.fvarNew 1 13, .termNewBVar 0 1, .termNewApp 13 [1] 2,
      .defineConst [13] [0] 2 14 1]] [] = .rejected 0 3 .definitionFailed := by decide +kernel

theorem definition_hint_mismatch :
    run [[.fvarNew 1 13, .fvarNew 1 14, .termNewLiteral [0] 1, .termNewApp 13 [1] 2,
      .defineConst [13, 14] [1] 2 15 1]] [] = .rejected 0 4 .definitionFailed := by decide +kernel

theorem exchange_needs_equal_statement :
    run [axiomSetup ++ [.thmExchange 1 1]] [] = .rejected 0 5 .exchangeMismatch := by decide +kernel

theorem challenge_mismatch :
    run [mpSetup] [[.challengeSatisfy 0 1]] = .rejected 1 0 .challengeMismatch := by decide +kernel

theorem satisfied_challenge_slot_is_cleared :
    run [axiomSetup] [[.challengeSatisfy 0 1, .challengeSatisfy 0 1]] =
      .rejected 1 1 .noChallenge := by decide +kernel

theorem largest_word_index_unbuildable :
    run [[.termNewBVar maxWord 1]] [] = .rejected 0 0 .termBuildFailed := by decide +kernel

theorem execution_primitive_is_unsupported :
    run [axiomSetup] [[.jit 1 2 3, .challengeSatisfy 0 1]] = .unsupported 1 0 := by decide +kernel

theorem execution_primitive_unsupported_in_setup :
    run [[.jit 1 2 3]] [] = .unsupported 0 0 := by decide +kernel

end Mettapedia.Languages.VibeITP.Spec.Controls
