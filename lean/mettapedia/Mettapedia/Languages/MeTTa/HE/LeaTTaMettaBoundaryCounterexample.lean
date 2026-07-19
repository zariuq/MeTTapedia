import Mettapedia.Languages.MeTTa.HE.HumanEvalSpec
import MettaHyperonFull.Minimal.Interpreter

/-!
# Repaired expected-type and space consumption at LeaTTa's `metta` boundary

The published evaluator gives the `metta` operation semantic control over an
expected result type and a selected atomspace.  Before repair #8, minimal
LeaTTa accepted both arguments syntactically but discarded them before
entering its recursive evaluator.  This file retains that old boundary as a
private executable witness, pins the conflicting human-spec outcome, and
checks the repaired type-selection primitive.

The user-level stdlib function named `type-cast` is a separate wrapper and is
not the counterexample here.  The relevant boundary is the embedded `metta`
instruction corresponding to the evaluator operation.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMettaBoundaryCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanMatchMergeSpec
open HumanTypeSpec
open HumanEvalSpec

private def mettaItem
    (atom expectedType space : Metta.Atom) (bindings : Metta.Bindings) :
    Metta.Minimal.Item :=
  { stack := [{ atom :=
      Metta.Atom.expr [Metta.Atom.sym "metta", atom, expectedType, space] }],
    bnd := bindings }

/-- The pre-repair `metta` branch, retained verbatim as a negative canary.
Both semantic operands were accepted and then ignored. -/
private def legacyMettaBoundary
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (atom : Metta.Atom)
    (_expectedType _space : Metta.Atom) :
    List Metta.Minimal.Item × Metta.Minimal.St :=
  let (pairs, state') :=
    Metta.Minimal.mettaEval env fuel state bindings atom
  (pairs.map (fun pair =>
    Metta.Minimal.finItem [] pair.1 bindings), state')

/-- Kernel-pinned pre-repair defect: changing both the expected type and
selected space left the legacy `metta` branch definitionally unchanged. -/
theorem metta_step_ignores_expected_type_and_space
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (atom expectedLeft expectedRight
      spaceLeft spaceRight : Metta.Atom) :
    legacyMettaBoundary env fuel state bindings atom expectedLeft spaceLeft =
      legacyMettaBoundary env fuel state bindings atom expectedRight
        spaceRight := by
  rfl

/-- Repair canary: the expected-type selector rejects `A` against `B` and
retains the rejected actual type needed for the structured error. -/
theorem repaired_expected_type_selector_rejects_A_as_B :
    Metta.Minimal.matchExpectedType [] (Metta.Atom.sym "B")
        [Metta.Atom.sym "A"] =
      .inl [Metta.Atom.sym "A"] := by
  rfl

/-- Repair canary: the executable boundary constructs the same structured
`BadType` shape as the published evaluator. -/
theorem repaired_bad_type_shape :
    Metta.Minimal.badTypeAtom (Metta.Atom.sym "a") (Metta.Atom.sym "B")
        (Metta.Atom.sym "A") =
      Metta.Atom.expr [Metta.Atom.sym "Error", Metta.Atom.sym "a",
        Metta.Atom.expr [Metta.Atom.sym "BadType", Metta.Atom.sym "B",
          Metta.Atom.sym "A"]] := by
  rfl

private def typedASpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "a", .symbol "A"]]

private def noHostDispatch : HumanGroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

private theorem aHasTypeA :
    TypeOfRel typedASpace (.symbol "a") (.symbol "A") := by
  refine ⟨[.symbol "A"], ?_, by simp⟩
  exact TypesOfRel.symbolKnown
    (AnnotationTypesRel.hit AnnotationTypesRel.nil) (by simp)

private theorem aDoesNotMatchB (candidate : Bindings) :
    ¬TypeMatchRel (.symbol "A") (.symbol "B")
      Bindings.empty candidate := by
  intro hmatch
  obtain ⟨matched, hhuman, _⟩ := hmatch.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide)
  exact symbol_mismatch_not_match (by decide) matched hhuman

/-- The published internal type cast produces the structured error required
by the official evaluator pseudocode for `a : A` at expected type `B`. -/
theorem human_type_cast_rejects_A_as_B :
    TypeCastRel typedASpace (.symbol "a") (.symbol "B") Bindings.empty
      (mkError (.symbol "a") (.badType (.symbol "B") (.symbol "A")),
        Bindings.empty) := by
  apply TypeCastRel.failure (types := [.symbol "A"])
      (actualType := .symbol "A")
  · exact TypesOfRel.symbolKnown
      (AnnotationTypesRel.hit AnnotationTypesRel.nil) (by simp)
  · simp
  · intro candidateType hmem candidate
    simp only [List.mem_singleton] at hmem
    subst candidateType
    exact aDoesNotMatchB candidate

/-- Evaluator-level form of the counterexample: the executable-independent
human relation must expose the structured `BadType B A` result. -/
theorem human_eval_atom_rejects_A_as_B :
    HumanEvalAtomRaw typedASpace noHostDispatch []
      (.symbol "a") (.symbol "B") Bindings.empty
      (mkError (.symbol "a") (.badType (.symbol "B") (.symbol "A")),
        Bindings.empty) := by
  apply HumanEvalAtomRaw.cast
      (.symbol "a") (.symbol "B") Atom.symbolType Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.symbol "a"
  · simp [Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"a", rfl⟩
  · exact human_type_cast_rejects_A_as_B

/-- The spec-required error is observably different from the unchanged atom
currently produced when the expected type is discarded. -/
theorem structured_bad_type_is_not_unchanged_atom :
    mkError (.symbol "a") (.badType (.symbol "B") (.symbol "A")) ≠
      .symbol "a" := by
  decide

end Mettapedia.Languages.MeTTa.HE.LeaTTaMettaBoundaryCounterexample
