import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.CaptureAvoidingFreshening

/-!
# Under-scoped argument-type freshening counterexamples

Argument type candidates are freshened at each recursive applicability node.
The legacy avoid set contained the environment, remaining source arguments,
formal and actual types, and threaded private bindings, but omitted the
expected result type and source arguments already passed by the recursion.
These witnesses permanently pin both the old public/private capture and the
repaired full-boundary avoidance.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeInferenceScopeCounterexample

private def pair (left right : Metta.Atom) : Metta.Atom :=
  .expr [.sym "Pair", left, right]

private def arrow : Metta.Atom :=
  .expr [.sym "->", .var "t", pair (.sym "B") (.var "t")]

private def scopeEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", arrow],
    .expr [.sym ":", .sym "a", .var "u"]] []

private def legacyRuntimeActualAvoid : List Metta.VarName :=
  Metta.Minimal.typeInferenceAvoid scopeEnv (.expr [.sym "a"])
      [.var "t", .var "u"] ++ Metta.Bindings.vars []

private def capturedPublicName : Metta.VarName :=
  Metta.Minimal.captureAvoidingName legacyRuntimeActualAvoid 0 "u"

private def capturedExpected : Metta.Atom :=
  pair (.var capturedPublicName) (.sym "A")

private def legacyFreshActual : Metta.Atom :=
  Metta.Minimal.freshenTypeCandidate legacyRuntimeActualAvoid 0 (.var "u")

private def repairedRuntimeActualAvoid : List Metta.VarName :=
  Metta.Minimal.applicationTypeInferenceScope capturedExpected [.sym "a"] ++
    legacyRuntimeActualAvoid

private def repairedFreshName : Metta.VarName :=
  Metta.Minimal.captureAvoidingName repairedRuntimeActualAvoid 0 "u"

private def repairedFreshActual : Metta.Atom :=
  Metta.Minimal.freshenTypeCandidate repairedRuntimeActualAvoid 0 (.var "u")

/-- The freshener deterministically chooses the very spelling forged in the
expected result type.  This is the private/public name collision at the
candidate-selection boundary. -/
theorem generated_name_collides_with_expected_public_variable :
    legacyFreshActual = .var capturedPublicName ∧
      capturedPublicName ∈ capturedExpected.vars ∧
      capturedPublicName ∉ legacyRuntimeActualAvoid := by
  refine ⟨?_, ?_, ?_⟩
  · simp [legacyFreshActual, Metta.Minimal.freshenTypeCandidate,
      Metta.Minimal.renameAllVars, capturedPublicName]
  · simp [capturedExpected, pair, Metta.Atom.vars]
  · simpa [capturedPublicName] using
      (Metta.Minimal.captureAvoidingName_not_mem
        legacyRuntimeActualAvoid 0 "u")

/-- Including the expected type in the avoid set makes the corresponding
generated name private with respect to every variable observable there. -/
theorem repaired_name_avoids_expected_scope :
    repairedFreshName ∉ capturedExpected.vars := by
  intro hmem
  have hnot := Metta.Minimal.captureAvoidingName_not_mem
    repairedRuntimeActualAvoid 0 "u"
  apply hnot
  change repairedFreshName ∈ repairedRuntimeActualAvoid
  rw [repairedRuntimeActualAvoid,
    Metta.Minimal.applicationTypeInferenceScope]
  exact List.mem_append_left legacyRuntimeActualAvoid
    (List.mem_append_left _ hmem)

/-- The repaired runtime candidate is exactly the fresh atom whose variable
is outside the expected-result scope. -/
theorem repaired_candidate_uses_avoiding_name :
    repairedFreshActual = .var repairedFreshName := by
  simp [repairedFreshActual, repairedFreshName,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars]

/-- The broadened avoid set changes the generated identity in precisely the
collision case pinned above.  This is a positive/negative seam canary; it does
not authorize an executable repair by itself. -/
theorem repaired_name_differs_from_captured_name :
    repairedFreshName ≠ capturedPublicName := by
  intro heq
  apply repaired_name_avoids_expected_scope
  rw [heq]
  exact generated_name_collides_with_expected_public_variable.2.1

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeInferenceScopeCounterexample
