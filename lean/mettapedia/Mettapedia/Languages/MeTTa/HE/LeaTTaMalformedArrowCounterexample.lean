import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.Substitution
import Std.Data.HashMap.Lemmas

/-!
# Malformed-arrow candidate counterexample

The pre-repair application-type scan treated a bare `(->)` annotation as a
zero-argument function whose missing return defaulted to `%Undefined%`.
That behavior is masked when it is the only candidate, because the outer
fallback emits the same singleton.  It becomes observable beside a valid
candidate: the malformed annotation contributes an extra leading result.

The executable-independent spec scan rejects the bare arrow because it has
no return component, while preserving the later valid nullary candidate.
These canaries pin both the old defect and the intended ordered result.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMalformedArrowCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact

private def bareArrow : Metta.Atom :=
  .expr [.sym "->"]

private def validNullaryArrow : Metta.Atom :=
  .expr [.sym "->", .sym "R"]

/-- The application-candidate scan used before the malformed-arrow repair. -/
private def legacyApplicationTypeResults
    (functionTypes actualTypes : List Metta.Atom) : List Metta.Atom :=
  functionTypes.filterMap fun type =>
    match type with
    | .expr (.sym "->" :: types) =>
        let returnType :=
          (types.getLast?).getD (.sym "%Undefined%")
        match Metta.Minimal.matchApplicationTypeArguments
            Metta.Bindings.empty types.dropLast actualTypes with
        | some bindings => some (Metta.instantiate bindings returnType)
        | none => none
    | _ => none

/-- Negative legacy canary: the malformed first candidate contributed a
spurious observable `%Undefined%` before the later valid return. -/
theorem legacy_mixed_arrows_emit_spurious_undefined :
    legacyApplicationTypeResults [bareArrow, validNullaryArrow] [] =
      [.sym "%Undefined%", .sym "R"] := by
  simp [legacyApplicationTypeResults, bareArrow, validNullaryArrow,
    Metta.Minimal.matchApplicationTypeArguments, Metta.Bindings.empty,
    Metta.instantiate_nil]

private def malformedNativeArrow : Atom :=
  .expression [.symbol "->"]

private def validNativeNullaryArrow : Atom :=
  .expression [.symbol "->", .symbol "R"]

private theorem malformedArrowNoSuccess (result : TypePackage) :
    ¬ApplicationPackageSuccessRel [] malformedNativeArrow result := by
  intro success
  cases success with
  | @mk _ returnType expectedTypes _ _ shape _ =>
      have lengths := congrArg (fun atom => match atom with
        | .expression atoms => atoms.length
        | _ => 0) shape
      simp [malformedNativeArrow] at lengths

private theorem validNullaryArrowSuccess :
    ApplicationPackageSuccessRel [] validNativeNullaryArrow
      (publishedPackage (.symbol "R")) := by
  simpa [validNativeNullaryArrow, inferredPackage, publishedPackage,
    RuntimeTypePackage.published] using
      (ApplicationPackageSuccessRel.mk
        (operatorType := validNativeNullaryArrow)
        (returnType := .symbol "R")
        (expectedTypes := []) (actualTypes := [])
        (substitution := []) rfl
        (PresentationArgumentListMatchRel.nil []))

/-- Positive spec boundary: the malformed candidate is skipped and the
later valid nullary arrow contributes exactly `R`. -/
theorem spec_mixed_arrow_scan_emits_only_valid_return :
    ApplicationPackageScanRel []
      [malformedNativeArrow, validNativeNullaryArrow]
      [publishedPackage (.symbol "R")] := by
  apply ApplicationPackageScanRel.skip
  · exact ApplicationPackageOutcomeRel.failure malformedArrowNoSuccess
  · apply ApplicationPackageScanRel.emit
    · exact ApplicationPackageOutcomeRel.success validNullaryArrowSuccess
    · exact ApplicationPackageScanRel.nil

private def mixedArrowEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "mixed", bareArrow],
    .expr [.sym ":", .sym "mixed", validNullaryArrow]] []

private def mixedArrowCall : Metta.Atom :=
  .expr [.sym "mixed"]

/-- Positive executable canary: the repaired scan skips the malformed first
candidate and retains the later valid nullary return. -/
theorem repaired_mixed_arrows_emit_only_valid_return :
    Metta.Minimal.getTypes mixedArrowEnv mixedArrowCall = [.sym "R"] := by
  have operatorTypes :
      Metta.Minimal.getTypes mixedArrowEnv (.sym "mixed") =
        [bareArrow, validNullaryArrow] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [mixedArrowEnv, bareArrow, validNullaryArrow,
      Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_emptyWithCapacity]
  have noDirect : mixedArrowEnv.exprTypes = [] := rfl
  have sourceAtoms : mixedArrowEnv.atoms = [
      .expr [.sym ":", .sym "mixed", bareArrow],
      .expr [.sym ":", .sym "mixed", validNullaryArrow]] := rfl
  rw [show mixedArrowCall = .expr [.sym "mixed"] from rfl,
    Metta.Minimal.getTypes.eq_10 _ _ _ (by simp)]
  simp [operatorTypes, noDirect, sourceAtoms,
    Metta.Minimal.typeInferenceAvoid, Metta.Atom.vars,
    Metta.Minimal.freshenArgumentTypes,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.Minimal.matchApplicationTypeArguments, Metta.instantiate_nil,
    bareArrow, validNullaryArrow]

end Mettapedia.Languages.MeTTa.HE.LeaTTaMalformedArrowCounterexample
