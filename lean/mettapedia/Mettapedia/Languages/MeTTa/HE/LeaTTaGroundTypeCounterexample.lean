import Mettapedia.Languages.MeTTa.HE.HumanTypeConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
import MettaHyperonFull.Minimal.Interpreter

/-!
# External-ground type-tag counterexample

Native custom grounded values carry their intrinsic type name.  The structural
LeaTTa translation preserves that name as the first component of
`Ground.external`.  The pre-repair minimal type service discarded it and
reported the generic meta-type `Grounded`, diverging from both the human type
relation and Hyperon's grounded `type_()` contract.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaGroundTypeCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE.HumanTypeSpec
open Mettapedia.Languages.MeTTa.HE.HumanTypeConformance
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-- Translation-tag contract: the first external component is exactly the
intrinsic type of the source custom grounded value. -/
theorem nativeCustom_externalTag_contract (typeName payload : String) :
    toLeaTTaGround (.custom typeName payload) =
        .external typeName payload ∧
      IntrinsicGroundedTypeRel (.custom typeName payload)
        (.symbol typeName) := by
  exact ⟨rfl, .custom typeName payload⟩

private def customNative : Atom :=
  .grounded (.custom "T" "payload")

private def customLea : Metta.Atom :=
  .gnd (.external "T" "payload")

/-- The exact pre-repair residual-ground branch, retained locally as the
negative capability canary. -/
private def legacyResidualGroundType (_ : Metta.Ground) : List Metta.Atom :=
  [.sym "Grounded"]

/-- Negative legacy witness: the carried intrinsic tag was flattened to the
generic grounded meta-type. -/
theorem legacy_external_type_discards_tag :
    legacyResidualGroundType (.external "T" "payload") =
      [.sym "Grounded"] := by
  rfl

/-- The independent human type relation reads the source custom value's
intrinsic type rather than its grounded meta-type. -/
theorem human_custom_ground_has_carried_type :
    TypeOfRel Space.empty customNative (.symbol "T") := by
  refine ⟨[.symbol "T"], ?_, by simp⟩
  exact TypesOfRel.groundedKnown
    (IntrinsicGroundedTypeRel.custom "T" "payload") (by decide)

/-- The translated witness really is the external payload named above. -/
theorem customNative_translates_to_customLea :
    toLeaTTaAtom customNative = customLea := by
  rfl

private def emptyEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [] []

/-- Positive repair witness: the runtime reads the preserved intrinsic tag. -/
theorem repaired_external_type_preserves_tag :
    Metta.Minimal.getTypes emptyEnv customLea = [.sym "T"] := by
  simpa [customLea] using
    (Metta.Minimal.getTypes.eq_5 emptyEnv "T" "payload")

private def customApplicabilityEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT
    [.expr [.sym ":", .sym "acceptsT",
      .expr [.sym "->", .sym "T", .sym "R"]]] []

/-- Observable applicability canary: the translated custom payload now
satisfies a parameter whose declared type is its carried tag. -/
theorem repaired_external_tag_accepted_by_applicability :
    Metta.Minimal.typeMismatch customApplicabilityEnv
      Metta.Minimal.World.empty "acceptsT" [customLea] = none := by
  have hopPrep : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "acceptsT") = .sym "acceptsT" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hopTypes : Metta.Minimal.getTypes customApplicabilityEnv (.sym "acceptsT") =
      [.expr [.sym "->", .sym "T", .sym "R"]] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [customApplicabilityEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_emptyWithCapacity]
  have hprep : Metta.Minimal.typePrep Metta.Minimal.World.empty customLea =
      customLea := by
    simp [Metta.Minimal.typePrep, customLea,
      Metta.Minimal.subTokens.eq_3, Metta.Minimal.wrapStates.eq_3]
  have htypes : Metta.Minimal.getTypes customApplicabilityEnv customLea =
      [.sym "T"] := by
    simpa [customLea] using
      (Metta.Minimal.getTypes.eq_5 customApplicabilityEnv "T" "payload")
  have hmatch : Metta.Minimal.matchType [] (.sym "T") (.sym "T") =
      some [] := by
    rfl
  have hcheck :
      Metta.Minimal.typeCheckArgsOutcome customApplicabilityEnv
          Metta.Minimal.World.empty [.sym "T"] 0 [] [customLea] = .success [] := by
    simp [Metta.Minimal.typeCheckArgsOutcome, hprep, htypes,
      Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      Metta.instantiate, hmatch]
  rw [Metta.Minimal.typeMismatch, Metta.Minimal.selectFunctionType, hopPrep, hopTypes]
  simp [Metta.Minimal.scanFunctionTypeCandidates, hcheck]

end Mettapedia.Languages.MeTTa.HE.LeaTTaGroundTypeCounterexample
