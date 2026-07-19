import Mettapedia.Languages.MeTTa.HE.HumanTypeConformance
import Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement
import MettaHyperonFull.Minimal.Interpreter
import Std.Data.HashMap.Lemmas

/-!
# R3 state-wrapper representation refinement

LeaTTa represents a state handle prepared for type lookup as the ordinary
expression `(StateValue value)` and synthesizes `(StateMonad contentType)`.
Unlike Hyperon's grounded state object, this spelling is forgeable directly in
source syntax.  R3 records the executable behavior without pretending it is a
published-core rule.  The canary below pins that representation leak.

The clean future migration is to represent state handles as unforgeable
grounded values carrying their `StateMonad` type, matching Hyperon and making
R3 unnecessary.  That migration is optional and outside the current tranche.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaStateValueRefinement

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec
open HumanTypeConformance
open HumanTypeRuntimeRefinement

private def forgedStateValue : Atom :=
  .expression [.symbol "StateValue", .grounded (.int 1)]

private def stateMonadNumber : Atom :=
  .expression [.symbol "StateMonad", .symbol "Number"]

private def forgedLeaStateValue : Metta.Atom :=
  .expr [.sym "StateValue", .gnd (.int 1)]

private def emptyEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [] []

/-- Published-core lookup sees no direct annotation for the forged expression. -/
theorem published_forged_stateValue_undefined :
    TypesOfRel Space.empty forgedStateValue [Atom.undefinedType] := by
  exact TypesOfRel.expressionUndefined AnnotationTypesRel.nil

/-- Negative core witness: synthesized state-monad typing is not a published
type-lookup derivation for the forgeable expression. -/
theorem published_forged_stateValue_not_stateMonad :
    ¬TypeOfRel Space.empty forgedStateValue stateMonadNumber := by
  intro htype
  have hmem := (typeOfRel_iff_mem_getAtomTypes _ _ _).mp htype
  simp [forgedStateValue, stateMonadNumber, getAtomTypes,
    getAnnotatedTypes, Atom.undefinedType, Space.empty] at hmem

private theorem forged_content_number_evidence :
    RuntimeTypeEvidenceRel Space.empty (.grounded (.int 1))
      (.symbol "Number") := by
  apply RuntimeTypeEvidenceRel.published
  refine ⟨[.symbol "Number"], ?_, by simp⟩
  exact TypesOfRel.groundedKnown
    (IntrinsicGroundedTypeRel.int 1) (by decide)

/-- Positive R3 witness: the rule applies to source-forged syntax exactly as
it applies to an internally produced wrapper. -/
theorem r3_forged_stateValue_stateMonad :
    R3StateValueTypeRel Space.empty forgedStateValue stateMonadNumber := by
  exact R3StateValueTypeRel.mk forged_content_number_evidence

/-- Negative R3 boundary: an atom without the `StateValue` wrapper shape has
no R3 derivation. -/
theorem r3_symbol_not_stateValue (type : Atom) :
    ¬R3StateValueTypeRel Space.empty (.symbol "StateValue") type := by
  intro h
  cases h

/-- Executable side of the representation leak: the same forged spelling is
special-cased by the runtime type service. -/
theorem leatta_forged_stateValue_stateMonad :
    Metta.Minimal.getTypes emptyEnv forgedLeaStateValue =
      [.expr [.sym "StateMonad", .sym "Number"]] := by
  rw [show forgedLeaStateValue =
      .expr [.sym "StateValue", .gnd (.int 1)] from rfl,
    Metta.Minimal.getTypes.eq_9,
    Metta.Minimal.getTypes.eq_1]
  rfl

/-- Permanent divergence canary: published-core lookup rejects the synthesized
type, while unrestricted named R3 and the current LeaTTa representation both
accept it. -/
theorem forged_stateValue_representation_leak_canary :
    ¬TypeOfRel Space.empty forgedStateValue stateMonadNumber ∧
      R3StateValueTypeRel Space.empty forgedStateValue stateMonadNumber ∧
      Metta.Minimal.getTypes emptyEnv forgedLeaStateValue =
        [.expr [.sym "StateMonad", .sym "Number"]] :=
  ⟨published_forged_stateValue_not_stateMonad,
    r3_forged_stateValue_stateMonad,
    leatta_forged_stateValue_stateMonad⟩

/-! ## Exact-lookup priority canary -/

private def stateApplicabilityEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "accepts-number",
      .expr [.sym "->", .sym "Number", .sym "R"]]] []

private def forgedStateCall : Atom :=
  .expression [.symbol "accepts-number", forgedStateValue]

private def forgedStateFunctionType : Atom :=
  .expression [.symbol "->", .symbol "Number", .symbol "R"]

private theorem published_forged_stateValue_undefined_type :
    TypeOfRel Space.empty forgedStateValue Atom.undefinedType :=
  ⟨[Atom.undefinedType], published_forged_stateValue_undefined, by simp⟩

private theorem number_undefined_runtime_match :
    CorePlusR2TypeMatchRel (.symbol "Number") Atom.undefinedType
      Bindings.empty Bindings.empty := by
  constructor
  · exact ⟨fun name => .var name, by
      simp [HumanTypeBindingSatisfied, Bindings.empty]⟩
  · intro valuation
    simp [HumanTypeBindingSatisfied, Bindings.empty,
      CorePlusR2TypeConsistent, Atom.undefinedType]

private theorem R_R_runtime_match :
    CorePlusR2TypeMatchRel (.symbol "R") (.symbol "R")
      Bindings.empty Bindings.empty := by
  constructor
  · exact ⟨fun name => .var name, by
      simp [HumanTypeBindingSatisfied, Bindings.empty]⟩
  · intro valuation
    simp [HumanTypeBindingSatisfied, Bindings.empty,
      CorePlusR2TypeConsistent, ReducedTypeConsistent,
      Atom.undefinedType, Atom.atomType]

/-- A permissive union of published and refined type evidence admits the
published `%Undefined%` fallback even though R3 is the runtime-selected type. -/
theorem permissive_runtime_evidence_accepts_forged_state_as_number :
    RuntimeApplicabilityRel Space.empty forgedStateCall
      forgedStateFunctionType (.symbol "R") Bindings.empty
      (.success Bindings.empty) := by
  apply RuntimeApplicabilityRel.success
  apply RuntimeApplicationSuccessRel.mk
      (operator := .symbol "accepts-number")
      (arguments := [forgedStateValue])
      (argumentTypes := [.symbol "Number"])
      (returnType := .symbol "R")
      (afterArguments := Bindings.empty)
  · rfl
  · rfl
  · exact RuntimeArgumentsApplicableRel.cons
      (RuntimeTypeEvidenceRel.published
        published_forged_stateValue_undefined_type)
      (TypeVariableRenamingOf.refl _)
      number_undefined_runtime_match
      (RuntimeArgumentsApplicableRel.nil Bindings.empty)
  · exact R_R_runtime_match

/-- LeaTTa's ordered lookup selects only `StateMonad Number`, so the same
argument is rejected against `Number`. -/
theorem leatta_ordered_state_type_rejects_number_parameter :
    Metta.Minimal.typeMismatch stateApplicabilityEnv
      Metta.Minimal.World.empty "accepts-number" [forgedLeaStateValue] =
        some (1, .sym "Number",
          .expr [.sym "StateMonad", .sym "Number"]) := by
  have hopPrep : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "accepts-number") = .sym "accepts-number" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hopTypes : Metta.Minimal.getTypes stateApplicabilityEnv (.sym "accepts-number") =
      [.expr [.sym "->", .sym "Number", .sym "R"]] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [stateApplicabilityEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_emptyWithCapacity]
  have hprep : Metta.Minimal.typePrep Metta.Minimal.World.empty
      forgedLeaStateValue = forgedLeaStateValue := by
    rw [Metta.Minimal.typePrep]
    simp only [forgedLeaStateValue, Metta.Minimal.subTokens]
    rw [Metta.Minimal.wrapStates.eq_2] <;>
      simp [Metta.Minimal.subTokens, Metta.Minimal.wrapStates,
        Metta.Minimal.World.empty]
  have htypes : Metta.Minimal.getTypes stateApplicabilityEnv
      forgedLeaStateValue =
        [.expr [.sym "StateMonad", .sym "Number"]] := by
    rw [show forgedLeaStateValue =
        .expr [.sym "StateValue", .gnd (.int 1)] from rfl,
      Metta.Minimal.getTypes.eq_9,
      Metta.Minimal.getTypes.eq_1]
    rfl
  have hmatch : Metta.Minimal.matchType [] (.sym "Number")
      (.expr [.sym "StateMonad", .sym "Number"]) = none := by
    rfl
  have hfreshened : ∀ avoid position,
      Metta.Minimal.freshenTypeCandidate avoid position
        (.expr [.sym "StateMonad", .sym "Number"]) =
        .expr [.sym "StateMonad", .sym "Number"] := by
    intro avoid position
    simp [Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars]
  have hcheck :
      Metta.Minimal.typeCheckArgsOutcome stateApplicabilityEnv
          Metta.Minimal.World.empty [.sym "Number"] 0 [] [forgedLeaStateValue] =
        .failure 1 (.sym "Number") (.expr [.sym "StateMonad", .sym "Number"]) := by
    simp [Metta.Minimal.typeCheckArgsOutcome, hprep, htypes, hmatch, hfreshened,
      Metta.instantiate]
  rw [Metta.Minimal.typeMismatch, Metta.Minimal.selectFunctionType, hopPrep, hopTypes]
  simp [Metta.Minimal.scanFunctionTypeCandidates, hcheck,
    Metta.Minimal.FunctionTypeScanOutcome.prependError]

/-- Permanent precision canary: positive type evidence is not an exact runtime
lookup relation and therefore cannot soundly support negative applicability
premises. -/
theorem permissive_type_evidence_is_not_exact_lookup_canary :
    RuntimeApplicabilityRel Space.empty forgedStateCall
        forgedStateFunctionType (.symbol "R") Bindings.empty
        (.success Bindings.empty) ∧
      Metta.Minimal.typeMismatch stateApplicabilityEnv
        Metta.Minimal.World.empty "accepts-number" [forgedLeaStateValue] =
          some (1, .sym "Number",
            .expr [.sym "StateMonad", .sym "Number"]) :=
  ⟨permissive_runtime_evidence_accepts_forged_state_as_number,
    leatta_ordered_state_type_rejects_number_parameter⟩

end Mettapedia.Languages.MeTTa.HE.LeaTTaStateValueRefinement
