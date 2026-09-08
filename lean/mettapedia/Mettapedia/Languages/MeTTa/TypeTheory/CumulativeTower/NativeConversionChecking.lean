import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILRootConversionCode
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedRootConversionCode
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.StructuralConversionCodeDependencies
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveMILQualification

/-!
# Native conversion checking at the formation-sensitive admission boundary

The two existing authored packages instantiate the same finite-code checker.
Exactness includes all raw open conversions, not only constructor quotation or
canonical redexes. The packages are qualified separately; this is not a theorem
about the union of their declarations or a decision procedure for finding a code.

Conversion checking enters typing only alongside an admitted source and an
independently formed target type. Forward-step checking can additionally use
the actual MIL preservation theorem. Symmetric conversion is not execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower

namespace Presentation.FormationSensitive

variable {Head : Type} [DecidableEq Head] {R : Rules Head}
    [DecidableRel R.headEq] {n : Nat}

/-- Checked conversion does not replace either source admission or target
formation. Both belong to the selected judgment and context. -/
theorem Judgment.convertChecked
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    {context : Ctx Head n} {term sourceType targetType : Tm Head n} {sortHead : Head}
    (source : Judgment R context term sourceType)
    (targetFormed : Typing R context targetType (.head sortHead))
    (isUniverse : R.isUniverse sortHead)
    {code : StructuralConversionCode.Code Head decoder.Code n}
    (checked : code.check R.headEq decoder.decode sourceType targetType = true) :
    Judgment R context term targetType :=
  ⟨source.context, .conv source.typing targetFormed isUniverse
    (StructuralConversionCode.Code.check_sound decoder checked)⟩

end Presentation.FormationSensitive

namespace NativeConversionChecking

open Presentation StructuralConversionCode

variable {n : Nat}

abbrev MILCode (n : Nat) := Code Tower.Head MILRootConversionCode.Code n

abbrev IndexedCode (n : Nat) :=
  Code Tower.Head NativeIndexedFamilies.Intrinsic.IotaEvidenceCode n

/-- The original MIL conversion relation, without auxiliary completed roots. -/
def checkMIL (code : MILCode n) (left right : Tower.Tm n) : Bool :=
  code.check Tower.HeadEq MILRootConversionCode.decode left right

/-- The original List and identity package, checked with the same structural core. -/
def checkIndexed (code : IndexedCode n) (left right : Tower.Tm n) : Bool :=
  code.check Tower.HeadEq NativeIndexedRootConversionCode.decode left right

theorem mil_conversion_iff_checked {left right : Tower.Tm n} :
    Conv IntrinsicMILHypothesis.rules.headEq left right
        IntrinsicMILHypothesis.rules.computation ↔
      ∃ code : MILCode n, checkMIL code left right = true :=
  Code.conversion_iff_checked (headEq := Tower.HeadEq) MILRootConversionCode.decoder

theorem indexed_conversion_iff_checked {left right : Tower.Tm n} :
    Conv NativeIndexedFamilies.Intrinsic.rules.headEq left right
        NativeIndexedFamilies.Intrinsic.rules.computation ↔
      ∃ code : IndexedCode n, checkIndexed code left right = true :=
  Code.conversion_iff_checked (headEq := Tower.HeadEq)
    NativeIndexedRootConversionCode.rootDecoder

/-- The native constructor boundary rules out every purported finite code,
not only one hand-picked malformed candidate. -/
theorem mil_pi_head_has_no_code {domain : Tower.Tm n}
    {codomain : Tower.Tm (n + 1)} {head : Tower.Head} :
    ¬ ∃ code : MILCode n, checkMIL code (.pi domain codomain) (.head head) = true := by
  intro checked
  exact MILConversionParallel.nativePiConversionBoundary.headDisjoint
    (mil_conversion_iff_checked.mpr checked)

/-- Every accepted forward MIL step preserves every admitted refined source
judgment, with its original dependent displayed type. -/
theorem checked_mil_step_preserves
    {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicMILHypothesis.rules
      context source displayed)
    {code : StepCode Tower.Head MILRootConversionCode.Code n}
    (checked : code.check Tower.HeadEq MILRootConversionCode.decode source target = true) :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules context target displayed :=
  FormationSensitiveMILQualification.steps_preserve judgment
    (.tail .refl (StepCode.check_sound (headEq := Tower.HeadEq)
      MILRootConversionCode.decoder checked))

namespace Examples

open IntrinsicMILHypothesis

/-- The variable outside the lambda remains outside it after beta reduction. -/
def beneathBinder : StepCode Tower.Head MILRootConversionCode.Code 1 :=
  .congLam (.betaPi (.var 2) (.var 0))

def beneathBinderSource : Tower.Tm 1 :=
  .lam (.app (.lam (.var 2)) (.var 0))

theorem beta_beneath_binder_checked :
    checkMIL (.single beneathBinder) beneathBinderSource (.lam (.var 1)) = true := by
  decide

theorem variable_capture_rejected :
    checkMIL (.single beneathBinder) beneathBinderSource (.lam (.var 0)) = false := by
  decide

/-- Reversing evidence is legitimate conversion, not a forward evaluation step. -/
theorem symmetric_beta_checked :
    checkMIL (.symm (.single beneathBinder)) (.lam (.var 1)) beneathBinderSource = true := by
  decide

def firstHead : Tower.Head := .sort (.max (.param 0) (.const 0))
def secondHead : Tower.Head := .sort (.param 0)

/-- Conversion of levels is semantic: these heads are not syntactically equal. -/
theorem head_bridge_checked :
    checkMIL (.single (.head firstHead secondHead) : MILCode 0)
      (.head firstHead) (.head secondHead) = true := by decide

def brokenJoin : MILCode 0 := .trans (.refl (.head firstHead)) (.refl (.head secondHead))

theorem mismatched_join_rejected :
    checkMIL brokenJoin (.head firstHead) (.head secondHead) = false := by decide

def repairedJoin : MILCode 0 :=
  .trans (.refl (.head firstHead))
    (.trans (.single (.head firstHead secondHead)) (.refl (.head secondHead)))

/-- An explicit bridge repairs the path. Refusal of one malformed code is
not a proof that its claimed endpoints are nonconvertible. -/
theorem explicit_bridge_repairs_join :
    checkMIL repairedJoin (.head firstHead) (.head secondHead) = true ∧
      checkMIL brokenJoin (.head firstHead) (.head secondHead) = false := by decide

def primitiveStep : StepCode Tower.Head MILRootConversionCode.Code 8 :=
  .root MILRootConversionCode.Examples.primitiveCode

theorem primitive_step_checked :
    primitiveStep.check Tower.HeadEq MILRootConversionCode.decode
      primitiveIotaLeft primitiveIotaRight = true := by decide

/-- Both dependent endpoints are converted by actual native primitive steps. -/
def primitiveIdentityTypeCode : MILCode 8 :=
  .trans (.single (.congIdLeft primitiveIotaResultType primitiveStep primitiveIotaLeft))
    (.single (.congIdRight primitiveIotaResultType primitiveIotaRight primitiveStep))

theorem primitive_identity_type_checked :
    checkMIL primitiveIdentityTypeCode
      (.id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft)
      (.id primitiveIotaResultType primitiveIotaRight primitiveIotaRight) = true := by
  decide

/-- An actual dependent judgment consumes checked conversion while separately
retaining the formation proof of the new identity type. -/
theorem checked_dependent_identity_admission :
    FormationSensitive.Judgment rules contextSPMPCSourceTargetSymbol
      (.refl primitiveIotaLeft)
      (.id primitiveIotaResultType primitiveIotaRight primitiveIotaRight) := by
  letI : DecidableRel rules.headEq := Tower.instDecidableHeadEq
  have source := FormationSensitiveMILElimination.primitiveIota_judgments.1
  have target := checked_mil_step_preserves source primitive_step_checked
  obtain ⟨sortHead, isUniverse, typeFormed⟩ :=
    source.regularity (FormationSensitive.towerUniverseRegularity.includeSignature rawSignature)
  have identitySource : FormationSensitive.Judgment rules contextSPMPCSourceTargetSymbol
      (.refl primitiveIotaLeft)
      (.id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft) :=
    ⟨source.context, .reflIntro source.typing⟩
  exact identitySource.convertChecked MILRootConversionCode.decoder
    (.idForm typeFormed.typing isUniverse target.typing target.typing) isUniverse
    primitive_identity_type_checked

theorem checked_identity_elimination :
    checkIndexed (.single (.root NativeIndexedRootConversionCode.identityCode))
      NativeIndexedFamilies.Intrinsic.identityIotaLeft
      NativeIndexedFamilies.Intrinsic.identityIotaRight = true := by decide

/-- Reflexive conversion of undeclared syntax is valid raw conversion. It
does not establish a typing judgment for that syntax. -/
theorem conversion_does_not_supply_formation :
    checkMIL (.refl (.const FormationSensitiveMIL.Examples.missingName) : MILCode 0)
      (.const FormationSensitiveMIL.Examples.missingName)
      (.const FormationSensitiveMIL.Examples.missingName) = true ∧
    ¬ ∃ type : Tower.Tm 0, FormationSensitive.Judgment rules .nil
      (.const FormationSensitiveMIL.Examples.missingName) type := by
  constructor
  · decide
  · rintro ⟨type, judgment⟩
    exact FormationSensitiveMIL.Examples.missing_primitive_rejected judgment.typing

/-- Equal endpoints do not identify the retained evidence constructors. -/
theorem distinct_paths_same_endpoints :
    checkMIL (.refl (.head secondHead) : MILCode 0)
      (.head secondHead) (.head secondHead) = true ∧
    checkMIL (.single (.head secondHead secondHead) : MILCode 0)
      (.head secondHead) (.head secondHead) = true ∧
    (.refl (.head secondHead) : MILCode 0) ≠ .single (.head secondHead secondHead) := by
  refine ⟨by decide, by decide, ?_⟩
  intro impossible
  cases impossible

/-! ## Finite dependency checks and verdict invalidation

These perturbed decoding functions test the reuse boundary. They are not
qualified as new logical profiles. Transporting a logical claim to another
profile additionally needs that profile's independent root qualification.
-/

def withoutChain : {n : Nat} → MILRootConversionCode.Code n →
    Option (Tower.Tm n × Tower.Tm n)
  | _, code@(.primitive _ _ _ _ _ _ _ _) => MILRootConversionCode.decode code
  | _, .chain _ _ _ _ _ _ _ _ _ _ => none

def changedPrimitiveOutput : {n : Nat} → MILRootConversionCode.Code n →
    Option (Tower.Tm n × Tower.Tm n)
  | _, code@(.primitive _ _ _ _ _ _ _ _) => some (code.endpoints.1, .head .legacyGround)
  | _, code@(.chain _ _ _ _ _ _ _ _ _ _) => MILRootConversionCode.decode code

theorem retained_root_requests_agree :
    agreeOnCheck primitiveIdentityTypeCode.rootRequests
      MILRootConversionCode.decode withoutChain = true := by decide

/-- Removing an unused branch preserves the exact verdict at every pair of
claimed endpoints, not just the one successful claim. -/
theorem unused_branch_change_reuses (left right : Tower.Tm 8) :
    checkMIL primitiveIdentityTypeCode left right =
      primitiveIdentityTypeCode.check Tower.HeadEq withoutChain left right :=
  Code.check_eq_of_agreeOnCheck Tower.HeadEq primitiveIdentityTypeCode left right
    retained_root_requests_agree

theorem unused_branch_preserves_success_and_failure :
    primitiveIdentityTypeCode.check Tower.HeadEq withoutChain
      (.id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft)
      (.id primitiveIotaResultType primitiveIotaRight primitiveIotaRight) = true ∧
    primitiveIdentityTypeCode.check Tower.HeadEq withoutChain
      (.id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft)
      (.head .legacyGround) = false := by decide

theorem used_root_change_detected :
    agreeOnCheck primitiveIdentityTypeCode.rootRequests
      MILRootConversionCode.decode changedPrimitiveOutput = false ∧
    primitiveIdentityTypeCode.check Tower.HeadEq changedPrimitiveOutput
      (.id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft)
      (.id primitiveIotaResultType primitiveIotaRight primitiveIotaRight) = false := by
  decide

/-- The removed branch really changes the decoder and invalidates its own
formerly accepted chain evidence. The positive reuse is not global agreement. -/
theorem omitted_branch_is_observable :
    checkMIL (.single (.root MILRootConversionCode.Examples.chainCode))
      chainIotaLeft chainIotaRight = true ∧
    Code.check Tower.HeadEq withoutChain
      (.single (.root MILRootConversionCode.Examples.chainCode))
      chainIotaLeft chainIotaRight = false := by decide

def binderRoundTrip : MILCode 7 :=
  .trans (.single (.congLam primitiveStep)) (.symm (.single (.congLam primitiveStep)))

/-- The outer code has seven variables; each retained root under its lambda
has eight. Both occurrences remain in the manifest. -/
theorem binder_root_scopes_retained :
    binderRoundTrip.rootRequests =
      [⟨8, MILRootConversionCode.Examples.primitiveCode⟩,
        ⟨8, MILRootConversionCode.Examples.primitiveCode⟩] := rfl

theorem binder_round_trip_checked :
    checkMIL binderRoundTrip (.lam primitiveIotaLeft) (.lam primitiveIotaLeft) = true := by
  decide

theorem binder_round_trip_reuses (left right : Tower.Tm 7) :
    checkMIL binderRoundTrip left right =
      binderRoundTrip.check Tower.HeadEq withoutChain left right := by
  apply Code.check_eq_of_agreeOnCheck
  decide

end Examples

#print axioms Presentation.FormationSensitive.Judgment.convertChecked
#print axioms mil_conversion_iff_checked
#print axioms indexed_conversion_iff_checked
#print axioms mil_pi_head_has_no_code
#print axioms checked_mil_step_preserves
#print axioms Examples.beta_beneath_binder_checked
#print axioms Examples.variable_capture_rejected
#print axioms Examples.symmetric_beta_checked
#print axioms Examples.explicit_bridge_repairs_join
#print axioms Examples.checked_dependent_identity_admission
#print axioms Examples.checked_identity_elimination
#print axioms Examples.conversion_does_not_supply_formation
#print axioms Examples.distinct_paths_same_endpoints
#print axioms Examples.retained_root_requests_agree
#print axioms Examples.unused_branch_change_reuses
#print axioms Examples.unused_branch_preserves_success_and_failure
#print axioms Examples.used_root_change_detected
#print axioms Examples.omitted_branch_is_observable
#print axioms Examples.binder_root_scopes_retained
#print axioms Examples.binder_round_trip_checked
#print axioms Examples.binder_round_trip_reuses

end NativeConversionChecking
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
