import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeNamedGeneralization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeProductClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeReceivedFrame

/-! Positive named GEN uses the actual admitted Boolean definition objects.
These compact controls do not supply the nine concrete product readings. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeProductClosureControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open StandardTheoryInterpretation NativeNamedGeneralization

local instance : DecidablePred SourceProfileModels.policy := inferInstance
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def truthObject : ConstantDefinitionResult :=
  (checkConstantDefinition (.global "T") Source.truthBody).get (by decide +kernel)

def universalObject : ConstantDefinitionResult :=
  (checkConstantDefinition (.global "!") Source.universalBody).get (by decide +kernel)

theorem truthObject_is_admitted : truthObject = Source.truthResult.output := by
  have computed : checkConstantDefinition (.global "T") Source.truthBody = some truthObject :=
    (Option.some_get _).symm
  have actual := (DefinitionAdapters.admitConstantInTheory_result Source.truthAdmitted).2.2.2.2.1
  exact Option.some.inj (computed.symm.trans actual)

theorem universalObject_is_admitted : universalObject = Source.universalResult.output := by
  have computed : checkConstantDefinition (.global "!") Source.universalBody = some universalObject :=
    (Option.some_get _).symm
  have actual := (DefinitionAdapters.admitConstantInTheory_result Source.universalAdmitted).2.2.2.2.1
  exact Option.some.inj (computed.symm.trans actual)

def actualTruth : Theorem := truthObject.definitionTheorem

def actualUniversalBool : Theorem :=
  substituteTheorem (SourceSubstitution.typeOnlySubstitution [(Ty.bool, .var (.global "A"))])
    universalObject.definitionTheorem

def actualDefinitions : ProofExecution.State := GraphExpansion.start [actualUniversalBool, actualTruth]

def binder : SourceVar := ⟨.global "x", Ty.bool⟩
def operand : CanonicalTerm := CanonicalTerm.free binder
def input : Theorem := EqualityExpansion.reflexivity operand

def conversion : Option Theorem := do
  let (state, root) ← functionConversion? .prop actualDefinitions 0 1 ("actual-named-universal", 0)
  state.cache[root]?

def namedReflexivity : Option (Σ actual : Theorem, NamedBlock SourceProfileModels.policy input actual binder) := do
  let actual ← conversion
  let checked ← namedGenBlock? SourceProfileModels.policy input actual binder ("actual-named-GEN", 1)
  return ⟨actual, checked⟩

theorem actual_definition_reads :
    (CachedSourceExpansion.readAll? actualDefinitions
      [(universalBinding .prop).equation, truthBinding.equation] [0, 1]).isSome = true := by
  decide +kernel

theorem actual_definition_conversion : conversion.isSome = true := by
  obtain ⟨sources, read⟩ := Option.isSome_iff_exists.mp actual_definition_reads
  obtain ⟨after, root, fact, computed, _, found, _, _, _, _⟩ :=
    functionConversion_checked .prop 0 1 sources read
      (GraphExpansion.start_checked emptyAxiomPolicy [actualUniversalBool, actualTruth])
      ("actual-named-universal", 0)
  exact Option.isSome_iff_exists.mpr ⟨fact, by simp only [conversion, computed, found, bind, Option.bind_some]⟩

/-- This is the independently specified conversion claim used as one compact
external premise. Its source-definition derivation is checked above. -/
def conversionClaim : Theorem :=
  Theorem.emptyResult ∅ (CachedSourceExpansion.encode (functionEquation .prop))

def compactNamedGen : Option (NamedBlock SourceProfileModels.policy input conversionClaim binder) :=
  namedGenBlock? SourceProfileModels.policy input conversionClaim binder ("compact-named-GEN", 4)

theorem compact_named_gen_checked : compactNamedGen.isSome = true := by
  decide +kernel

def captured : Theorem := Theorem.emptyResult {operand} operand

theorem captured_variable_refused (equation : Theorem) :
    namedGenBlock? SourceProfileModels.policy captured equation binder ("captured-named-GEN", 2) = none := by
  apply NativeNamedGeneralization.captured_variable_refused
  exact ⟨operand, Finset.mem_singleton_self _, DBTerm.FreeOccurrence.here⟩

theorem actual_truth_missing_refused :
    functionConversion? .prop (GraphExpansion.start [actualUniversalBool]) 0 1
      ("missing-actual-truth", 3) = none := by
  apply missing_truth_refused
  rfl

def primitiveBefore : ProofExecution.Registered.State :=
  ProofExecution.Registered.empty SourceProfile.primitiveContext

def primitiveCertificate : ProofSystem.Certificate :=
  GraphExpansion.primitiveBlock (.inference (.refl operand)) input ("registered-source-GEN-control", 5)

def primitiveBlock : CheckedBlock SourceProfileModels.policy [] :=
  (checkBlock? SourceProfileModels.policy [] primitiveCertificate).get (by decide +kernel)

theorem actual_registered_block_appended :
    (NativeProductClosure.appendBlock? (NativeProductClosure.ProofRun.start primitiveBefore)
      [] primitiveBlock).isSome = true := by
  decide +kernel

theorem actual_future_parent_refused :
    NativeProductClosure.appendBlock? (NativeProductClosure.ProofRun.start primitiveBefore)
      [0] primitiveBlock = none := by
  rfl

#check_failure fun (state : ProofExecution.Registered.State)
    (first second : SourceProfileModels.ProfileFrame.{0} state) (ops : NativeClauseData.Operations)
    (table : Fin 29 → NativeFieldSchema.Syntax ops) (index : Fin 29)
    (other : TypeFamilySemantics.OperatorFamilies.{0}) (assignment : TypeFamilySemantics.Assignment.{0})
    (view : NativeReceivedFrame.actualCallView first table index other assignment) =>
  (show NativeReceivedFrame.actualCallView second table index other assignment from view)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeProductClosureControls
