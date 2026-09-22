import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorQualification
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedMatchedIndexService
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedNativeProofService

/-!
# Opaque wire data with the existing native List, J and relator rules

Both component presentations use the same scoped terms and universe heads.
This compatibility package installs the existing opaque wire declarations
over the existing List/J/relator package. Declaration names are checked
disjoint, both formation-sensitive judgments embed, and the wire signature
adds no root equations or conversions.

Service execution remains the original execution on raw Data. Its result
formation is distinct from a checker verdict and from a native dependent
inhabitant. Preserving an original admitted relator step after embedding is
also distinct from a full subject-reduction qualification for every newly
typable judgment of the combined declaration environment.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeWireRelatorCompatibility

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.FormationSensitive (Typing Judgment ContextFormation)
open Presentation.FormationSensitive.Dependencies

variable {n : Nat}

/-- No new symbols, equations or identity policy are authored here. -/
def rules : Rules Tower.Head :=
  extendRules IntrinsicRelator.rules NativeWireData.signature

theorem wire_values_opaque (name : DeclName) :
    NativeWireData.signature.valueOf? name = none := by
  cases name <;>
    simp [Signature.valueOf?, NativeWireData.signature] <;>
    split_ifs <;> simp

private theorem relator_entry_wire_absent {name : DeclName} {entry : Entry Tower.Head}
    (known : IntrinsicRelator.rawSignature.entries name = some entry) :
    NativeWireData.signature.entries name = none := by
  simp only [IntrinsicRelator.rawSignature] at known
  split_ifs at known with hMap hNil hCons hElim
  · subst name; decide
  · subst name; decide
  · subst name; decide
  · subst name; decide
  · simp only [Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList,
      List.foldr, Signature.insert, Signature.empty] at known
    split_ifs at known with hList hNil hCons hElim hIdentity
    · subst name; decide
    · subst name; decide
    · subst name; decide
    · subst name; decide
    · subst name; decide

/-- The infinite literal-name families are fresh against all nine actual
List/J/relator declarations, not merely against the displayed examples. -/
theorem wire_declarations_fresh {name : DeclName} {entry : Entry Tower.Head}
    (known : NativeWireData.signature.entries name = some entry) :
    IntrinsicRelator.rules.constantType name = none := by
  cases relator : IntrinsicRelator.rawSignature.entries name with
  | none =>
      simp [IntrinsicRelator.rules, extendRules, combinedType, Tower.rules,
        Signature.typeOf?, relator]
  | some prior =>
      have absent := relator_entry_wire_absent relator
      rw [absent] at known
      cases known

theorem wire_constant_preserved {name : DeclName} {type : Tower.Tm 0}
    (known : NativeWireData.rules.constantType name = some type) :
    rules.constantType name = some type := by
  have typed : NativeWireData.signature.typeOf? name = some type := known
  obtain ⟨entry, entryKnown, _⟩ := Option.map_eq_some_iff.mp typed
  exact combinedType_of_signature IntrinsicRelator.rules NativeWireData.signature
    (wire_declarations_fresh entryKnown) typed

theorem wire_root_empty {left right : Tower.Tm n}
    (root : NativeWireData.rules.computation.step left right) : False := by
  cases root with
  | inherited impossible => exact impossible.elim
  | delta lookup => rw [wire_values_opaque] at lookup; cases lookup
  | declared impossible => exact impossible.elim

/-- Opaque wire data introduces no computation generator. -/
theorem root_iff {left right : Tower.Tm n} :
    rules.computation.step left right ↔ IntrinsicRelator.rules.computation.step left right := by
  constructor
  · intro root
    cases root with
    | inherited root => exact root
    | delta lookup => rw [wire_values_opaque] at lookup; cases lookup
    | declared impossible => exact impossible.elim
  · exact RootStep.inherited

theorem wire_requirements (requirement : Requirement Tower.Head) :
    requirement.Holds NativeWireData.rules → requirement.Holds rules := by
  intro valid
  cases requirement with
  | constantType name type => exact wire_constant_preserved valid
  | rootStep k left right => exact (wire_root_empty valid).elim
  | _ => exact valid

theorem relator_requirements (requirement : Requirement Tower.Head) :
    requirement.Holds IntrinsicRelator.rules → requirement.Holds rules := by
  intro valid
  cases requirement with
  | constantType name type =>
      exact combinedType_of_base IntrinsicRelator.rules NativeWireData.signature valid
  | rootStep k left right => exact root_iff.mpr valid
  | _ => exact valid

theorem wire_typing {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing NativeWireData.rules context term type) : Typing rules context term type :=
  typing_transfer wire_requirements typed

theorem relator_typing {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing IntrinsicRelator.rules context term type) : Typing rules context term type :=
  typed.includeSignature NativeWireData.signature

theorem wire_judgment {context : Tower.Ctx n} {term type : Tower.Tm n}
    (admitted : Judgment NativeWireData.rules context term type) :
    Judgment rules context term type :=
  judgment_transfer wire_requirements admitted

theorem relator_judgment {context : Tower.Ctx n} {term type : Tower.Tm n}
    (admitted : Judgment IntrinsicRelator.rules context term type) :
    Judgment rules context term type :=
  judgment_transfer relator_requirements admitted

/-- Equality of the actual one-step relations is proved from opacity;
it is not inferred merely from either package inclusion. -/
theorem step_iff {left right : Tower.Tm n} :
    Step rules.headEq left right rules.computation ↔
      Step IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation := by
  constructor
  · intro step
    simpa only [Tm.mapHead_id] using step.mapHead
      (targetEq := IntrinsicRelator.rules.headEq) (fun head => head) (fun equal => equal)
      (by intro k a b root; simpa only [Tm.mapHead_id] using root_iff.mp root)
  · exact StepCore.includeSignature IntrinsicRelator.rules NativeWireData.signature

theorem conversion_iff {left right : Tower.Tm n} :
    Conv rules.headEq left right rules.computation ↔
      Conv IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation := by
  constructor
  · intro conversion
    simpa only [Tm.mapHead_id] using conversion.mapHead
      (targetEq := IntrinsicRelator.rules.headEq) (fun head => head) (fun equal => equal)
      (by intro k a b root; simpa only [Tm.mapHead_id] using root_iff.mp root)
  · exact Conv.includeSignature IntrinsicRelator.rules NativeWireData.signature

/-- The original checker is still exact for the unchanged forward relation.
This statement checks steps, not formation of their source or target. -/
theorem checked_step_iff {left right : Tower.Tm n} :
    Step rules.headEq left right rules.computation ↔
      ∃ code, NativeRelatorConversionChecking.checkStep code left right = true := by
  exact step_iff.trans NativeRelatorConversionChecking.step_iff_checked

theorem checked_conversion_iff {left right : Tower.Tm n} :
    Conv rules.headEq left right rules.computation ↔
      ∃ code, NativeRelatorConversionChecking.check code left right = true :=
  conversion_iff.trans NativeRelatorConversionChecking.conversion_iff_checked

/-- Checked conversion is available for newly admitted combined judgments,
but still requires independent formation of the new displayed type. -/
theorem convert_checked {context : Tower.Ctx n}
    {term sourceType targetType : Tower.Tm n} {level : Tower.Head}
    (source : Judgment rules context term sourceType)
    (target : Typing rules context targetType (.head level))
    (universeWitness : rules.isUniverse level)
    {code : NativeRelatorConversionChecking.Code n}
    (checked : NativeRelatorConversionChecking.check code sourceType targetType = true) :
    Judgment rules context term targetType :=
  ⟨source.context, .conv source.typing target universeWitness
    (checked_conversion_iff.mpr ⟨code, checked⟩)⟩

/-- Original source admission suffices to reuse the original preservation
theorem, then embed its target judgment in the common package. -/
theorem embedded_checked_step_preserves {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (admitted : Judgment IntrinsicRelator.rules context source type)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    Judgment rules context target type :=
  relator_judgment
    (FormationSensitiveNativeRelatorQualification.checkedStep_preserves admitted checked)


/-! ## Formation and the unchanged service primitives -/

theorem dataType_formed (context : Tower.Ctx n) :
    Typing rules context NativeWireData.dataType (sortTm Tower.zero) :=
  wire_typing (NativeWireData.dataType_formed context)

theorem encode_typed (context : Tower.Ctx n) (wire : NativeWireData.Wire) :
    Typing rules context (NativeWireData.encode wire) NativeWireData.dataType :=
  wire_typing (NativeWireData.encode_typing context wire)

private theorem binaryType_formed : Typing rules .nil NativeWireData.binaryType
    (sortTm (.max Tower.zero (.max Tower.zero Tower.zero))) :=
  .piForm (dataType_formed _) (.sort _)
    (.piForm (dataType_formed _) (.sort _) (dataType_formed _) (.sort _) (.sorts _ _))
    (.sort _) (.sorts _ _)

private theorem wire_binary_typing {context : Tower.Ctx n} {name : DeclName}
    (known : NativeWireData.rules.constantType name = some NativeWireData.binaryType)
    {left right : Tower.Tm n}
    (first : Typing rules context left NativeWireData.dataType)
    (second : Typing rules context right NativeWireData.dataType) :
    Typing rules context (.app (.app (.const name) left) right) NativeWireData.dataType := by
  have symbol : Typing rules context (.const name) NativeWireData.binaryType :=
    .const (wire_constant_preserved known) binaryType_formed (.sort _)
  exact .appElim (.appElim symbol first) second

theorem operation_formation {Operation : Type}
    {signature : ScopedComputation.OperationSignature Tower.Head Operation}
    {operation : Operation}
    (formed : ScopedComputation.OperationFormation NativeWireData.rules signature operation) :
    ScopedComputation.OperationFormation rules signature operation := by
  obtain ⟨⟨inputLevel, inputUniverse, inputTyped⟩,
    ⟨outputLevel, outputUniverse, outputTyped⟩⟩ := formed
  exact ⟨⟨inputLevel, inputUniverse, wire_typing inputTyped⟩,
    ⟨outputLevel, outputUniverse, wire_typing outputTyped⟩⟩

open NeedReference Presentation.PolarizedNeed Presentation.PolarizedNeedMachine

theorem matched_operation_formed (operation : PolarizedNeedMatchedIndex.Operation) :
    ScopedComputation.OperationFormation rules PolarizedNeedMatchedIndex.signature operation :=
  operation_formation (PolarizedNeedMatchedIndex.operation_formed operation)

theorem nativeProof_operation_formed :
    ScopedComputation.OperationFormation rules PolarizedNeedNativeProofService.signature () :=
  operation_formation PolarizedNeedNativeProofService.operation_formed

/-- This proof accepts arguments admitted by the combined package. It does
not assume that every new argument was already admitted by the wire package. -/
theorem matched_primitive_sound (context : Tower.Ctx n) :
    PrimitiveSoundness rules PolarizedNeedMatchedIndex.signature context
      PolarizedNeedMatchedIndex.primitive := by
  intro operation argument value _ _ produced
  cases operation <;>
    simp only [PolarizedNeedMatchedIndex.primitive, Produced.value.injEq] at produced <;>
    cases produced <;> exact encode_typed context _

theorem nativeProof_primitive_sound
    (environment : Mettapedia.Languages.Megalodon.MathdataKernel.Environment)
    (current : PolarizedNeedNativeProofWire.Scope)
    (expected : PolarizedNeedNativeProofWire.Request) (context : Tower.Ctx n) :
    PrimitiveSoundness rules PolarizedNeedNativeProofService.signature context
      (PolarizedNeedNativeProofService.primitive environment current expected) := by
  intro operation argument value _ _ produced
  cases operation
  simp only [PolarizedNeedNativeProofService.primitive, Produced.value.injEq] at produced
  cases produced
  exact encode_typed context _

theorem matched_consume_argument_typed {context : Tower.Ctx n}
    (expected : PolarizedNeedMatchedIndex.Request) {reply : Tower.Tm n}
    (typed : Typing rules context reply NativeWireData.dataType) :
    Typing rules context (PolarizedNeedMatchedIndex.consumeArgument expected reply)
      NativeWireData.dataType :=
  wire_binary_typing (by decide) (encode_typed context _)
    (wire_binary_typing (by decide) (encode_typed context _)
      (wire_binary_typing (by decide) typed (wire_typing (NativeWireData.nil_typing context))))

/-- The actual two-call source, including its native binder, is admitted
under the common rules without changing the authored operation signature. -/
theorem matched_source_typed {v k : Nat} {Effect : Type} (context : Tower.Ctx n)
    (values : Fin v → VTy Tower.Head n) (needs : Fin k → CTy Tower.Head n)
    (expected actual : PolarizedNeedMatchedIndex.Request) :
    ComputationTyping rules PolarizedNeedMatchedIndex.signature context values needs
      (PolarizedNeedMatchedIndex.source (Effect := Effect) expected actual)
      (.returns (.native NativeWireData.dataType)) := by
  apply ComputationTyping.bindNative
    ⟨.sort Tower.zero, Tower.IsUniverse.sort _, dataType_formed context⟩
    (.returns (.native ⟨.sort Tower.zero, Tower.IsUniverse.sort _, dataType_formed context⟩))
  · exact .call (matched_operation_formed .select) (encode_typed context _)
  · exact .call (matched_operation_formed .consume) (matched_consume_argument_typed expected (.var 0))

theorem nativeProof_source_typed {v k : Nat} {Effect : Type} (context : Tower.Ctx n)
    (values : Fin v → VTy Tower.Head n) (needs : Fin k → CTy Tower.Head n)
    (input : NativeWireData.Wire) :
    ComputationTyping rules PolarizedNeedNativeProofService.signature context values needs
      (PolarizedNeedNativeProofService.source (Effect := Effect) input)
      (.returns (.native NativeWireData.dataType)) := by
  have formed : ComputationFormation rules context (.returns (.native NativeWireData.dataType)) :=
    .returns (.native ⟨.sort Tower.zero, .sort _, dataType_formed context⟩)
  exact .letNeed formed formed
    (.call nativeProof_operation_formed (encode_typed context input)) (.forceNeed 0)

/-! ## Genuine mixed native terms and substituted J schemas -/

private theorem dataType_at_elementLevel (context : Tower.Ctx n) :
    Typing rules context NativeWireData.dataType (sortTm Intrinsic.elementLevel) :=
  .cumul (dataType_formed context) (fun _ => Nat.zero_le _)

theorem list_data_formed (context : Tower.Ctx n) :
    Typing rules context (Intrinsic.listApp NativeWireData.dataType)
      (sortTm Intrinsic.elementLevel) := by
  have applied := Typing.appElim
    (relator_typing (FormationSensitiveNativeList.listConstant_hasType (context := context)))
    (dataType_at_elementLevel context)
  simpa [Intrinsic.listType, Intrinsic.listApp, liftClosed, sortTm,
    rename, inst0, subst] using applied

private theorem nil_data_typed (context : Tower.Ctx n) :
    Typing rules context (Intrinsic.nilApp NativeWireData.dataType)
      (Intrinsic.listApp NativeWireData.dataType) := by
  have applied := Typing.appElim
    (relator_typing (FormationSensitiveNativeList.nilConstant_hasType (context := context)))
    (dataType_at_elementLevel context)
  simpa [Intrinsic.nilType, Intrinsic.nilApp, Intrinsic.listApp, liftClosed, sortTm,
    rename, inst0, subst, subst0, liftRen, liftSub] using applied

/-- The native List constructor stores the original encoded wire as its
actual head. This is a native List of Data, not the Data encoding of a List. -/
def singleton (wire : NativeWireData.Wire) : Tower.Tm n :=
  Intrinsic.consApp NativeWireData.dataType (NativeWireData.encode wire)
    (Intrinsic.nilApp NativeWireData.dataType)

theorem singleton_typed (context : Tower.Ctx n) (wire : NativeWireData.Wire) :
    Typing rules context (singleton wire) (Intrinsic.listApp NativeWireData.dataType) := by
  have bodyAsArrows : Intrinsic.consBodyType =
      SchemaElaboration.arrow (.var 0)
        (SchemaElaboration.arrow (Intrinsic.listApp (.var 0))
          (Intrinsic.listApp (.var 0))) := by decide
  have first := Typing.appElim
    (relator_typing (FormationSensitiveNativeList.consConstant_hasType (context := context)))
    (dataType_at_elementLevel context)
  have firstTyped : Typing rules context
      (.app (.const Intrinsic.consName) NativeWireData.dataType)
      (SchemaElaboration.arrow NativeWireData.dataType
        (SchemaElaboration.arrow (Intrinsic.listApp NativeWireData.dataType)
          (Intrinsic.listApp NativeWireData.dataType))) := by
    simpa [Intrinsic.consType, bodyAsArrows, liftClosed, inst0, subst0] using first
  exact .appElim (.appElim firstTyped (encode_typed context wire)) (nil_data_typed context)

theorem singleton_judgment (wire : NativeWireData.Wire) :
    Judgment rules .nil (singleton wire) (Intrinsic.listApp NativeWireData.dataType) :=
  ⟨.nil, singleton_typed .nil wire⟩

/-- The existing J schema may be instantiated by independently typed
substitutions in the combined environment, including its new Data terms.
The substitution premise supplies arguments, not a desired output judgment. -/
theorem identity_schema_substitute {context : Tower.Ctx n}
    {substitution : Sub Tower.Head 4 n} (formed : ContextFormation rules context)
    (typed : FormationSensitive.CtxMor rules Intrinsic.contextAXPD context substitution) :
    Judgment rules context (subst substitution Intrinsic.identityIotaLeft)
        (subst substitution Intrinsic.identityIotaResultType) ∧
      Judgment rules context (subst substitution Intrinsic.identityIotaRight)
        (subst substitution Intrinsic.identityIotaResultType) :=
  ⟨(relator_judgment FormationSensitiveNativeIdentity.identityIota_judgments.1).substitute formed typed,
    (relator_judgment FormationSensitiveNativeIdentity.identityIota_judgments.2).substitute formed typed⟩

theorem identity_schema_root (substitution : Sub Tower.Head 4 n) :
    rules.computation.step (subst substitution Intrinsic.identityIotaLeft)
      (subst substitution Intrinsic.identityIotaRight) :=
  root_iff.mpr (FormationSensitiveNativeIdentity.identityIota_substitutedRoot substitution)

/-! ## Conversion separation and non-interchangeability -/

theorem pi_conversion_boundary : PiConversionBoundary rules where
  components := by
    intro k A A' B B' conversion
    obtain ⟨domain, codomain⟩ :=
      NativeRelatorConversionParallel.nativePiConversionBoundary.components (conversion_iff.mp conversion)
    exact ⟨conversion_iff.mpr domain, conversion_iff.mpr codomain⟩
  headDisjoint := fun conversion =>
    NativeRelatorConversionParallel.nativePiConversionBoundary.headDisjoint (conversion_iff.mp conversion)

theorem sigma_conversion_boundary : SigmaConversionBoundary rules where
  components := by
    intro k A A' B B' conversion
    obtain ⟨domain, codomain⟩ :=
      NativeRelatorConversionParallel.nativeSigmaConversionBoundary.components (conversion_iff.mp conversion)
    exact ⟨conversion_iff.mpr domain, conversion_iff.mpr codomain⟩
  headDisjoint := fun conversion =>
    NativeRelatorConversionParallel.nativeSigmaConversionBoundary.headDisjoint (conversion_iff.mp conversion)

private theorem parStar_const_eq {name : DeclName} {target : Tower.Tm n}
    (steps : NativeRelatorConversionParallel.ParStar (.const name) target) :
    target = .const name := by
  induction steps with
  | refl => rfl
  | tail previous finalStep ih =>
      rw [ih] at finalStep
      cases finalStep
      rfl

private theorem parStar_id_shape {type left right target : Tower.Tm n}
    (steps : NativeRelatorConversionParallel.ParStar (.id type left right) target) :
    ∃ type' left' right', target = .id type' left' right' := by
  induction steps with
  | refl => exact ⟨_, _, _, rfl⟩
  | tail previous finalStep ih =>
      obtain ⟨_, _, _, rfl⟩ := ih
      cases finalStep with
      | id first second third => exact ⟨_, _, _, rfl⟩

theorem constant_head_disjoint (name : DeclName) (head : Tower.Head) :
    ¬ Conv rules.headEq (.const name : Tower.Tm n) (.head head) rules.computation := by
  intro conversion
  obtain ⟨common, constSteps, headSteps⟩ :=
    NativeRelatorConversionParallel.conversion_join (conversion_iff.mp conversion)
  have constantShape := parStar_const_eq constSteps
  obtain ⟨_, headShape⟩ := NativeRelatorConversionParallel.parStar_head_shape headSteps
  rw [constantShape] at headShape
  cases headShape

theorem constant_identity_disjoint (name : DeclName) (type left right : Tower.Tm n) :
    ¬ Conv rules.headEq (.const name) (.id type left right) rules.computation := by
  intro conversion
  obtain ⟨common, constSteps, identitySteps⟩ :=
    NativeRelatorConversionParallel.conversion_join (conversion_iff.mp conversion)
  have constantShape := parStar_const_eq constSteps
  obtain ⟨_, _, _, identityShape⟩ := parStar_id_shape identitySteps
  rw [constantShape] at identityShape
  cases identityShape

private theorem encode_spine (context : Tower.Ctx n) (wire : NativeWireData.Wire) :
    FormationSensitive.DeclarationSpine rules context (NativeWireData.encode wire)
      NativeWireData.dataType := by
  cases wire with
  | symbol value =>
      simp only [NativeWireData.encode]
      apply FormationSensitive.DeclarationSpine.constant
        (wire_constant_preserved ?_) (dataType_formed .nil) (.sort Tower.zero)
      simp [NativeWireData.rules, extendRules, combinedType, Tower.rules, Signature.typeOf?,
        NativeWireData.signature, NativeWireData.dataName, NativeWireData.applicationName,
        NativeWireData.consName, NativeWireData.nilName, NativeWireData.symbolPrefix,
        NativeWireData.stringPrefix]
  | string value =>
      simp only [NativeWireData.encode]
      apply FormationSensitive.DeclarationSpine.constant
        (wire_constant_preserved ?_) (dataType_formed .nil) (.sort Tower.zero)
      simp [NativeWireData.rules, extendRules, combinedType, Tower.rules, Signature.typeOf?,
        NativeWireData.signature, NativeWireData.dataName, NativeWireData.applicationName,
        NativeWireData.consName, NativeWireData.nilName, NativeWireData.symbolPrefix,
        NativeWireData.stringPrefix]
  | natural value =>
      simp only [NativeWireData.encode]
      apply FormationSensitive.DeclarationSpine.constant
        (wire_constant_preserved ?_) (dataType_formed .nil) (.sort Tower.zero)
      simp [NativeWireData.rules, extendRules, combinedType, Tower.rules, Signature.typeOf?,
        NativeWireData.signature, NativeWireData.dataName, NativeWireData.applicationName,
        NativeWireData.consName, NativeWireData.nilName, NativeWireData.naturalPrefix]
  | application head arguments =>
      simp only [NativeWireData.encode]
      have symbol : FormationSensitive.DeclarationSpine rules context
          (.const NativeWireData.applicationName) NativeWireData.binaryType :=
        .constant (wire_constant_preserved (by decide)) binaryType_formed (.sort _)
      have spine := FormationSensitive.DeclarationSpine.app
        (.app symbol (encode_typed context (.symbol head)))
        (wire_typing (NativeWireData.encodeList_typing context arguments))
      simpa only [NativeWireData.encode, NativeWireData.dataType, inst0, subst] using spine

/-- Every original wire encoding has principal type Data. No encoded receipt
is itself a native identity inhabitant, even when that identity is inhabited. -/
theorem encoded_wire_not_identity {context : Tower.Ctx n} (wire : NativeWireData.Wire)
    (type left right : Tower.Tm n) :
    ¬ Typing rules context (NativeWireData.encode wire) (.id type left right) := by
  intro typed
  have adjustment := (encode_spine context wire).adjustment pi_conversion_boundary typed
  have conversion := adjustment.toConvOfSourceDisjointHeads
    (constant_head_disjoint NativeWireData.dataName)
  exact constant_identity_disjoint NativeWireData.dataName type left right conversion

/-- The negative distinction is nonvacuous: the corresponding reflexive
identity has its ordinary formed native witness, with the wire value retained. -/
theorem data_reflexivity_judgment (wire : NativeWireData.Wire) :
    Judgment rules .nil (.refl (NativeWireData.encode wire))
      (.id NativeWireData.dataType (NativeWireData.encode wire) (NativeWireData.encode wire)) :=
  ⟨.nil, .reflIntro (encode_typed .nil wire)⟩

theorem relator_alone_rejects_data {context : Tower.Ctx n} (type : Tower.Tm n) :
    ¬ Typing IntrinsicRelator.rules context NativeWireData.dataType type := by
  intro typed
  obtain ⟨_, _, lookup, _, _⟩ := typed.constFormation
  have absent : IntrinsicRelator.rules.constantType NativeWireData.dataName = none := by decide
  rw [absent] at lookup
  cases lookup

theorem wire_alone_rejects_list {context : Tower.Ctx n} (type : Tower.Tm n) :
    ¬ Typing NativeWireData.rules context (.const Intrinsic.listName) type := by
  intro typed
  obtain ⟨_, _, lookup, _, _⟩ := typed.constFormation
  have absent : NativeWireData.rules.constantType Intrinsic.listName = none := by decide
  rw [absent] at lookup
  cases lookup

theorem wire_alone_rejects_J {context : Tower.Ctx n} (type : Tower.Tm n) :
    ¬ Typing NativeWireData.rules context (.const Intrinsic.identityEliminateName) type := by
  intro typed
  obtain ⟨_, _, lookup, _, _⟩ := typed.constFormation
  have absent : NativeWireData.rules.constantType Intrinsic.identityEliminateName = none := by decide
  rw [absent] at lookup
  cases lookup

#print axioms matched_primitive_sound
#print axioms nativeProof_primitive_sound
#print axioms matched_source_typed
#print axioms nativeProof_source_typed
#print axioms singleton_judgment
#print axioms identity_schema_substitute
#print axioms identity_schema_root
#print axioms encoded_wire_not_identity
#print axioms data_reflexivity_judgment
#print axioms relator_alone_rejects_data
#print axioms wire_alone_rejects_list
#print axioms wire_alone_rejects_J


#print axioms wire_declarations_fresh
#print axioms wire_judgment
#print axioms relator_judgment
#print axioms step_iff
#print axioms conversion_iff
#print axioms checked_step_iff
#print axioms checked_conversion_iff
#print axioms convert_checked
#print axioms pi_conversion_boundary
#print axioms sigma_conversion_boundary
#print axioms embedded_checked_step_preserves

end NativeWireRelatorCompatibility
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
