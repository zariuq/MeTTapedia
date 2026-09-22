import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorCompatibility
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartNIKService

/-!
# Retained HOL, wire data and native List/J/relator in one rules environment

The actual uniform-list HOL declarations and opaque wire-data declarations
share the existing native List/J/relator environment. Freshness preserves
both declaration interfaces; opacity allows the generic preservation and
exact conversion-checking theorems to apply to newly admitted mixed terms.

The abstract HOL sequence carrier is not native List Data. Source HOL proof
admission is the existing intrinsic service, not a native dependent proof
inhabitant of the separately represented proposition. No mathematical host,
identity policy or candidate is selected by this compatibility construction.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeRelatorCompatibility

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.FormationSensitive (Typing Judgment ContextFormation)
open Presentation.FormationSensitive.Dependencies

variable {n : Nat}

/-- The retained HOL entries precede the wire entries. The freshness theorem
below proves that this choice does not shadow either actual interface. -/
def signature : Signature Tower.Head where
  entries name := (FormationSensitiveHOLUniformList.declarations.entries name).orElse
    (fun _ => NativeWireData.signature.entries name)

def rules : Rules Tower.Head := OpaqueRelatorExtension.rules signature

private theorem ofList_entry_mem {declarations : List (DeclName × Entry Tower.Head)}
    {name : DeclName} {entry : Entry Tower.Head}
    (known : (Signature.ofList declarations).entries name = some entry) :
    (name, entry) ∈ declarations := by
  induction declarations with
  | nil => cases known
  | cons declaration declarations ih =>
      change (if name = declaration.1 then some declaration.2
        else (Signature.ofList declarations).entries name) = some entry at known
      split at known
      · rename_i same
        exact List.mem_cons.mpr (.inl (Prod.ext same (Option.some.inj known).symm))
      · exact List.mem_cons_of_mem _ (ih known)

private theorem ofList_values_none (declarations : List (DeclName × Entry Tower.Head))
    (allOpaque : ∀ declaration ∈ declarations, declaration.2.value? = none) (name : DeclName) :
    (Signature.ofList declarations).valueOf? name = none := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
      change (if name = declaration.1 then some declaration.2
        else (Signature.ofList declarations).entries name).bind Entry.value? = none
      split
      · exact allOpaque declaration List.mem_cons_self
      · exact ih (fun other member => allOpaque other (List.mem_cons_of_mem _ member))

theorem hol_entry_fresh {name : DeclName} {entry : Entry Tower.Head}
    (known : FormationSensitiveHOLUniformList.declarations.entries name = some entry) :
    NativeWireData.signature.entries name = none ∧
      IntrinsicRelator.rules.constantType name = none := by
  have member := ofList_entry_mem known
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

theorem hol_values_opaque (name : DeclName) :
    FormationSensitiveHOLUniformList.declarations.valueOf? name = none := by
  apply ofList_values_none
  intro declaration member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> rfl

theorem signature_extends_hol :
    FormationSensitiveHOLUniformList.declarations.Extends signature where
  entries := by
    intro name entry known
    simp [signature, known]
  computation := by intro n left right impossible; exact impossible.elim

theorem signature_extends_wire : NativeWireData.signature.Extends signature where
  entries := by
    intro name entry known
    cases hol : FormationSensitiveHOLUniformList.declarations.entries name with
    | none => simp [signature, hol, known]
    | some prior =>
        rw [(hol_entry_fresh hol).1] at known
        cases known
  computation := by intro n left right impossible; exact impossible.elim

theorem opacity : OpaqueRelatorExtension.Opacity signature where
  values := by
    intro name
    cases hol : FormationSensitiveHOLUniformList.declarations.entries name with
    | none =>
        simpa [Signature.valueOf?, signature, hol] using
          NativeWireRelatorCompatibility.wire_values_opaque name
    | some entry =>
        simpa [Signature.valueOf?, signature, hol] using hol_values_opaque name
  roots := by intro n left right impossible; exact impossible.elim

theorem hol_constant_preserved {name : DeclName} {type : Tower.Tm 0}
    (known : FormationSensitiveHOLUniformList.rules.constantType name = some type) :
    rules.constantType name = some type := by
  have typed : FormationSensitiveHOLUniformList.declarations.typeOf? name = some type := known
  obtain ⟨entry, entryKnown, _⟩ := Option.map_eq_some_iff.mp typed
  exact combinedType_of_signature IntrinsicRelator.rules signature
    (hol_entry_fresh entryKnown).2 (signature_extends_hol.typeOf typed)

theorem wire_relator_constant_preserved {name : DeclName} {type : Tower.Tm 0}
    (known : NativeWireRelatorCompatibility.rules.constantType name = some type) :
    rules.constantType name = some type :=
  signature_extends_wire.preservesCombinedType IntrinsicRelator.rules known

private theorem hol_root_empty {left right : Tower.Tm n}
    (root : FormationSensitiveHOLUniformList.rules.computation.step left right) : False := by
  cases root with
  | inherited impossible => exact impossible.elim
  | delta known => rw [hol_values_opaque] at known; cases known
  | declared impossible => exact impossible.elim

theorem hol_requirements (requirement : Requirement Tower.Head) :
    requirement.Holds FormationSensitiveHOLUniformList.rules → requirement.Holds rules := by
  intro valid
  cases requirement with
  | constantType name type => exact hol_constant_preserved valid
  | rootStep k left right => exact (hol_root_empty valid).elim
  | _ => exact valid

theorem wire_relator_requirements (requirement : Requirement Tower.Head) :
    requirement.Holds NativeWireRelatorCompatibility.rules → requirement.Holds rules := by
  intro valid
  cases requirement with
  | constantType name type => exact wire_relator_constant_preserved valid
  | rootStep k left right =>
      exact (OpaqueRelatorExtension.root_iff opacity).mpr
        (NativeWireRelatorCompatibility.root_iff.mp valid)
  | _ => exact valid

theorem hol_typing {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing FormationSensitiveHOLUniformList.rules context term type) :
    Typing rules context term type := typing_transfer hol_requirements typed

theorem hol_judgment {context : Tower.Ctx n} {term type : Tower.Tm n}
    (admitted : Judgment FormationSensitiveHOLUniformList.rules context term type) :
    Judgment rules context term type := judgment_transfer hol_requirements admitted

theorem wire_relator_typing {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing NativeWireRelatorCompatibility.rules context term type) :
    Typing rules context term type := typing_transfer wire_relator_requirements typed

theorem wire_relator_judgment {context : Tower.Ctx n} {term type : Tower.Tm n}
    (admitted : Judgment NativeWireRelatorCompatibility.rules context term type) :
    Judgment rules context term type := judgment_transfer wire_relator_requirements admitted

theorem wire_typing {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing NativeWireData.rules context term type) : Typing rules context term type :=
  wire_relator_typing (NativeWireRelatorCompatibility.wire_typing typed)

theorem relator_typing {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing IntrinsicRelator.rules context term type) : Typing rules context term type :=
  OpaqueRelatorExtension.relator_typing typed

theorem relator_judgment {context : Tower.Ctx n} {term type : Tower.Tm n}
    (admitted : Judgment IntrinsicRelator.rules context term type) :
    Judgment rules context term type :=
  wire_relator_judgment (NativeWireRelatorCompatibility.relator_judgment admitted)

/-! ## Qualification applies to every common-admitted source -/

theorem checked_conversion_iff {left right : Tower.Tm n} :
    Conv rules.headEq left right rules.computation ↔
      ∃ code, NativeRelatorConversionChecking.check code left right = true :=
  OpaqueRelatorExtension.checked_conversion_iff opacity

theorem root_preservation : FormationSensitive.RootPreservation rules :=
  OpaqueRelatorExtension.root_preservation opacity

theorem step_preserves {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment rules context source type)
    (step : Step rules.headEq source target rules.computation) :
    Judgment rules context target type :=
  OpaqueRelatorExtension.step_preserves opacity admitted step

theorem checked_step_preserves {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment rules context source type)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    Judgment rules context target type :=
  OpaqueRelatorExtension.checked_step_preserves opacity admitted checked

/-! ## A native List of abstract HOL sequences, paired with actual wire data -/

def holSequenceType : Tower.Tm n := .const `HOLUniformList.sequence

theorem hol_sequence_formed (context : Tower.Ctx n) :
    Typing rules context holSequenceType (sortTm Tower.zero) :=
  hol_typing (FormationSensitiveHOLUniformList.simple_type_formed
    Logic.HOL.UniformListInduction.sequence context)

theorem hol_nil_typed (context : Tower.Ctx n) :
    Typing rules context FormationSensitiveHOLUniformList.rawNil holSequenceType :=
  .const (hol_constant_preserved (by decide)) (hol_sequence_formed .nil) (.sort Tower.zero)

private theorem hol_sequence_at_elementLevel (context : Tower.Ctx n) :
    Typing rules context holSequenceType (sortTm Intrinsic.elementLevel) :=
  .cumul (hol_sequence_formed context) (fun _ => Nat.zero_le _)

theorem list_hol_sequence_formed (context : Tower.Ctx n) :
    Typing rules context (Intrinsic.listApp holSequenceType)
      (sortTm Intrinsic.elementLevel) := by
  have applied := Typing.appElim
    (relator_typing (FormationSensitiveNativeList.listConstant_hasType (context := context)))
    (hol_sequence_at_elementLevel context)
  simpa [Intrinsic.listType, Intrinsic.listApp, liftClosed, sortTm,
    rename, inst0, subst] using applied

private theorem native_nil_hol_sequence_typed (context : Tower.Ctx n) :
    Typing rules context (Intrinsic.nilApp holSequenceType)
      (Intrinsic.listApp holSequenceType) := by
  have applied := Typing.appElim
    (relator_typing (FormationSensitiveNativeList.nilConstant_hasType (context := context)))
    (hol_sequence_at_elementLevel context)
  simpa [Intrinsic.nilType, Intrinsic.nilApp, Intrinsic.listApp, liftClosed, sortTm,
    rename, inst0, subst, subst0, liftRen, liftSub] using applied

/-- This native singleton stores the abstract HOL nil as its head. Neither
its native List carrier nor its HOL sequence element is the wire Data type. -/
def holSequenceSingleton : Tower.Tm n :=
  Intrinsic.consApp holSequenceType FormationSensitiveHOLUniformList.rawNil
    (Intrinsic.nilApp holSequenceType)

theorem hol_sequence_singleton_typed (context : Tower.Ctx n) :
    Typing rules context holSequenceSingleton (Intrinsic.listApp holSequenceType) := by
  have bodyAsArrows : Intrinsic.consBodyType =
      SchemaElaboration.arrow (.var 0)
        (SchemaElaboration.arrow (Intrinsic.listApp (.var 0))
          (Intrinsic.listApp (.var 0))) := by decide
  have first := Typing.appElim
    (relator_typing (FormationSensitiveNativeList.consConstant_hasType (context := context)))
    (hol_sequence_at_elementLevel context)
  have firstTyped : Typing rules context (.app (.const Intrinsic.consName) holSequenceType)
      (SchemaElaboration.arrow holSequenceType
        (SchemaElaboration.arrow (Intrinsic.listApp holSequenceType)
          (Intrinsic.listApp holSequenceType))) := by
    simpa [Intrinsic.consType, bodyAsArrows, liftClosed, inst0, subst0] using first
  exact .appElim (.appElim firstTyped (hol_nil_typed context))
    (native_nil_hol_sequence_typed context)

def mixedPayload (wire : NativeWireData.Wire) : Tower.Tm n :=
  .pair holSequenceSingleton (NativeWireData.encode wire)

def mixedPayloadType : Tower.Tm n :=
  .sigma (Intrinsic.listApp holSequenceType) NativeWireData.dataType

theorem mixed_payload_type_formed (context : Tower.Ctx n) :
    Typing rules context mixedPayloadType (sortTm (.max Intrinsic.elementLevel Tower.zero)) :=
  .sigmaForm (list_hol_sequence_formed context) (.sort _)
    (wire_typing (NativeWireData.dataType_formed _)) (.sort _) (.sorts _ _)

theorem mixed_payload_typed (context : Tower.Ctx n) (wire : NativeWireData.Wire) :
    Typing rules context (mixedPayload wire) mixedPayloadType :=
  .pairIntro (mixed_payload_type_formed context) (.sort _)
    (hol_sequence_singleton_typed context) (wire_typing (NativeWireData.encode_typing context wire))

theorem mixed_payload_judgment (wire : NativeWireData.Wire) :
    Judgment rules .nil (mixedPayload wire) mixedPayloadType :=
  ⟨.nil, mixed_payload_typed .nil wire⟩

theorem mixed_projection_checked (wire : NativeWireData.Wire) :
    NativeRelatorConversionChecking.checkStep
      (.betaSigmaSnd holSequenceSingleton (NativeWireData.encode wire))
      (.snd (mixedPayload (n := n) wire)) (NativeWireData.encode wire) = true := by
  simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
    StructuralConversionCode.StepCode.decode, mixedPayload]

/-- The existing checker and generic opaque-extension preservation operate
on this newly admitted mixed source, with no old-package typing premise. -/
theorem mixed_projection_admitted (wire : NativeWireData.Wire) :
    Judgment rules .nil (NativeWireData.encode wire) NativeWireData.dataType :=
  checked_step_preserves
    ⟨.nil, Typing.sndElim (mixed_payload_typed .nil wire)⟩ (mixed_projection_checked wire)

theorem hol_sequence_distinct_from_native_list_data :
    (holSequenceType : Tower.Tm n) ≠ Intrinsic.listApp NativeWireData.dataType := by
  intro equality
  cases equality

/-! ## The unchanged source-proof service in the common formed context -/

open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
  UniformListChartNIKService in
/-- The accepted source claim is unchanged. Only its separately formed
representation is embedded into the shared List/J/relator/wire environment. -/
theorem produced_source_admission_and_common_formation
    (gamma : Logic.HOL.Ctx Logic.HOL.UniformListInduction.BaseSort)
    (request : ReplayRequest gamma) (proof : (intrinsicProofSystem gamma).ProofObject)
    (produced : produce? gamma request = some proof) :
    (intrinsicKernel gamma).decide request.claim proof = true ∧
      Logic.HOL.ExtDerivation Logic.HOL.UniformListInduction.Symbol request.claim.1 request.claim.2 ∧
      represent FormationSensitiveHOLUniformList.signature request.claim.2 = some rawMapLength ∧
      request.claim.1.map (represent FormationSensitiveHOLUniformList.signature) =
        (rawTheory (n := gamma.length)).map some ∧
      Judgment rules (context types gamma) rawMapLength (.const `HOLUniformList.prop) ∧
      (∀ formula ∈ rawTheory (n := gamma.length),
        Judgment rules (context types gamma) formula (.const `HOLUniformList.prop)) := by
  obtain ⟨accepted, derivation, represented, assumptions, conclusionFormed, premisesFormed⟩ :=
    produced_admission_and_representation gamma request proof produced
  exact ⟨accepted, derivation, represented, assumptions, hol_judgment conclusionFormed,
    fun formula member => hol_judgment (premisesFormed formula member)⟩

open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
  UniformListChartNIKService Logic.HOL.UniformListInduction in
theorem actual_source_admission_and_common_formation (gamma : Logic.HOL.Ctx BaseSort) :
    (intrinsicKernel gamma).decide (mapLengthClaim gamma) (actualNativeProof gamma) = true ∧
      Logic.HOL.ExtDerivation Symbol (theory (Γ := gamma)) mapLength ∧
      represent FormationSensitiveHOLUniformList.signature (mapLength (Γ := gamma)) =
        some rawMapLength ∧
      (theory (Γ := gamma)).map (represent FormationSensitiveHOLUniformList.signature) =
        (rawTheory (n := gamma.length)).map some ∧
      Judgment rules (context types gamma) rawMapLength (.const `HOLUniformList.prop) ∧
      (∀ formula ∈ rawTheory (n := gamma.length),
        Judgment rules (context types gamma) formula (.const `HOLUniformList.prop)) :=
  produced_source_admission_and_common_formation gamma (actualRequest gamma)
    (actualNativeProof gamma) (actual_produced gamma)

/-! ## Missing declarations, actual shadowing and unchanged meaning limits -/

theorem wire_relator_without_hol_rejects_nil {context : Tower.Ctx n} (type : Tower.Tm n) :
    ¬ Typing NativeWireRelatorCompatibility.rules context
      FormationSensitiveHOLUniformList.rawNil type := by
  intro typed
  obtain ⟨declared, level, known, _, _⟩ := typed.constFormation
  have absent : NativeWireRelatorCompatibility.rules.constantType `HOLUniformList.nil = none :=
    by decide
  rw [absent] at known
  cases known

/-- An actual conflicting declaration would change the wire Data lookup.
Opacity alone is not a freshness or component-embedding theorem. -/
def collidingSignature : Signature Tower.Head :=
  signature.insert NativeWireData.dataName ⟨.const `HOLUniformList.prop, none⟩

theorem collision_changes_wire_declaration :
    NativeWireData.rules.constantType NativeWireData.dataName = some (sortTm Tower.zero) ∧
      (OpaqueRelatorExtension.rules collidingSignature).constantType NativeWireData.dataName =
        some (.const `HOLUniformList.prop) ∧
      (OpaqueRelatorExtension.rules collidingSignature).constantType NativeWireData.dataName ≠
        NativeWireData.rules.constantType NativeWireData.dataName := by decide

open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
  UniformListChartNIKService Logic.HOL.UniformListInduction in
theorem common_formation_does_not_supply_induction :
    Judgment rules (context types []) rawMapLength (.const `HOLUniformList.prop) ∧
      ¬ ∃ proof, (intrinsicKernel []).decide (equations, mapLength) proof = true :=
  ⟨hol_judgment (mapLength_formed []), missing_induction_has_no_native_proof⟩

open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
  UniformListChartNIKService Logic.HOL.UniformListInduction in
theorem common_formation_does_not_change_model_meaning :
    Judgment rules (context types []) rawMapLength (.const `HOLUniformList.prop) ∧
      ¬ (∀ claim : SourceClaim [], JunkModel.model.models claim.2 ↔
        Nonempty ((intrinsicProofSystem []).ProofFibre claim)) :=
  ⟨hol_judgment (mapLength_formed []), unconditional_junk_meaning_not_adequate⟩

#print axioms hol_entry_fresh
#print axioms opacity
#print axioms hol_judgment
#print axioms wire_relator_judgment
#print axioms root_preservation
#print axioms checked_step_preserves
#print axioms mixed_payload_judgment
#print axioms mixed_projection_admitted
#print axioms actual_source_admission_and_common_formation
#print axioms wire_relator_without_hol_rejects_nil
#print axioms collision_changes_wire_declaration
#print axioms common_formation_does_not_change_model_meaning

end HOLNativeRelatorCompatibility
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
