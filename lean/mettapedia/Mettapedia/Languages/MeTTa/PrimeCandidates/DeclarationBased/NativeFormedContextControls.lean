import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticContextualCategory
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility

/-! # Concrete controls for formation-sensitive contextual category -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual
open _root_.CategoryTheory FormationSensitive
/-! ## Common-package admission and the unquotiented boundary -/

namespace Common

open HOLNativeRelatorCompatibility NativeIndexedFamilies

abbrev context : Context HOLNativeRelatorCompatibility.rules := empty _

/-- The coverage theorem applies to every admitted term of the actual
common package, at every formed telescope, not just the examples below. -/
theorem all_judgments_represented (context : Context HOLNativeRelatorCompatibility.rules)
    (term type : Tower.Tm context.arity) :
    Judgment HOLNativeRelatorCompatibility.rules context.raw term type ↔
      ∃ formedType : TypeOver context, formedType.code = type ∧
        ∃ value : Term context formedType, value.code = term :=
  judgment_iff_term context
    (OpaqueRelatorExtension.universes (signature := HOLNativeRelatorCompatibility.signature))
    term type

def wireType : TypeOver context :=
  ⟨NativeWireData.dataType, .sort Tower.zero, .sort _,
    wire_typing (NativeWireData.dataType_formed .nil)⟩

def payloadType : TypeOver context :=
  ⟨mixedPayloadType, .sort (.max Intrinsic.elementLevel Tower.zero), .sort _,
    mixed_payload_type_formed .nil⟩

def payload (wire : NativeWireData.Wire) : Term context payloadType :=
  ⟨mixedPayload wire, mixed_payload_typed .nil wire⟩

def projected (wire : NativeWireData.Wire) : Term context wireType :=
  ⟨.snd (mixedPayload wire), .sndElim (mixed_payload_typed .nil wire)⟩

def result (wire : NativeWireData.Wire) : Term context wireType :=
  ⟨NativeWireData.encode wire, (mixed_projection_admitted wire).typing⟩

def sectionHom {type : TypeOver context} (term : Term context type) : context ⟶ extend context type :=
  pair (𝟙 context) (term.cast type.reindex_id.symm)

/-- The actual mixed native value can be passed through a formed context
extension and recovered, with its complete refined source judgment. -/
theorem mixed_payload_comprehension (wire : NativeWireData.Wire) :
    Judgment HOLNativeRelatorCompatibility.rules context.raw (payload wire).code payloadType.code ∧
      (pulledNewest (sectionHom (payload wire))).code = mixedPayload wire := by
  exact ⟨(payload wire).judgment, by simp [sectionHom, pair, payload]⟩

theorem projected_converts_result (wire : NativeWireData.Wire) :
    Conv HOLNativeRelatorCompatibility.rules.headEq (projected wire).code (result wire).code
      HOLNativeRelatorCompatibility.rules.computation :=
  .rel _ _ (.betaSigmaSnd holSequenceSingleton (NativeWireData.encode wire))

/-- This syntactic structural base is not yet a conversion-invariant model:
the real mixed projection and its natural-number result are distinct codes
and distinguishable by the newest-variable comprehension consumer. -/
theorem converted_sections_distinct :
    sectionHom (projected (.natural 7)) ≠ sectionHom (result (.natural 7)) := by
  apply pair_distinguishes_codes
  simp only [Term.cast_code]
  intro same
  simp [projected, result, NativeWireData.encode] at same

theorem different_wire_sections (first second : NativeWireData.Wire) (different : first ≠ second) :
    sectionHom (result first) ≠ sectionHom (result second) := by
  apply pair_distinguishes_codes
  simp only [Term.cast_code]
  intro same
  exact different (NativeWireData.encode_injective same)

/-- A concrete required consumer: inspect the native newest component with
the existing wire decoder. Neither an arbitrary semantic observer nor an
ambient-family definability assumption is involved. -/
def readWire (morphism : context ⟶ extend context wireType) : Option NativeWireData.Wire :=
  NativeWireData.decode (morphism.substitution 0)

theorem readWire_section (wire : NativeWireData.Wire) :
    readWire (sectionHom (result wire)) = some wire := by
  simp [readWire, sectionHom, pair, result, NativeWireData.decode_encode]

/-- An interpretation that identifies these native sections cannot support
this specific required wire consumer. This does not demand global semantic
functionality or preservation of every conceivable code observation. -/
theorem no_wire_recovery_after_identification {View : Type*}
    (view : (context ⟶ extend context wireType) → View)
    (first second : NativeWireData.Wire) (different : first ≠ second)
    (identified : view (sectionHom (result first)) = view (sectionHom (result second))) :
    ¬ ∃ recover : View → Option NativeWireData.Wire,
      ∀ wire, recover (view (sectionHom (result wire))) = readWire (sectionHom (result wire)) := by
  rintro ⟨recover, exactReadout⟩
  have firstRead := exactReadout first
  have secondRead := exactReadout second
  rw [readWire_section] at firstRead secondRead
  rw [identified] at firstRead
  exact different (Option.some.inj (firstRead.symm.trans secondRead))

end Common

/-- The old raw constant rule really admits the dangling declaration, but
no formation-sensitive term in any formed context can retain that code. -/
theorem dangling_raw_use_is_not_a_formed_term :
    HasType FormationSensitive.Examples.danglingDeclarationRules (.nil : Tower.Ctx 0)
      (.const FormationSensitive.Examples.declaredName) (.const FormationSensitive.Examples.missingName) ∧
    ∀ (context : Context FormationSensitive.Examples.danglingDeclarationRules)
      (type : TypeOver context) (term : Term context type),
      term.code ≠ .const FormationSensitive.Examples.declaredName := by
  refine ⟨FormationSensitive.Examples.raw_accepts_dangling_declaration, ?_⟩
  intro context type term same
  have typed := term.typed
  rw [same] at typed
  exact FormationSensitive.Examples.rejects_dangling_declaration typed

end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
