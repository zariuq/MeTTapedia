import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientDeclarations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientInterpretationControls

/-! # Concrete controls for declared constants in the formed quotient -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientDeclarations
open _root_.CategoryTheory Declaration FormationSensitive QuotientInterpretation
namespace Controls

open NativeIndexedFamilies

theorem natural_wire_entry (payload : Nat) :
    NativeWireData.signature.entries (.num NativeWireData.naturalPrefix payload) =
      some ⟨NativeWireData.dataType, none⟩ := by
  simp [NativeWireData.signature, NativeWireData.dataName, NativeWireData.applicationName,
    NativeWireData.consName, NativeWireData.nilName]

theorem natural_common_entry (payload : Nat) :
    HOLNativeRelatorCompatibility.signature.entries (.num NativeWireData.naturalPrefix payload) =
      some ⟨NativeWireData.dataType, none⟩ :=
  HOLNativeRelatorCompatibility.signature_extends_wire.entries (natural_wire_entry payload)

theorem natural_effective_lookup (payload : Nat) :
    HOLNativeRelatorCompatibility.rules.constantType (.num NativeWireData.naturalPrefix payload) =
      some NativeWireData.dataType := by
  exact combinedType_of_signature IntrinsicRelator.rules HOLNativeRelatorCompatibility.signature
    (NativeWireRelatorCompatibility.wire_declarations_fresh (natural_wire_entry payload))
    (by simp only [Signature.typeOf?, natural_common_entry, Option.map_some])

def naturalConstant (payload : Nat) : Term Common.context Common.wireType :=
  closedConstant (.num NativeWireData.naturalPrefix payload) Common.wireType
    (natural_effective_lookup payload)

theorem natural_closed_meaning (payload : Nat) :
    TermMeaning Common.context (.const (.num NativeWireData.naturalPrefix payload))
      NativeWireData.dataType (QType.mk Common.wireType) (TermFibre.mk (naturalConstant payload)) :=
  closed_constant_meaning (.num NativeWireData.naturalPrefix payload) Common.wireType
    (natural_effective_lookup payload)

/-- All literals in the existing infinite natural-name family are covered.
The declaration meaning is the actual constant class, not a decoded value
used to manufacture an interpretation of other native terms. -/
theorem natural_in_caller (context : Context HOLNativeRelatorCompatibility.rules) (payload : Nat) :
    Judgment HOLNativeRelatorCompatibility.rules context.raw
      (.const (.num NativeWireData.naturalPrefix payload)) NativeWireData.dataType ∧
    TermMeaning context (.const (.num NativeWireData.naturalPrefix payload))
      NativeWireData.dataType (QType.mk (typeIn context Common.wireType))
      (TermFibre.mk (constantIn context (.num NativeWireData.naturalPrefix payload)
        Common.wireType (natural_effective_lookup payload))) :=
  ⟨caller_constant_judgment context (.num NativeWireData.naturalPrefix payload)
      Common.wireType (natural_effective_lookup payload),
    caller_constant_meaning context (.num NativeWireData.naturalPrefix payload)
      Common.wireType (natural_effective_lookup payload)⟩

def mixedCaller : Context HOLNativeRelatorCompatibility.rules :=
  extend Common.context Common.payloadType

/-- This is a nonidentity native substitution whose newest component is
the existing mixed HOL-list/wire payload. Constants retain their meaning
when that actual caller environment is filled. -/
theorem natural_after_mixed_substitution (payload : Nat) (wire : NativeWireData.Wire) :
    QuotientCwf.totalSub
      (QTerm.mk (constantIn mixedCaller (.num NativeWireData.naturalPrefix payload)
        Common.wireType (natural_effective_lookup payload)))
      (QuotientCwf.project (Common.sectionHom (Common.payload wire))) =
      QTerm.mk (naturalConstant payload) :=
  caller_constant_class_substitution (Common.sectionHom (Common.payload wire))
    (.num NativeWireData.naturalPrefix payload) Common.wireType (natural_effective_lookup payload)

theorem natural_meaning_iff (first second : Nat) :
    TermMeaning Common.context (.const (.num NativeWireData.naturalPrefix first))
      NativeWireData.dataType (QType.mk Common.wireType) (TermFibre.mk (naturalConstant second)) ↔
      first = second := by
  constructor
  · intro meaning
    have exactValue := (caller_meaning_iff Common.context _ Common.wireType
      (natural_effective_lookup first) _ _).mp meaning
    have converted := ((QTerm.mk_eq_iff _ _).mp exactValue.2).2
    apply (QuotientControls.natural_conversion_iff first second).mp
    simpa only [constantIn, Term.reindex, naturalConstant, closedConstant,
      NativeWireData.encode, subst] using converted
  · intro same
    subst second
    exact natural_closed_meaning first

theorem seven_cannot_mean_eight :
    ¬ TermMeaning Common.context (.const (.num NativeWireData.naturalPrefix 7))
      NativeWireData.dataType (QType.mk Common.wireType) (TermFibre.mk (naturalConstant 8)) := by
  intro meaning
  have impossible := (natural_meaning_iff 7 8).mp meaning
  cases impossible

def holUniversalType : TypeOver Common.context where
  code := FormationSensitiveHOLUniformList.universalType
  level := .sort (.max (.succ Tower.zero) Tower.zero)
  universeWitness := .sort _
  formed := HOLNativeRelatorCompatibility.hol_typing
    FormationSensitiveHOLUniformList.universal_type_formed

theorem hol_universal_entry :
    HOLNativeRelatorCompatibility.signature.entries `HOLUniformList.universal =
      some ⟨FormationSensitiveHOLUniformList.universalType, none⟩ :=
  HOLNativeRelatorCompatibility.signature_extends_hol.entries (by rfl)

theorem hol_universal_lookup :
    HOLNativeRelatorCompatibility.rules.constantType `HOLUniformList.universal =
      some FormationSensitiveHOLUniformList.universalType :=
  HOLNativeRelatorCompatibility.hol_constant_preserved (by decide)

def holUniversal : Term Common.context holUniversalType :=
  closedConstant `HOLUniformList.universal holUniversalType hol_universal_lookup

/-- This preserves the actual dependent declaration type and its native
constant class. It does not turn HOL truth into native proof inhabitation. -/
theorem hol_universal_in_mixed_caller :
    TypeMeaning mixedCaller (liftClosed FormationSensitiveHOLUniformList.universalType)
      (QType.mk (typeIn mixedCaller holUniversalType)) ∧
    TermMeaning mixedCaller (.const `HOLUniformList.universal)
      (liftClosed FormationSensitiveHOLUniformList.universalType)
      (QType.mk (typeIn mixedCaller holUniversalType))
      (TermFibre.mk (constantIn mixedCaller `HOLUniformList.universal
        holUniversalType hol_universal_lookup)) :=
  ⟨caller_type_meaning mixedCaller holUniversalType,
    caller_constant_meaning mixedCaller `HOLUniformList.universal holUniversalType hol_universal_lookup⟩

theorem hol_universal_after_mixed_substitution (wire : NativeWireData.Wire) :
    QuotientCwf.totalSub
      (QTerm.mk (constantIn mixedCaller `HOLUniformList.universal
        holUniversalType hol_universal_lookup))
      (QuotientCwf.project (Common.sectionHom (Common.payload wire))) =
      QTerm.mk (constantIn Common.context `HOLUniformList.universal
        holUniversalType hol_universal_lookup) :=
  caller_constant_class_substitution (Common.sectionHom (Common.payload wire)) _ _ hol_universal_lookup

theorem data_actual_entry :
    HOLNativeRelatorCompatibility.signature.entries NativeWireData.dataName =
      some ⟨sortTm Tower.zero, none⟩ :=
  HOLNativeRelatorCompatibility.signature_extends_wire.entries (by rfl)

/-- Higher cumulative typing of the existing Data constant does not replace
the fixed declaration entry. This is an installation discriminator, not a
claim that the higher typing itself must be rejected. -/
theorem cumulative_retyping_does_not_replace_entry :
    Judgment HOLNativeRelatorCompatibility.rules Common.context.raw NativeWireData.dataType
      (sortTm (.succ Tower.zero)) ∧
    HOLNativeRelatorCompatibility.signature.entries NativeWireData.dataName ≠
      some ⟨sortTm (.succ Tower.zero), none⟩ := by
  constructor
  · refine ⟨.nil, .cumul Common.wireType.formed ?_⟩
    change ∀ valuation, LevelExpr.eval valuation Tower.zero ≤
      LevelExpr.eval valuation (.succ Tower.zero)
    intro valuation
    simp only [LevelExpr.eval]
    exact Nat.le_succ _
  · intro changed
    rw [data_actual_entry] at changed
    have impossible := congrArg Entry.type (Option.some.inj changed)
    cases impossible

theorem missing_declaration_has_no_meaning
    (context : Context HOLNativeRelatorCompatibility.rules)
    (annotation : Tower.Tm context.arity) (semanticType : QType context)
    (value : TermFibre semanticType) :
    ¬ TermMeaning context (.const FormationSensitiveCompletedConversion.Controls.missingName)
      annotation semanticType value :=
  no_term_meaning_of_missing context _ (by decide) annotation semanticType value

theorem missing_declaration_has_no_type_meaning
    (context : Context HOLNativeRelatorCompatibility.rules) (semanticType : QType context) :
    ¬ TypeMeaning context (.const FormationSensitiveCompletedConversion.Controls.missingName)
      semanticType := no_type_meaning_of_missing context _ (by decide) semanticType

end Controls

end FormationSensitiveContextual.QuotientDeclarations
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
