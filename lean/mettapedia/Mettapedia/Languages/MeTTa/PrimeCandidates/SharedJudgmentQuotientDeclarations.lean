import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentDeclarationInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientDeclarations
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientDeclarationControls

/-!+# Actual declaration meanings on the shared native quotient

This attachment uses the very same formed quotient interpretation as the
shared admission and constructor interfaces. An independently admitted
declaration instance supplies its actual closed type and constant classes.
The table is noncomputable: its classical admission test is a semantic
construction, not a runtime declaration checker or proof search algorithm.

Every admitted instance is covered, for any independently supplied required
family. Exact installation and closed formation remain necessary for a
selected entry. Arbitrary formed callers and admitted substitutions use the
existing native constant construction and quotient action. Missing names and
changed natural values are rejected without identifying failed admission
with semantic falsity of a proposition.

No complete shared constructor/service qualification, external set model,
identity policy, or final candidate choice is asserted here.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientDeclarations

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment
open FormationSensitiveContextual
open SharedJudgmentDeclarationInterpretation (Instance Meaning Coverage ClosedTypeAgreement ClosedHeadAgreement)

variable {assembly : Assembly}

/-- The chosen level is only a formation witness. The retained type code is
exactly the installed instance's closed annotation. -/
noncomputable def closedType (slot : Instance) (admitted : slot.Admitted assembly) :
    TypeOver (empty assembly.rules) where
  code := slot.entry.type
  level := .sort (Classical.choose admitted.2)
  universeWitness := .sort _
  formed := (Classical.choose_spec admitted.2).typing

noncomputable def closedMeaning (slot : Instance) (admitted : slot.Admitted assembly) :
    Meaning (SharedJudgmentQuotientInterpretation.data assembly) where
  type := QType.mk (closedType slot admitted)
  value := TermFibre.mk (QuotientDeclarations.closedConstant slot.name (closedType slot admitted) admitted.1.2)

/-- A partial semantic attachment, not an executable admission procedure.
It is absent exactly when the existing instance admission predicate fails. -/
noncomputable def declarations (assembly : Assembly) :
    SharedJudgmentDeclarationInterpretation.Data (SharedJudgmentQuotientInterpretation.data assembly) := by
  classical
  exact ⟨fun slot => if admitted : slot.Admitted assembly then
    some (closedMeaning slot admitted) else none⟩

theorem selected_of_admitted (slot : Instance) (admitted : slot.Admitted assembly) :
    (declarations assembly).meaning slot = some (closedMeaning slot admitted) := by
  classical
  simp only [declarations, dif_pos admitted]

theorem declined_of_not_admitted (slot : Instance) (notAdmitted : ¬ slot.Admitted assembly) :
    (declarations assembly).meaning slot = none := by
  classical
  simp only [declarations, dif_neg notAdmitted]

theorem selected_iff (slot : Instance) (meaning : Meaning (SharedJudgmentQuotientInterpretation.data assembly)) :
    (declarations assembly).meaning slot = some meaning ↔
      ∃ admitted : slot.Admitted assembly, closedMeaning slot admitted = meaning := by
  classical
  by_cases admitted : slot.Admitted assembly
  · rw [selected_of_admitted slot admitted]
    constructor
    · intro selected
      exact ⟨admitted, Option.some.inj selected⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rw [declined_of_not_admitted slot admitted]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨actual, _⟩
      exact (admitted actual).elim

theorem isSome_iff_admitted (slot : Instance) :
    ((declarations assembly).meaning slot).isSome = true ↔ slot.Admitted assembly := by
  classical
  by_cases admitted : slot.Admitted assembly
  · simp only [selected_of_admitted slot admitted, Option.isSome_some, admitted]
  · simp only [declined_of_not_admitted slot admitted, Option.isSome_none, Bool.false_eq_true,
      admitted]

/-- Coverage does not choose the required family: every externally named
required instance is covered whenever that very instance is admitted. -/
theorem coverage (required : Instance → Prop) : Coverage required (declarations assembly) := by
  intro slot _ admitted
  exact ⟨closedMeaning slot admitted, selected_of_admitted slot admitted⟩

theorem closed_type_agreement : ClosedTypeAgreement (declarations assembly) := by
  intro slot meaning admitted selected
  rw [selected_of_admitted slot admitted] at selected
  cases Option.some.inj selected
  exact QuotientDeclarations.closed_type_meaning (closedType slot admitted)

theorem closed_head_agreement : ClosedHeadAgreement (declarations assembly) := by
  intro slot meaning admitted selected
  rw [selected_of_admitted slot admitted] at selected
  cases Option.some.inj selected
  exact QuotientDeclarations.closed_constant_meaning slot.name (closedType slot admitted) admitted.1.2

/-- This consequence consumes the existing shared declaration interface
and the actual quotient interpretation's proved substitution laws. -/
theorem required_in_caller (required : Instance → Prop) (slot : Instance)
    (needed : required slot) (admitted : slot.Admitted assembly)
    {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n) :
    ∃ (meaning : Meaning (SharedJudgmentQuotientInterpretation.data assembly))
      (semantic : (QuotientCwf.cwf assembly.rules).Sub
        ((SharedJudgmentQuotientInterpretation.data assembly).ctx source) ((SharedJudgmentQuotientInterpretation.data assembly).ctx .nil)),
      (declarations assembly).meaning slot = some meaning ∧
      (SharedJudgmentQuotientInterpretation.data assembly).sub .nil source (renSub Fin.elim0) semantic ∧
      Judgment assembly.rules source.raw (.const slot.name) (liftClosed slot.entry.type) ∧
      (SharedJudgmentQuotientInterpretation.data assembly).ty source (liftClosed slot.entry.type)
        ((QuotientCwf.cwf assembly.rules).tySub meaning.type semantic) ∧
      (SharedJudgmentQuotientInterpretation.data assembly).term source (.const slot.name) (liftClosed slot.entry.type)
        ((QuotientCwf.cwf assembly.rules).tySub meaning.type semantic)
        ((QuotientCwf.cwf assembly.rules).tmSub meaning.value semantic) :=
  SharedJudgmentDeclarationInterpretation.required_declared_head_meaning
    (SharedJudgmentQuotientInterpretation.data assembly) (declarations assembly) required (coverage required)
    closed_type_agreement closed_head_agreement SharedJudgmentQuotientInterpretation.substitution_stable
    SharedJudgmentQuotientInterpretation.substitutions_total slot needed admitted source source.formed

noncomputable def callerType {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    (slot : Instance) (admitted : slot.Admitted assembly) : QType (SharedJudgmentQuotientInterpretation.context source) :=
  QType.mk (QuotientDeclarations.typeIn (SharedJudgmentQuotientInterpretation.context source) (closedType slot admitted))

noncomputable def callerValue {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    (slot : Instance) (admitted : slot.Admitted assembly) : TermFibre (callerType source slot admitted) :=
  TermFibre.mk (QuotientDeclarations.constantIn (SharedJudgmentQuotientInterpretation.context source) slot.name
    (closedType slot admitted) admitted.1.2)

/-- The selected closed table entry and the actual weakened constant share
one source instance and one shared interpretation, in every formed caller. -/
theorem selected_in_caller {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    (slot : Instance) (admitted : slot.Admitted assembly) :
    (declarations assembly).meaning slot = some (closedMeaning slot admitted) ∧
      Judgment assembly.rules source.raw (.const slot.name) (liftClosed slot.entry.type) ∧
      (SharedJudgmentQuotientInterpretation.data assembly).ty source (liftClosed slot.entry.type)
        (callerType source slot admitted) ∧
      (SharedJudgmentQuotientInterpretation.data assembly).term source (.const slot.name) (liftClosed slot.entry.type)
        (callerType source slot admitted) (callerValue source slot admitted) :=
  ⟨selected_of_admitted slot admitted,
    QuotientDeclarations.caller_constant_judgment (SharedJudgmentQuotientInterpretation.context source) slot.name
      (closedType slot admitted) admitted.1.2,
    QuotientDeclarations.caller_type_meaning (SharedJudgmentQuotientInterpretation.context source) (closedType slot admitted),
    QuotientDeclarations.caller_constant_meaning (SharedJudgmentQuotientInterpretation.context source) slot.name
      (closedType slot admitted) admitted.1.2⟩

/-- Every semantic substitution related to the submitted native one has
the actual constant action. This is not restricted to a chosen weakening. -/
theorem caller_substitution {n m : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {target : SharedJudgmentInterpretation.Context assembly m}
    {sigma : Sub Tower.Head n m}
    {semantic : (QuotientCwf.cwf assembly.rules).Sub
      ((SharedJudgmentQuotientInterpretation.data assembly).ctx target) ((SharedJudgmentQuotientInterpretation.data assembly).ctx source)}
    (related : (SharedJudgmentQuotientInterpretation.data assembly).sub source target sigma semantic)
    (slot : Instance) (admitted : slot.Admitted assembly) :
    QuotientCwf.tySub (callerType source slot admitted) semantic = callerType target slot admitted ∧
      QuotientCwf.totalSub (callerValue source slot admitted).val semantic =
        (callerValue target slot admitted).val :=
  QuotientDeclarations.caller_substitution_meaning related slot.name (closedType slot admitted) admitted.1.2

theorem declined_of_missing (slot : Instance)
    (missing : assembly.rules.constantType slot.name = none) :
    (declarations assembly).meaning slot = none := by
  apply declined_of_not_admitted slot
  intro admitted
  have known := admitted.1.2
  rw [missing] at known
  cases known

theorem no_meaning_of_missing {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    (name : DeclName) (missing : assembly.rules.constantType name = none)
    (annotation : Tower.Tm n) (semanticType : QType (SharedJudgmentQuotientInterpretation.context source))
    (value : TermFibre semanticType) :
    ¬ (SharedJudgmentQuotientInterpretation.data assembly).term source (.const name) annotation semanticType value :=
  QuotientDeclarations.no_term_meaning_of_missing (SharedJudgmentQuotientInterpretation.context source) name missing annotation
    semanticType value

namespace Controls

open SharedJudgmentDeclarationInterpretation.Controls (naturalInstance natural_admitted)

theorem natural_selected (payload : Nat) (levels : Nat → LevelExpr Nat) :
    (declarations common).meaning (naturalInstance payload levels) =
      some (closedMeaning (naturalInstance payload levels) (natural_admitted payload levels)) :=
  selected_of_admitted _ _

/-- The chosen formation level cannot change the literal's native value
class. The actual constructor and its admitted code establish this equation. -/
theorem natural_value_class (payload : Nat) (levels : Nat → LevelExpr Nat) :
    (closedMeaning (naturalInstance payload levels) (natural_admitted payload levels)).value.val =
      QTerm.mk (QuotientDeclarations.Controls.naturalConstant payload) := by
  apply Quotient.sound
  exact ⟨.refl _, .refl _⟩

theorem natural_lookup_iff (first second : Nat) (levels : Nat → LevelExpr Nat) :
    (declarations common).meaning (naturalInstance first levels) =
      some (closedMeaning (naturalInstance second levels) (natural_admitted second levels)) ↔
      first = second := by
  constructor
  · intro selected
    rw [natural_selected] at selected
    have meanings := Option.some.inj selected
    have values := congrArg (fun meaning : Meaning (SharedJudgmentQuotientInterpretation.data common) => meaning.value.val)
      meanings
    rw [natural_value_class, natural_value_class] at values
    have converted := ((QTerm.mk_eq_iff _ _).mp values).2
    apply (QuotientControls.natural_conversion_iff first second).mp
    simpa only [QuotientDeclarations.Controls.naturalConstant, QuotientDeclarations.closedConstant, NativeWireData.encode]
      using converted
  · intro equal
    subst second
    exact natural_selected first levels

theorem seven_does_not_select_eight :
    (declarations common).meaning (naturalInstance 7 LevelExpr.param) ≠
      some (closedMeaning (naturalInstance 8 LevelExpr.param) (natural_admitted 8 LevelExpr.param)) := by
  intro selected
  have impossible := (natural_lookup_iff 7 8 LevelExpr.param).mp selected
  cases impossible

def holUniversalInstance : Instance :=
  ⟨`HOLUniformList.universal, ⟨FormationSensitiveHOLUniformList.universalType, none⟩, LevelExpr.param⟩

theorem hol_universal_admitted : holUniversalInstance.Admitted common := by
  refine ⟨⟨QuotientDeclarations.Controls.hol_universal_entry, QuotientDeclarations.Controls.hol_universal_lookup⟩,
    .max (.succ Tower.zero) Tower.zero, .nil, ?_⟩
  exact QuotientDeclarations.Controls.holUniversalType.formed

theorem hol_universal_selected :
    (declarations common).meaning holUniversalInstance =
      some (closedMeaning holUniversalInstance hol_universal_admitted) :=
  selected_of_admitted _ _

/-- The actual single-field caller contains a mixed HOL-list/wire payload,
not a fresh example datatype standing in for the native context. -/
def mixedContext : SharedJudgmentInterpretation.Context common 1 :=
  ⟨QuotientDeclarations.Controls.mixedCaller.raw, QuotientDeclarations.Controls.mixedCaller.formed⟩

theorem filled_mixed_substitution (slot : Instance) (admitted : slot.Admitted common)
    (wire : NativeWireData.Wire) :
    QuotientCwf.tySub (callerType mixedContext slot admitted)
        (QuotientCwf.project (Common.sectionHom (Common.payload wire))) =
      callerType .nil slot admitted ∧
      QuotientCwf.totalSub (callerValue mixedContext slot admitted).val
        (QuotientCwf.project (Common.sectionHom (Common.payload wire))) =
      (callerValue .nil slot admitted).val := by
  apply caller_substitution (source := mixedContext)
    (target := SharedJudgmentInterpretation.Context.nil)
    (sigma := (Common.sectionHom (Common.payload wire)).substitution)
  exact ⟨(Common.sectionHom (Common.payload wire)).typed, rfl⟩

/-- A selected real HOL declaration is interpreted in the mixed caller and
retains its exact native class after the actual payload section is filled. -/
theorem hol_universal_through_filled_caller (wire : NativeWireData.Wire) :
    (declarations common).meaning holUniversalInstance =
        some (closedMeaning holUniversalInstance hol_universal_admitted) ∧
      (SharedJudgmentQuotientInterpretation.data common).term mixedContext
        (.const holUniversalInstance.name) (liftClosed holUniversalInstance.entry.type)
        (callerType mixedContext holUniversalInstance hol_universal_admitted)
        (callerValue mixedContext holUniversalInstance hol_universal_admitted) ∧
      QuotientCwf.totalSub
        (callerValue mixedContext holUniversalInstance hol_universal_admitted).val
        (QuotientCwf.project (Common.sectionHom (Common.payload wire))) =
        (callerValue .nil holUniversalInstance hol_universal_admitted).val :=
  ⟨hol_universal_selected,
    (selected_in_caller mixedContext holUniversalInstance hol_universal_admitted).2.2.2,
    (filled_mixed_substitution holUniversalInstance hol_universal_admitted wire).2⟩

def missingInstance : Instance :=
  ⟨FormationSensitiveCompletedConversion.Controls.missingName,
    ⟨NativeWireData.dataType, none⟩, LevelExpr.param⟩

/-- Changing only the name retains a genuinely formed annotation but
does not install a declaration or supply a native constant meaning. -/
theorem formed_annotation_missing_name :
    Judgment common.rules .nil missingInstance.entry.type (sortTm Tower.zero) ∧
      (declarations common).meaning missingInstance = none := by
  refine ⟨⟨.nil, ?_⟩, declined_of_missing missingInstance (by decide)⟩
  exact HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed .nil)

theorem missing_name_has_no_meaning {n : Nat}
    (source : SharedJudgmentInterpretation.Context common n) (annotation : Tower.Tm n)
    (semanticType : QType (SharedJudgmentQuotientInterpretation.context source)) (value : TermFibre semanticType) :
    ¬ (SharedJudgmentQuotientInterpretation.data common).term source (.const missingInstance.name)
      annotation semanticType value :=
  no_meaning_of_missing source _ (by decide) annotation semanticType value

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientDeclarations
