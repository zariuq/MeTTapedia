import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentTypeInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.DeclarationLevelInstantiation

/-!
# Declared meanings on the same native assembly

A slot retains its declaration name, schema entry and universe-level
substitution. Its instantiated entry must actually occur in the supplied
assembly and supply the effective constant lookup. This does not silently
make a fixed name universe-polymorphic: changing levels can require a
different signature. Closed formation remains an independent native premise.

The meaning attachment is partial, externally chosen data over the existing
interpretation's empty context. Coverage is indexed by the caller's required
instances. Agreement with closed native type and constant meanings is
separate from that data. Existing typed-substitution laws derive use in every
formed context admitting the relevant semantic substitution; no terminal
context equality or blanket term totality is imposed.

Application reuses the actual native Pi clause. Its comparison of selected
semantic type representatives is explicitly a sufficient strict class, not a
requirement that every host use equality instead of an independently licensed
comparison. No new unfolding rule, host or complete model is supplied.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentDeclarationInterpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive
open SharedJudgmentFragment SharedJudgmentTypeInterpretation

universe u v w w'

/-- Raw slot data. Neither source lookup nor target admission is hidden
in the record. -/
structure Instance where
  name : DeclName
  schema : Entry Tower.Head
  levels : Nat → LevelExpr

def Instance.entry (slot : Instance) : Entry Tower.Head :=
  slot.schema.instantiateLevels slot.levels

/-- The exact entry, including its optional value, is retained. The second
condition prevents a differently typed base declaration from shadowing it. -/
def Instance.Installed (assembly : Assembly) (slot : Instance) : Prop :=
  assembly.declarations.entries slot.name = some slot.entry ∧
    assembly.rules.constantType slot.name = some slot.entry.type

def Instance.Admitted (assembly : Assembly) (slot : Instance) : Prop :=
  slot.Installed assembly ∧
    ∃ level, Judgment assembly.rules .nil slot.entry.type (sortTm level)

theorem Instance.installed_of_fresh {assembly : Assembly} (slot : Instance)
    (known : assembly.declarations.entries slot.name = some slot.entry)
    (fresh : NativeIndexedFamilies.IntrinsicRelator.rules.constantType slot.name = none) :
    slot.Installed assembly := by
  refine ⟨known, combinedType_of_signature _ _ fresh ?_⟩
  simp only [Signature.typeOf?, known, Option.map_some]

/-- The existing level-instantiation interface establishes actual entry
provenance. Inclusion in this assembly is explicit, not inferred from a
same-name source lookup or from formation of the new type. -/
theorem Instance.installed_of_level_instance {assembly : Assembly} (slot : Instance)
    (source : Signature Tower.Head)
    (instantiation : LevelInstance source slot.levels)
    (sourceKnown : source.entries slot.name = some slot.schema)
    (included : instantiation.signature.Extends assembly.declarations)
    (fresh : NativeIndexedFamilies.IntrinsicRelator.rules.constantType slot.name = none) :
    slot.Installed assembly := by
  apply slot.installed_of_fresh
  · apply included.entries
    simp only [LevelInstance.signature, Signature.instantiateLevels, sourceKnown,
      Option.map_some, Instance.entry]
  · exact fresh

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-- A chosen closed semantic object, with no assertion about native syntax. -/
structure Meaning (interpretation : SharedJudgmentInterpretation.Data assembly C) where
  type : C.Ty (interpretation.ctx (.nil : SharedJudgmentInterpretation.Context assembly 0))
  value : C.Tm (interpretation.ctx (.nil : SharedJudgmentInterpretation.Context assembly 0)) type

/-- Partial declaration meanings. A raw attachment need not cover, form or
correctly interpret even one declaration. -/
structure Data (interpretation : SharedJudgmentInterpretation.Data assembly C) where
  meaning : Instance → Option (Meaning interpretation)

def Coverage {interpretation : SharedJudgmentInterpretation.Data assembly C}
    (required : Instance → Prop) (declarations : Data interpretation) : Prop :=
  ∀ slot, required slot → slot.Admitted assembly →
    ∃ meaning, declarations.meaning slot = some meaning

def ClosedTypeAgreement {interpretation : SharedJudgmentInterpretation.Data assembly C}
    (declarations : Data interpretation) : Prop :=
  ∀ slot meaning, slot.Admitted assembly →
    declarations.meaning slot = some meaning →
      interpretation.ty .nil slot.entry.type meaning.type

/-- The primitive clause is only for a closed declared head. Contextual use,
application and substitution consequences are derived below. -/
def ClosedHeadAgreement {interpretation : SharedJudgmentInterpretation.Data assembly C}
    (declarations : Data interpretation) : Prop :=
  ∀ slot meaning, slot.Admitted assembly →
    declarations.meaning slot = some meaning →
      interpretation.term .nil (.const slot.name) slot.entry.type
        meaning.type meaning.value

private theorem liftClosed_zero (term : Tower.Tm 0) :
    (liftClosed term : Tower.Tm 0) = term := by
  calc
    liftClosed term = rename id term := by
      apply rename_ext
      exact fun index => Fin.elim0 index
    _ = term := rename_id term

theorem Instance.head_judgment {n : Nat} {context : Tower.Ctx n} (slot : Instance)
    (admitted : slot.Admitted assembly) (formed : ContextFormation assembly.rules context) :
    Judgment assembly.rules context (.const slot.name) (liftClosed slot.entry.type) := by
  obtain ⟨level, closed⟩ := admitted.2
  exact ⟨formed, .const admitted.1.2 closed.typing (.sort level)⟩

private theorem empty_substitution_typed {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.CtxMor assembly.rules .nil context (renSub Fin.elim0) :=
  fun index => Fin.elim0 index

/-- Closed declaration agreement plus real interpretation substitution laws
derive the declared-head rule in an arbitrary formed native environment. -/
theorem declared_head_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (declarations : Data interpretation)
    (typeAgreement : ClosedTypeAgreement declarations)
    (headAgreement : ClosedHeadAgreement declarations)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (slot : Instance) (admitted : slot.Admitted assembly)
    (meaning : Meaning interpretation) (chosen : declarations.meaning slot = some meaning)
    {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n)
    (formed : ContextFormation assembly.rules context.raw)
    (semantic : C.Sub (interpretation.ctx context) (interpretation.ctx .nil))
    (related : interpretation.sub .nil context (renSub Fin.elim0) semantic) :
    Judgment assembly.rules context.raw (.const slot.name) (liftClosed slot.entry.type) ∧
      interpretation.ty context (liftClosed slot.entry.type) (C.tySub meaning.type semantic) ∧
      interpretation.term context (.const slot.name) (liftClosed slot.entry.type)
        (C.tySub meaning.type semantic) (C.tmSub meaning.value semantic) := by
  have closed : Judgment assembly.rules .nil (.const slot.name) slot.entry.type := by
    simpa only [liftClosed_zero] using slot.head_judgment admitted (.nil)
  have nativeType := typeAgreement slot meaning admitted chosen
  have nativeTerm := headAgreement slot meaning admitted chosen
  refine ⟨slot.head_judgment admitted formed, ?_, ?_⟩
  · simpa only [subst_renSub, liftClosed] using
      stable.1 0 n .nil context (renSub Fin.elim0) semantic slot.entry.type meaning.type
        formed (empty_substitution_typed (assembly := assembly) context.raw) related nativeType
  · simpa only [subst_renSub, rename, liftClosed] using
      stable.2 0 n .nil context (renSub Fin.elim0) semantic (.const slot.name)
        slot.entry.type meaning.type meaning.value formed
        (empty_substitution_typed (assembly := assembly) context.raw)
        closed related nativeType nativeTerm

/-- Only required admitted instances gain coverage. Existing substitution
coverage supplies the semantic map; no chosen terminal representative is
added to the CwF or to the declaration data. -/
theorem required_declared_head_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (declarations : Data interpretation) (required : Instance → Prop)
    (coverage : Coverage required declarations)
    (typeAgreement : ClosedTypeAgreement declarations)
    (headAgreement : ClosedHeadAgreement declarations)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (substitutions : SharedJudgmentInterpretation.AdmittedSubstitutionsTotal interpretation)
    (slot : Instance) (needed : required slot) (admitted : slot.Admitted assembly)
    {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n)
    (formed : ContextFormation assembly.rules context.raw) :
    ∃ (meaning : Meaning interpretation)
      (semantic : C.Sub (interpretation.ctx context) (interpretation.ctx .nil)),
      declarations.meaning slot = some meaning ∧
      interpretation.sub .nil context (renSub Fin.elim0) semantic ∧
      Judgment assembly.rules context.raw (.const slot.name) (liftClosed slot.entry.type) ∧
      interpretation.ty context (liftClosed slot.entry.type) (C.tySub meaning.type semantic) ∧
      interpretation.term context (.const slot.name) (liftClosed slot.entry.type)
        (C.tySub meaning.type semantic) (C.tmSub meaning.value semantic) := by
  obtain ⟨meaning, chosen⟩ := coverage slot needed admitted
  obtain ⟨semantic, related⟩ := substitutions 0 n .nil context (renSub Fin.elim0)
    formed (empty_substitution_typed (assembly := assembly) context.raw)
  exact ⟨meaning, semantic, chosen, related,
    declared_head_meaning interpretation declarations typeAgreement headAgreement stable
      slot admitted meaning chosen context formed semantic related⟩

/-- This is a named sufficient strict comparison route. The type equation
aligns the two supplied representatives; it neither follows from a carrier
isomorphism nor demands global strictness of the interpretation. -/
theorem declared_application_of_strict_comparison
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (declarations : Data interpretation) (operations : Operations C)
    (typeAgreement : ClosedTypeAgreement declarations)
    (headAgreement : ClosedHeadAgreement declarations)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (application : PiEliminationMeaning interpretation operations.products)
    (slot : Instance) (admitted : slot.Admitted assembly)
    (meaning : Meaning interpretation) (chosen : declarations.meaning slot = some meaning)
    {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n)
    (formed : ContextFormation assembly.rules context.raw)
    (semantic : C.Sub (interpretation.ctx context) (interpretation.ctx .nil))
    (related : interpretation.sub .nil context (renSub Fin.elim0) semantic)
    (domain argument : Tower.Tm n) (codomain : Tower.Tm (n + 1))
    (nativeShape : liftClosed slot.entry.type = .pi domain codomain)
    (family : Family interpretation context domain codomain)
    (familyAdmitted : FamilyAdmitted assembly context domain codomain)
    (familyMeaning : FamilyMeaning interpretation family)
    (semanticShape : C.tySub meaning.type semantic =
      operations.products.pi family.semanticDomain family.semanticCodomain)
    (argumentValue : C.Tm (interpretation.ctx context) family.semanticDomain)
    (argumentAdmitted : Judgment assembly.rules context argument domain)
    (argumentMeaning : interpretation.term context argument domain
      family.semanticDomain argumentValue) :
    let functionValue := cast (congrArg (C.Tm (interpretation.ctx context)) semanticShape)
      (C.tmSub meaning.value semantic)
    let resultType := C.tySub family.semanticCodomain
      (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend C argumentValue)
    Judgment assembly.rules context (.app (.const slot.name) argument) (inst0 argument codomain) ∧
      interpretation.ty context (inst0 argument codomain) resultType ∧
      interpretation.term context (.app (.const slot.name) argument) (inst0 argument codomain)
        resultType (operations.products.app functionValue argumentValue) := by
  obtain ⟨headTyped, _, headMeaning⟩ := declared_head_meaning interpretation declarations
    typeAgreement headAgreement stable slot admitted meaning chosen context formed semantic related
  rw [nativeShape] at headTyped headMeaning
  have compared := termMeaning_transport interpretation semanticShape
    (cast_heq (congrArg (C.Tm (interpretation.ctx context)) semanticShape)
      (C.tmSub meaning.value semantic)).symm headMeaning
  exact ⟨⟨formed, .appElim headTyped.typing argumentAdmitted.typing⟩,
    application n context domain (.const slot.name) argument codomain family _ argumentValue
      familyAdmitted familyMeaning headTyped argumentAdmitted compared argumentMeaning⟩

/-- Reusing the derived application meaning through an actual typed native
substitution needs no further declaration lookup or selected representative
in the target. This transports the selected semantic section, not an
arbitrary section along a type isomorphism. -/
theorem declared_application_substitution
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (declarations : Data interpretation) (operations : Operations C)
    (typeAgreement : ClosedTypeAgreement declarations)
    (headAgreement : ClosedHeadAgreement declarations)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (application : PiEliminationMeaning interpretation operations.products)
    (slot : Instance) (admitted : slot.Admitted assembly)
    (meaning : Meaning interpretation) (chosen : declarations.meaning slot = some meaning)
    {n m : Nat} (context : SharedJudgmentInterpretation.Context assembly n)
    (formed : ContextFormation assembly.rules context.raw)
    (semantic : C.Sub (interpretation.ctx context) (interpretation.ctx .nil))
    (related : interpretation.sub .nil context (renSub Fin.elim0) semantic)
    (domain argument : Tower.Tm n) (codomain : Tower.Tm (n + 1))
    (nativeShape : liftClosed slot.entry.type = .pi domain codomain)
    (family : Family interpretation context domain codomain)
    (familyAdmitted : FamilyAdmitted assembly context domain codomain)
    (familyMeaning : FamilyMeaning interpretation family)
    (semanticShape : C.tySub meaning.type semantic =
      operations.products.pi family.semanticDomain family.semanticCodomain)
    (argumentValue : C.Tm (interpretation.ctx context) family.semanticDomain)
    (argumentAdmitted : Judgment assembly.rules context argument domain)
    (argumentMeaning : interpretation.term context argument domain
      family.semanticDomain argumentValue)
    (target : SharedJudgmentInterpretation.Context assembly m) (sigma : Sub Tower.Head n m)
    (targetSemantic : C.Sub (interpretation.ctx target) (interpretation.ctx context))
    (targetFormed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules context target sigma)
    (targetRelated : interpretation.sub context target sigma targetSemantic) :
    let functionValue := cast (congrArg (C.Tm (interpretation.ctx context)) semanticShape)
      (C.tmSub meaning.value semantic)
    let resultType := C.tySub family.semanticCodomain
      (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend C argumentValue)
    let resultValue := operations.products.app functionValue argumentValue
    Judgment assembly.rules target (subst sigma (.app (.const slot.name) argument))
      (subst sigma (inst0 argument codomain)) ∧
      interpretation.ty target (subst sigma (inst0 argument codomain))
        (C.tySub resultType targetSemantic) ∧
      interpretation.term target (subst sigma (.app (.const slot.name) argument))
        (subst sigma (inst0 argument codomain)) (C.tySub resultType targetSemantic)
        (C.tmSub resultValue targetSemantic) := by
  obtain ⟨judgment, typeMeaning, termMeaning⟩ :=
    declared_application_of_strict_comparison interpretation declarations operations
      typeAgreement headAgreement stable application slot admitted meaning chosen context formed
      semantic related domain argument codomain nativeShape family familyAdmitted familyMeaning
      semanticShape argumentValue argumentAdmitted argumentMeaning
  exact ⟨judgment.substitute targetFormed typed,
    stable.1 n m context target sigma targetSemantic _ _ targetFormed typed targetRelated typeMeaning,
    stable.2 n m context target sigma targetSemantic _ _ _ _ targetFormed typed judgment
      targetRelated typeMeaning termMeaning⟩

namespace Controls

open NativeWireDataDenotation

/-- Every literal in the existing infinite natural-name family has an
actual installed entry. Its payload is not decoded to define meaning. -/
def naturalInstance (payload : Nat) (levels : Nat → LevelExpr) : Instance :=
  ⟨.num NativeWireData.naturalPrefix payload, ⟨NativeWireData.dataType, none⟩, levels⟩

private theorem natural_wire_entry (payload : Nat) :
    NativeWireData.signature.entries (.num NativeWireData.naturalPrefix payload) =
      some ⟨NativeWireData.dataType, none⟩ := by
  simp [NativeWireData.signature, NativeWireData.dataName, NativeWireData.applicationName,
    NativeWireData.consName, NativeWireData.nilName]

private theorem natural_common_type (payload : Nat) :
    common.rules.constantType (.num NativeWireData.naturalPrefix payload) =
      some NativeWireData.dataType := by
  exact combinedType_of_signature _ _
    (NativeWireRelatorCompatibility.wire_declarations_fresh (natural_wire_entry payload))
    (HOLNativeRelatorCompatibility.signature_extends_wire.typeOf (by
      simp only [Signature.typeOf?, natural_wire_entry, Option.map_some]))

theorem natural_admitted (payload : Nat) (levels : Nat → LevelExpr) :
    (naturalInstance payload levels).Admitted common := by
  refine ⟨⟨?_, natural_common_type payload⟩, Tower.zero, .nil, ?_⟩
  · exact HOLNativeRelatorCompatibility.signature_extends_wire.entries (natural_wire_entry payload)
  · exact HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed .nil)

def closedValue (value : Value) : Meaning SharedJudgmentServiceInterpretation.WireControls.interpretation where
  type := fun _ => Value
  value := fun _ => value

/-- An independently supplied value table. Nothing in this data asserts that
the chosen value is the literal named by the declaration. -/
def naturalData (values : Nat → Value) :
    Data SharedJudgmentServiceInterpretation.WireControls.interpretation where
  meaning slot := match slot.name with
    | .num tag payload =>
        if tag = NativeWireData.naturalPrefix then some (closedValue (values payload)) else none
    | _ => none

def NaturalRequired (slot : Instance) : Prop :=
  ∃ payload, slot.name = .num NativeWireData.naturalPrefix payload

private theorem natural_selected (values : Nat → Value) (slot : Instance)
    (meaning : Meaning SharedJudgmentServiceInterpretation.WireControls.interpretation) :
    (naturalData values).meaning slot = some meaning ↔
      ∃ payload, slot.name = .num NativeWireData.naturalPrefix payload ∧
        meaning = closedValue (values payload) := by
  cases named : slot.name with
  | anonymous => simp [naturalData, named]
  | str tag text => simp [naturalData, named]
  | num tag payload =>
      by_cases tagged : tag = NativeWireData.naturalPrefix
      · subst tag
        simp [naturalData, named, eq_comm]
      · simp [naturalData, named, tagged]

theorem natural_coverage (values : Nat → Value) : Coverage NaturalRequired (naturalData values) := by
  rintro slot ⟨payload, named⟩ _
  exact ⟨closedValue (values payload),
    (natural_selected values slot _).mpr ⟨payload, named, rfl⟩⟩

private theorem admitted_natural_type (slot : Instance) (admitted : slot.Admitted common)
    (payload : Nat) (named : slot.name = .num NativeWireData.naturalPrefix payload) :
    slot.entry.type = NativeWireData.dataType := by
  have effective := admitted.1.2
  rw [named, natural_common_type] at effective
  exact (Option.some.inj effective).symm

theorem natural_type_agreement (values : Nat → Value) :
    ClosedTypeAgreement (naturalData values) := by
  intro slot meaning admitted chosen
  obtain ⟨payload, named, rfl⟩ := (natural_selected values slot meaning).mp chosen
  exact ⟨admitted_natural_type slot admitted payload named, rfl⟩

theorem natural_head_agreement : ClosedHeadAgreement (naturalData Value.natural) := by
  intro slot meaning admitted chosen
  obtain ⟨payload, named, rfl⟩ := (natural_selected Value.natural slot meaning).mp chosen
  refine ⟨admitted_natural_type slot admitted payload named, _, ?_, HEq.rfl⟩
  rw [named]
  exact .natural payload

/-- Empty-source semantic substitution does not interpret the unrelated
mixed-context fields. The declaration's nontrivial carrier remains Value. -/
theorem natural_in_formed_context (payload : Nat) (levels : Nat → LevelExpr)
    {n : Nat} (context : SharedJudgmentInterpretation.Context common n)
    (formed : ContextFormation common.rules context.raw) :
    Judgment common.rules context.raw (.const (.num NativeWireData.naturalPrefix payload))
      NativeWireData.dataType ∧
      SharedJudgmentServiceInterpretation.WireControls.interpretation.ty context
        NativeWireData.dataType (fun _ => Value) ∧
      SharedJudgmentServiceInterpretation.WireControls.interpretation.term context
        (.const (.num NativeWireData.naturalPrefix payload)) NativeWireData.dataType
        (fun _ => Value) (fun _ => .natural payload) := by
  exact declared_head_meaning SharedJudgmentServiceInterpretation.WireControls.interpretation
    (naturalData Value.natural) (natural_type_agreement _) natural_head_agreement
    SharedJudgmentServiceInterpretation.WireControls.interpretation_substitution
    (naturalInstance payload levels) (natural_admitted payload levels)
    (closedValue (.natural payload)) (by simp [naturalData, naturalInstance]) context formed
    (fun _ => Fin.elim0) (fun index => Fin.elim0 index)

/-- The installed literal seven is interpreted on the actual common
HOL/List/wire context, with no claim that the partial wire interpretation
already gives meanings to its other fields. -/
theorem seven_in_common_context :
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      (.const (.num NativeWireData.naturalPrefix 7)) NativeWireData.dataType ∧
      SharedJudgmentServiceInterpretation.WireControls.interpretation.ty
        SharedJudgmentServiceInterpretation.WireControls.commonContext
        NativeWireData.dataType (fun _ => Value) ∧
      SharedJudgmentServiceInterpretation.WireControls.interpretation.term
        SharedJudgmentServiceInterpretation.WireControls.commonContext
        (.const (.num NativeWireData.naturalPrefix 7)) NativeWireData.dataType
        (fun _ => Value) (fun _ => .natural 7) :=
  natural_in_formed_context 7 LevelExpr.param
    SharedJudgmentServiceInterpretation.WireControls.commonContext
    OpaqueRelatorScopedComputation.Common.context_formed

/-- A still-covered, still-correctly-typed meaning table can assign the
wrong value to an actual admitted declaration. Native formation does not
establish the independently specified constant meaning. -/
theorem changed_value_fails_head_agreement :
    Coverage NaturalRequired (naturalData (fun payload => .natural (payload + 1))) ∧
    ClosedTypeAgreement (naturalData (fun payload => .natural (payload + 1))) ∧
    (naturalInstance 7 LevelExpr.param).Admitted common ∧
    ¬ ClosedHeadAgreement (naturalData (fun payload => .natural (payload + 1))) := by
  refine ⟨natural_coverage _, natural_type_agreement _, natural_admitted 7 _, ?_⟩
  intro agreement
  obtain ⟨_, denotation, denotes, same⟩ := agreement (naturalInstance 7 LevelExpr.param)
    (closedValue (.natural 8)) (natural_admitted 7 _) (by simp [naturalData, naturalInstance])
  have equal : (fun _ : Fin 0 → Value => Value.natural 8) = denotation := eq_of_heq same
  have fixed := denotes.functional (Denotes.natural 7)
  have impossible := congrFun (equal.trans fixed) Fin.elim0
  contradiction

/-- Unlike the name-only family used to separate semantic coverage from
admission, this externally stated family fixes the actual schema entries. -/
def RequiredNaturals (slot : Instance) : Prop :=
  ∃ payload levels, slot = naturalInstance payload levels

theorem actual_natural_family_qualified :
    (∀ slot, RequiredNaturals slot → slot.Admitted common) ∧
    Coverage RequiredNaturals (naturalData Value.natural) ∧
    ClosedTypeAgreement (naturalData Value.natural) ∧
    ClosedHeadAgreement (naturalData Value.natural) := by
  refine ⟨?_, ?_, natural_type_agreement _, natural_head_agreement⟩
  · rintro slot ⟨payload, levels, rfl⟩
    exact natural_admitted payload levels
  · rintro slot ⟨payload, levels, rfl⟩ admitted
    exact natural_coverage _ _ ⟨payload, rfl⟩ admitted

/-- An actual schema instantiation changes the declaration's type code.
This raw slot does not assert that the schema was installed in the target. -/
def dataInstance (level : LevelExpr) : Instance :=
  ⟨NativeWireData.dataName, ⟨sortTm (.param 0), none⟩, fun _ => level⟩

theorem data_instance_entry (level : LevelExpr) :
    (dataInstance level).entry = ⟨sortTm level, none⟩ := rfl

private theorem data_wire_entry :
    NativeWireData.signature.entries NativeWireData.dataName =
      some ⟨sortTm Tower.zero, none⟩ := by
  simp [NativeWireData.signature]

theorem data_zero_admitted : (dataInstance Tower.zero).Admitted common := by
  refine ⟨(dataInstance Tower.zero).installed_of_fresh ?_ ?_, .succ Tower.zero,
    .nil, .headType (.sort Tower.zero)⟩
  · exact HOLNativeRelatorCompatibility.signature_extends_wire.entries data_wire_entry
  · exact NativeWireRelatorCompatibility.wire_declarations_fresh data_wire_entry

/-- Formation of an instantiated entry is not evidence that the fixed
assembly installs it. The wrong slot still has a formed type in the very
same common context, while the correct Data declaration remains admitted. -/
theorem changed_level_formed_but_not_installed :
    (dataInstance Tower.zero).Admitted common ∧
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      (liftClosed (dataInstance (.succ Tower.zero)).entry.type)
      (sortTm (.succ (.succ Tower.zero))) ∧
    ¬ (dataInstance (.succ Tower.zero)).Installed common := by
  refine ⟨data_zero_admitted,
    ⟨OpaqueRelatorScopedComputation.Common.context_formed, .headType (.sort _)⟩, ?_⟩
  intro installed
  have actual := HOLNativeRelatorCompatibility.signature_extends_wire.entries data_wire_entry
  have requested := installed.1
  change HOLNativeRelatorCompatibility.signature.entries NativeWireData.dataName =
    some ⟨sortTm (.succ Tower.zero), none⟩ at requested
  rw [actual] at requested
  have impossible := congrArg Entry.type (Option.some.inj requested)
  cases impossible

theorem declaration_control_crown :
    (∀ slot, RequiredNaturals slot → slot.Admitted common) ∧
    Coverage RequiredNaturals (naturalData Value.natural) ∧
    ClosedTypeAgreement (naturalData Value.natural) ∧
    ClosedHeadAgreement (naturalData Value.natural) ∧
    ¬ ClosedHeadAgreement (naturalData (fun payload => .natural (payload + 1))) ∧
    ¬ (dataInstance (.succ Tower.zero)).Installed common :=
  ⟨actual_natural_family_qualified.1, actual_natural_family_qualified.2.1,
    actual_natural_family_qualified.2.2.1, actual_natural_family_qualified.2.2.2,
    changed_value_fails_head_agreement.2.2.2, changed_level_formed_but_not_installed.2.2⟩

end Controls

#print axioms Instance.installed_of_level_instance
#print axioms declared_head_meaning
#print axioms required_declared_head_meaning
#print axioms declared_application_of_strict_comparison
#print axioms declared_application_substitution
#print axioms Controls.natural_in_formed_context
#print axioms Controls.seven_in_common_context
#print axioms Controls.changed_value_fails_head_agreement
#print axioms Controls.changed_level_formed_but_not_installed
#print axioms Controls.declaration_control_crown

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentDeclarationInterpretation
