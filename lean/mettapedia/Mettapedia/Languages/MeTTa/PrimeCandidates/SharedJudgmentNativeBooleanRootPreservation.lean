import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRegion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeListEliminationPreservation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorEliminationPreservation

/-!
# Typed argument recovery for the computational Boolean extension

Every recovery starts with an arbitrary formation-sensitive typing in the
extended calculus. Declaration telescopes recover the actual arguments and
replay conversion and cumulativity at the original displayed type. The Pi
boundary is isolated here and discharged by the combined conversion module.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRootPreservation

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies


abbrev rules := SharedJudgmentNativeBooleanRegion.rules
abbrev theta : Nat → LevelExpr Nat := fun _ => SharedJudgmentNativeBooleanRegion.one
abbrev levelContext {k : Nat} (context : Tower.Ctx k) := substLevelsCtx theta context
abbrev levelTerm {k : Nat} (term : Tower.Tm k) := substLevelsTm theta term

variable {n : Nat}

theorem universes : UniverseRegularity rules :=
  (NativeIdentityLevelInstantiation.universes theta Signature.empty).includeSignature SharedJudgmentNativeBooleanRegion.signature

theorem includeNative {k : Nat} {context : Tower.Ctx k} {term type : Tower.Tm k}
    (typed : Typing IntrinsicRelator.rules context term type) :
    Typing rules (levelContext context) (levelTerm term) (levelTerm type) :=
  (((NativeIdentityLevelInstantiation.nativeInstance theta).refinedTyping typed).includeSignature
    (NativeIdentityLevelInstantiation.extensionSignature theta Signature.empty)).includeSignature SharedJudgmentNativeBooleanRegion.signature

theorem native_lookup {name : DeclName} {type : Tower.Tm 0}
    (known : IntrinsicRelator.rules.constantType name = some type) :
    rules.constantType name = some (levelTerm type) := by
  apply combinedType_of_base
  apply combinedType_of_base
  rw [NativeIdentityLevelInstantiation.native_lookup, known]
  rfl

theorem nativeSpine (context : Tower.Ctx n) {name : DeclName} {type : Tower.Tm 0}
    {level : LevelExpr Nat} (known : IntrinsicRelator.rules.constantType name = some type)
    (formed : Typing IntrinsicRelator.rules .nil type (sortTm level)) :
    DeclarationSpine rules context (.const name) (liftClosed (levelTerm type)) :=
  .constant (native_lookup known) (includeNative formed) (.sort (LevelExpr.subst theta level))

/-! ## The two Boolean roots -/

def booleanContext : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil SharedJudgmentNativeBooleanRegion.motiveType) (.app (.var 0) SharedJudgmentNativeBooleanRegion.falseTm))
    (.app (.var 1) SharedJudgmentNativeBooleanRegion.trueTm)) SharedJudgmentNativeBooleanRegion.boolTm

def booleanResult : Tower.Tm 4 := .app (.var 3) (.var 0)

def booleanSubstitution (motive onFalse onTrue value : Tower.Tm n) : Sub Tower.Head 4 n :=
  consSub value (consSub onTrue (consSub onFalse (consSub motive Fin.elim0)))

theorem booleanSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const SharedJudgmentNativeBooleanRegion.eliminateName) (liftClosed SharedJudgmentNativeBooleanRegion.eliminateType) :=
  .constant SharedJudgmentNativeBooleanRegion.eliminate_lookup SharedJudgmentNativeBooleanRegion.eliminateType_formed (.sort SharedJudgmentNativeBooleanRegion.eliminateLevel)

theorem booleanArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {motive onFalse onTrue value displayed : Tower.Tm n}
    (observed : Typing rules context (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue value) displayed) :
    Typing rules context onFalse (.app motive SharedJudgmentNativeBooleanRegion.falseTm) ∧
      Typing rules context onTrue (.app motive SharedJudgmentNativeBooleanRegion.trueTm) ∧
      (∀ {replacement}, Typing rules context replacement (.app motive value) →
        Typing rules context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    booleanContext booleanResult (booleanSubstitution motive onFalse onTrue value)
    (booleanSpine context) observed
  exact ⟨typed (2 : Fin 4), typed (1 : Fin 4), replay⟩

theorem boolean_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {left right displayed : Tower.Tm n} (evidence : SharedJudgmentNativeBooleanRegion.IotaEvidence n left right)
    (observed : Typing rules context left displayed) : Typing rules context right displayed := by
  cases evidence with
  | onFalse =>
      obtain ⟨falseTyped, _, replay⟩ := booleanArguments boundary formed observed
      exact replay falseTyped
  | onTrue =>
      obtain ⟨_, trueTyped, replay⟩ := booleanArguments boundary formed observed
      exact replay trueTyped

/-! ## The inherited List roots in the extended typing judgment -/

theorem listSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const Intrinsic.eliminateName)
      (liftClosed (levelTerm Intrinsic.eliminateType)) :=
  nativeSpine context (by decide) FormationSensitiveNativeListElimination.eliminateType_hasType

theorem listArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {element motive nilCase consCase list displayed : Tower.Tm n}
    (observed : Typing rules context (Intrinsic.eliminateApp element motive nilCase consCase list) displayed) :
    FormationSensitive.CtxMor rules (levelContext Intrinsic.contextAPZS) context
        (Intrinsic.nilSchemaSubstitution element motive nilCase consCase) ∧
      Typing rules context list (Intrinsic.listApp element) ∧
      (∀ {replacement}, Typing rules context replacement (.app motive list) →
        Typing rules context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    (levelContext FormationSensitiveNativeListElimination.eliminatorContext) (levelTerm FormationSensitiveNativeListElimination.eliminatorResult)
    (FormationSensitiveNativeListElimination.eliminatorSubstitution element motive nilCase consCase list)
    (listSpine context) observed
  exact ⟨typed.dropNewest, typed (0 : Fin 5), replay⟩

theorem listConsSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const Intrinsic.consName)
      (liftClosed (levelTerm Intrinsic.consType)) :=
  nativeSpine context (by decide) FormationSensitiveNativeList.consType_hasType

theorem listConsArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {element head tail displayed : Tower.Tm n}
    (observed : Typing rules context (Intrinsic.consApp element head tail) displayed) :
    Typing rules context head element ∧ Typing rules context tail (Intrinsic.listApp element) := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    (levelContext FormationSensitiveNativeListElimination.constructorContext) (levelTerm FormationSensitiveNativeListElimination.constructorResult)
    (FormationSensitiveNativeListElimination.constructorSubstitution element head tail) (listConsSpine context) observed
  exact ⟨typed (1 : Fin 3), typed (0 : Fin 3)⟩

theorem listNil_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {element motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing rules context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.nilApp element)) displayed) :
    Typing rules context nilCase displayed := by
  obtain ⟨parameters, _, replay⟩ := listArguments boundary formed observed
  exact replay ((includeNative FormationSensitiveNativeListElimination.nilIotaRight_hasType).substitute parameters)

theorem listCons_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {element motive nilCase consCase head tail displayed : Tower.Tm n}
    (observed : Typing rules context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.consApp element head tail)) displayed) :
    Typing rules context (.app (.app (.app consCase head) tail)
      (Intrinsic.eliminateApp element motive nilCase consCase tail)) displayed := by
  obtain ⟨parameters, listTyped, replay⟩ := listArguments boundary formed observed
  obtain ⟨headTyped, tailTyped⟩ := listConsArguments boundary formed listTyped
  have withHead : FormationSensitive.CtxMor rules (levelContext Intrinsic.contextAPZSHead) context
      (consSub head (Intrinsic.nilSchemaSubstitution element motive nilCase consCase)) :=
    parameters.extend headTyped
  have typed : FormationSensitive.CtxMor rules (levelContext Intrinsic.contextAPZSHeadTail) context
      (Intrinsic.consSchemaSubstitution element motive nilCase consCase head tail) :=
    withHead.extend tailTyped
  exact replay ((includeNative FormationSensitiveNativeListElimination.consIotaRight_hasType).substitute typed)

/-! ## Native identity elimination in the same extended judgment -/

theorem identitySpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const Intrinsic.identityEliminateName)
      (liftClosed (levelTerm Intrinsic.identityEliminateType)) :=
  nativeSpine context (by decide) FormationSensitiveNativeIdentity.identityEliminateType_hasType

theorem identityArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {element point motive reflCase endpoint equality displayed : Tower.Tm n}
    (observed : Typing rules context
      (Intrinsic.identityEliminateApp element point motive reflCase endpoint equality) displayed) :
    FormationSensitive.CtxMor rules (levelContext Intrinsic.contextAXPD) context
        (Intrinsic.identitySchemaSubstitution element point motive reflCase) ∧
      Typing rules context endpoint element ∧
      Typing rules context equality (.id element point endpoint) ∧
      (∀ {replacement}, Typing rules context replacement (.app (.app motive endpoint) equality) →
        Typing rules context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    (levelContext Intrinsic.contextAXPDYQ) (levelTerm FormationSensitiveNativeIdentity.identityResult)
    (FormationSensitiveNativeIdentity.identitySubstitution element point motive reflCase endpoint equality)
    (identitySpine context) observed
  exact ⟨typed.dropNewest.dropNewest, typed (1 : Fin 6), typed (0 : Fin 6), replay⟩

theorem identity_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {element point motive reflCase displayed : Tower.Tm n}
    (observed : Typing rules context
      (Intrinsic.identityEliminateApp element point motive reflCase point (.refl point)) displayed) :
    Typing rules context reflCase displayed := by
  obtain ⟨parameters, _, _, replay⟩ := identityArguments boundary formed observed
  exact replay ((includeNative FormationSensitiveNativeIdentity.identityIotaRight_hasType).substitute parameters)

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRootPreservation
