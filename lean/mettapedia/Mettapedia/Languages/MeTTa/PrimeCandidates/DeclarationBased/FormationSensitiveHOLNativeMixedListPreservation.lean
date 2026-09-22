import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedSchemas

/-!
# Native List and identity preservation in the mixed proof environment

The canonical native schemas are transported through the actual level
substitution. The arguments and result adjustments are recovered from the
caller's joint-system derivation, not assumed to belong to a smaller system.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveHOLNativeMixedListPreservation

open Presentation Presentation.Declaration NativeIndexedFamilies
open FormationSensitive
open FormationSensitiveHOLNativeMixedSchemas
abbrev jointRules := FormationSensitiveHOLProofListIntegration.rules
open HOLNativeMixedConversionParallel (mixedPiConversionBoundary)

variable {n : Nat}

namespace ListElimination

open Intrinsic
open FormationSensitiveNativeListElimination
  (eliminatorContext eliminatorResult eliminatorSubstitution
   constructorContext constructorResult constructorSubstitution)
open FormationSensitiveHOLNativeMixedSchemas (Typing universes)

/-- The generic native dependent eliminator is usable in any joint context.
The parameter telescope retains the motive and both branch obligations;
the result is that same motive applied to the supplied list. -/
theorem eliminate_typed {context : Tower.Ctx n}
    {element motive nilCase consCase list : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor jointRules (lowerContext contextAPZS) context
      (nilSchemaSubstitution element motive nilCase consCase))
    (listTyped : Typing context list (listApp element)) :
    Typing context (eliminateApp element motive nilCase consCase list) (.app motive list) := by
  have specialized := (native_typed
    FormationSensitiveNativeListElimination.eliminateAtParameters_hasType).substitute parameters
  have declared : Typing context
      (.app (.app (.app (.app (.const eliminateName) element) motive) nilCase) consCase)
      (.pi (listApp element) (.app (rename wk motive) (.var 0))) := by
    simpa [lowerTerm, RussellTarski.substLevelsTm, Tm.mapHead,
      eliminateAtParameters, eliminateAtParametersType, listApp, nilSchemaSubstitution,
      nilCaseSchemaSubstitution, motiveSchemaSubstitution, elementSchemaSubstitution,
      consSub, Fin.cases, Fin.induction, Fin.induction.go, subst, rename, wk,
      liftSub, liftRen, subst_rename, rename_subst] using specialized
  have applied := FormationSensitive.Typing.appElim declared listTyped
  change Typing context (eliminateApp element motive nilCase consCase list)
    (.app (inst0 list (rename wk motive)) list) at applied
  rw [inst0_rename_wk] at applied
  exact applied

theorem eliminateArguments {context : Tower.Ctx n}
    (formed : ContextFormation jointRules context)
    {element motive nilCase consCase list displayed : Tower.Tm n}
    (observed : Typing context (eliminateApp element motive nilCase consCase list) displayed) :
    FormationSensitive.CtxMor jointRules (lowerContext contextAPZS) context
        (nilSchemaSubstitution element motive nilCase consCase) ∧
      Typing context list (listApp element) ∧
      (∀ {replacement}, Typing context replacement (.app motive list) →
        Typing context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes
    mixedPiConversionBoundary formed
    (lowerContext eliminatorContext) (lowerTerm eliminatorResult)
    (eliminatorSubstitution element motive nilCase consCase list)
    (nativeSpine context (by decide)
      FormationSensitiveNativeListElimination.eliminateType_hasType (.sort _)) observed
  exact ⟨typed.dropNewest, typed (0 : Fin 5), replay⟩

theorem consArguments {context : Tower.Ctx n}
    (formed : ContextFormation jointRules context)
    {element head tail displayed : Tower.Tm n}
    (observed : Typing context (consApp element head tail) displayed) :
    Typing context head element ∧ Typing context tail (listApp element) := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes
    mixedPiConversionBoundary formed
    (lowerContext constructorContext) (lowerTerm constructorResult)
    (constructorSubstitution element head tail)
    (nativeSpine context (by decide) FormationSensitiveNativeList.consType_hasType (.sort _)) observed
  exact ⟨typed (1 : Fin 3), typed (0 : Fin 3)⟩

theorem consSchema_typed {context : Tower.Ctx n}
    {element motive nilCase consCase head tail : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor jointRules (lowerContext contextAPZS) context
      (nilSchemaSubstitution element motive nilCase consCase))
    (headTyped : Typing context head element)
    (tailTyped : Typing context tail (listApp element)) :
    FormationSensitive.CtxMor jointRules (lowerContext contextAPZSHeadTail) context
      (consSchemaSubstitution element motive nilCase consCase head tail) := by
  have withHead : FormationSensitive.CtxMor jointRules (lowerContext contextAPZSHead) context
      (consSub head (nilSchemaSubstitution element motive nilCase consCase)) :=
    parameters.extend headTyped
  exact withHead.extend tailTyped

theorem nil_preserves {context : Tower.Ctx n}
    (formed : ContextFormation jointRules context)
    {element motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp element motive nilCase consCase (nilApp element)) displayed) :
    Typing context nilCase displayed := by
  obtain ⟨parameters, _, replay⟩ := eliminateArguments formed observed
  exact replay (schema_substitute
    FormationSensitiveNativeListElimination.nilIota_judgments.2 formed parameters).typing

theorem cons_preserves {context : Tower.Ctx n}
    (formed : ContextFormation jointRules context)
    {element motive nilCase consCase head tail displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp element motive nilCase consCase (consApp element head tail)) displayed) :
    Typing context
      (.app (.app (.app consCase head) tail)
        (eliminateApp element motive nilCase consCase tail)) displayed := by
  obtain ⟨parameters, listTyped, replay⟩ := eliminateArguments formed observed
  obtain ⟨headTyped, tailTyped⟩ := consArguments formed listTyped
  have arguments := consSchema_typed parameters headTyped tailTyped
  exact replay (schema_substitute
    FormationSensitiveNativeListElimination.consIota_judgments.2 formed arguments).typing

end ListElimination

namespace IdentityElimination

open Intrinsic
open FormationSensitiveNativeIdentity (identityResult identitySubstitution)
open FormationSensitiveHOLNativeMixedSchemas (Typing universes)

theorem identityArguments {context : Tower.Ctx n}
    (formed : ContextFormation jointRules context)
    {element point motive reflCase endpoint equality displayed : Tower.Tm n}
    (observed : Typing context
      (identityEliminateApp element point motive reflCase endpoint equality) displayed) :
    FormationSensitive.CtxMor jointRules (lowerContext contextAXPD) context
        (identitySchemaSubstitution element point motive reflCase) ∧
      Typing context endpoint element ∧
      Typing context equality (.id element point endpoint) ∧
      (∀ {replacement},
        Typing context replacement (.app (.app motive endpoint) equality) →
        Typing context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes
    mixedPiConversionBoundary formed
    (lowerContext contextAXPDYQ) (lowerTerm identityResult)
    (identitySubstitution element point motive reflCase endpoint equality)
    (nativeSpine context (by decide)
      FormationSensitiveNativeIdentity.identityEliminateType_hasType (.sort _)) observed
  exact ⟨typed.dropNewest.dropNewest, typed (1 : Fin 6), typed (0 : Fin 6), replay⟩

theorem identity_preserves {context : Tower.Ctx n}
    (formed : ContextFormation jointRules context)
    {element point motive reflCase displayed : Tower.Tm n}
    (observed : Typing context
      (identityEliminateApp element point motive reflCase point (.refl point)) displayed) :
    Typing context reflCase displayed := by
  obtain ⟨parameters, _, _, replay⟩ := identityArguments formed observed
  exact replay (schema_substitute
    FormationSensitiveNativeIdentity.identityIota_judgments.2 formed parameters).typing

end IdentityElimination

#print axioms ListElimination.eliminateArguments
#print axioms ListElimination.eliminate_typed
#print axioms ListElimination.consArguments
#print axioms ListElimination.consSchema_typed
#print axioms ListElimination.nil_preserves
#print axioms ListElimination.cons_preserves
#print axioms IdentityElimination.identityArguments
#print axioms IdentityElimination.identity_preserves

end FormationSensitiveHOLNativeMixedListPreservation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
