import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLProofListIntegration

/-!
# Dependent List elimination in the common HOL/List environment

The eliminator is applied to independently typed arguments in an arbitrary
context. Its motive may depend on the entire list; no constant-family
restriction or additional computation rule is imposed.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveMixedListElimination

open Presentation Presentation.Declaration NativeIndexedFamilies IntrinsicMaps
open RussellTarski FormationSensitiveHOLProofListIntegration

variable {n : Nat}

theorem listApp_typed {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyped : Typing context element (sortTm Tower.zero)) :
    Typing context (Intrinsic.listApp element) (sortTm Tower.zero) := by
  have constant := execution_typed
    (FormationSensitiveNativeHOLMapExecution.listConstant_typed context)
  exact FormationSensitive.Typing.appElim constant elementTyped

theorem nilApp_typed {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyped : Typing context element (sortTm Tower.zero)) :
    Typing context (Intrinsic.nilApp element) (Intrinsic.listApp element) := by
  have constant := execution_typed
    (FormationSensitiveNativeHOLMapExecution.nilConstant_typed context)
  exact FormationSensitive.Typing.appElim constant elementTyped

theorem result_formed {context : Tower.Ctx n} {element motive list : Tower.Tm n}
    (motiveTyped : Typing context motive
      (.pi (Intrinsic.listApp element) (sortTm Tower.zero)))
    (listTyped : Typing context list (Intrinsic.listApp element)) :
    Typing context (.app motive list) (sortTm Tower.zero) :=
  FormationSensitive.Typing.appElim motiveTyped listTyped

def consCaseType (element motive : Tower.Tm n) : Tower.Tm n :=
  .pi element
    (.pi (Intrinsic.listApp (rename wk element))
      (.pi (.app (rename wk (rename wk motive)) (.var 0))
        (.app (rename wk (rename wk (rename wk motive)))
          (Intrinsic.consApp (rename wk (rename wk (rename wk element)))
            (.var 2) (.var 1)))))

theorem eliminateApp_typed {context : Tower.Ctx n}
    {element motive nilCase consCase list : Tower.Tm n}
    (elementTyped : Typing context element (sortTm Tower.zero))
    (motiveTyped : Typing context motive
      (.pi (Intrinsic.listApp element) (sortTm Tower.zero)))
    (nilTyped : Typing context nilCase (.app motive (Intrinsic.nilApp element)))
    (consTyped : Typing context consCase (consCaseType element motive))
    (listTyped : Typing context list (Intrinsic.listApp element)) :
    Typing context (Intrinsic.eliminateApp element motive nilCase consCase list)
      (.app motive list) := by
  have constant := execution_typed
    (FormationSensitiveNativeHOLMapExecution.eliminateConstant_typed context)
  have afterElement := FormationSensitive.Typing.appElim constant elementTyped
  have afterMotive := FormationSensitive.Typing.appElim afterElement motiveTyped
  have nilExpected : Typing context nilCase
      (instantiateTwoAt Tower.zero element motive Intrinsic.nilCaseType) := by
    rw [instantiateTwoAt_eq_subst, mapHead_nilCaseType,
      Intrinsic.subst_nilCaseType_motiveSchema]
    exact nilTyped
  have afterNil := FormationSensitive.Typing.appElim afterMotive nilExpected
  have consExpected : Typing context consCase
      (instantiateThreeAt Tower.zero element motive nilCase Intrinsic.consCaseType) := by
    rw [instantiateThreeAt_eq_subst, mapHead_consCaseType]
    change Typing context consCase (consCaseType element motive)
    exact consTyped
  have afterCons := FormationSensitive.Typing.appElim afterNil consExpected
  change Typing context _
    (instantiateFourAt Tower.zero element motive nilCase consCase
      Intrinsic.eliminateResultType) at afterCons
  rw [instantiateFourAt_eq_subst, mapHead_eliminateResultType,
    Intrinsic.subst_eliminateResult_nilSchema] at afterCons
  have afterList := FormationSensitive.Typing.appElim afterCons listTyped
  change Typing context (Intrinsic.eliminateApp element motive nilCase consCase list)
    (.app (inst0 list (rename wk motive)) list) at afterList
  rw [inst0_rename_wk] at afterList
  exact afterList

theorem eliminateApp_judgment {context : Tower.Ctx n}
    {element motive nilCase consCase list : Tower.Tm n}
    (contextFormed : FormationSensitive.ContextFormation rules context)
    (elementTyped : Typing context element (sortTm Tower.zero))
    (motiveTyped : Typing context motive
      (.pi (Intrinsic.listApp element) (sortTm Tower.zero)))
    (nilTyped : Typing context nilCase (.app motive (Intrinsic.nilApp element)))
    (consTyped : Typing context consCase (consCaseType element motive))
    (listTyped : Typing context list (Intrinsic.listApp element)) :
    FormationSensitive.Judgment rules context
      (Intrinsic.eliminateApp element motive nilCase consCase list) (.app motive list) :=
  ⟨contextFormed, eliminateApp_typed elementTyped motiveTyped nilTyped consTyped listTyped⟩

#print axioms listApp_typed
#print axioms nilApp_typed
#print axioms result_formed
#print axioms eliminateApp_typed
#print axioms eliminateApp_judgment

end FormationSensitiveMixedListElimination
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
