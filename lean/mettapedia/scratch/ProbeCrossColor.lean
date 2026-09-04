import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem probeCrossColor (declarationColor : CostStaticColor) :
    RhoCollapsingCrossColorFramesRestoreTogetherInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    leftColor rightColor leftView rightView colorNe sortEq sortNotProc
    admissible leftWS rightWS closeSmaller collapsing canonical
  have leftName : leftView.node.sourceSort.1 = "Name" := by
    rcases LanguageDefCanonicalSection.rhoLangSort_eq_proc_or_name
        leftView.node.sourceSort with procEq | nameEq
    · exact absurd (congrArg Subtype.val procEq) sortNotProc
    · exact congrArg Subtype.val nameEq
  have rightName : rightView.node.sourceSort.1 = "Name" := sortEq ▸ leftName
  obtain ⟨leftArgs, leftSkelArgs, leftPatShape, leftSkelShape⟩ :=
    rhoNameFibre_view_shape leftView leftName
  obtain ⟨rightArgs, rightSkelArgs, rightPatShape, rightSkelShape⟩ :=
    rhoNameFibre_view_shape rightView rightName
  rw [leftPatShape, rightPatShape] at collapsing canonical
  have declSide := rhoCrossColorNameFibre_declarationColor_eq collapsing
  rcases declSide with declLeft | declRight
  · subst declLeft
    obtain ⟨argument, argsEq, argCanonical⟩ :=
      rhoNameFibre_collapse_equation colorNe canonical
    rcases rhoNameFibre_canonicalFrame_shape leftView.node _ leftName with
      ⟨li, lEq⟩ | ⟨ln, lEq⟩ | ⟨lw, largs, lsc, lEq⟩
    · skip
    · skip
    · skip
  · subst declRight
    skip

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
