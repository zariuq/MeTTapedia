import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

example : RhoSameColorViewPairRestorationAligned := by
  intro targetFree available outer leftPattern rightPattern type left right
    color declarationColor leftView rightView roots closeSmaller canonical
  cases roots with
  | bvar index =>
      rcases left.pattern_shape_of_rootIsStatic leftView.rootIsStatic with
        ⟨_, _, shape⟩ | ⟨_, _, _, shape⟩ <;> cases shape
  | fvar name =>
      rcases left.pattern_shape_of_rootIsStatic leftView.rootIsStatic with
        ⟨_, _, shape⟩ | ⟨_, _, _, shape⟩ <;> cases shape
  | lambda binder body =>
      rcases left.pattern_shape_of_rootIsStatic leftView.rootIsStatic with
        ⟨_, _, shape⟩ | ⟨_, _, _, shape⟩ <;> cases shape
  | multiLambda arity binders body =>
      rcases left.pattern_shape_of_rootIsStatic leftView.rootIsStatic with
        ⟨_, _, shape⟩ | ⟨_, _, _, shape⟩ <;> cases shape
  | subst body replacement =>
      rcases left.pattern_shape_of_rootIsStatic leftView.rootIsStatic with
        ⟨_, _, shape⟩ | ⟨_, _, _, shape⟩ <;> cases shape
  | apply notQuote children => skip
  | collection collectionType elements => skip
  | collectionRest collectionType rest elements => skip

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
