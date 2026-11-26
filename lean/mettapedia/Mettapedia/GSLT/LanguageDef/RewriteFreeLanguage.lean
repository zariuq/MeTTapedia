import Mettapedia.GSLT.LanguageDef.TotalGSLT

/-! An object language with an empty rewrite declaration list has no step.
Its equations and relation environment stay explicit. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TotalGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

theorem languageGSLTUsing_no_step_of_no_rewrites {relations : RelationEnv}
    {language : LanguageDef} {laws : ReductionRespectsEquationsUsing relations language}
    (noRewrites : language.rewrites = []) {source target : Pattern} :
    ¬ (languageGSLTUsing relations language laws).Step source target := by
  intro reduction
  obtain ⟨_, step⟩ := (languageGSLTUsing_step relations language laws source target).mp reduction
  cases step with
  | rule member => simp [noRewrites] at member

theorem languageGSLT_no_step_of_no_rewrites {language : LanguageDef}
    {laws : ReductionRespectsEquations language} (noRewrites : language.rewrites = [])
    {source target : Pattern} : ¬ (languageGSLT language laws).Step source target :=
  languageGSLTUsing_no_step_of_no_rewrites noRewrites

end Mettapedia.GSLT.LanguageDef.TotalGSLT
