import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Possibility

/-!
# The presentation as the framework runs it

* The framework's validator (`LanguageDef.validate`) asks for distinct rewrite names; the presentation names
  each rewrite by its position. For the demo program the names are distinct (`demo_names_nodup`).
* The framework's executable compiler of the least contextual relation (`ContextualStep.rewriteAt`), run by
  the kernel on the demo, computes from the store `{1, 2}` exactly the two stores that `Language.step_storeCode`
  predicts (`demo_reducts`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

/-- **The demo's presented rewrites have distinct names.** -/
theorem demo_names_nodup : ((present Examples.demo).rewrites.map (·.name)).Nodup := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- **The framework's executable compiler computes the presented step**: from the store `{1, 2}` of the demo, one
contextual layer of rewriting gives exactly `{2, 2}` (take `1`, make `2`) and `{3, 2, 1}` (read `2`, make `3`), as
`Language.step_storeCode` predicts. -/
theorem demo_reducts :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
        (present Examples.demo) 1 (storeCode [.sym 1, .sym 2]) =
      [storeCode [.sym 2, .sym 2], storeCode [.sym 3, .sym 2, .sym 1]] := by
  decide +kernel

#print axioms demo_names_nodup
#print axioms demo_reducts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
