import Mettapedia.OSLF.Syntax.RhoOperationalClosure
import Mettapedia.OSLF.Syntax.RhoAuthoredDropProfile
import Mettapedia.OSLF.Syntax.RhoIntrinsicEncoding
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-!
# Contextual scope in the two Chapter 7 rho presentations

The intrinsic positioned-rule `Step` closes below every constructor. The
canonical authored rho presentation grants contextual reduction through its
declared parallel-bag `ParCong` rule. These are different operational
presentations even after adding the source's Drop rule to both. A concrete
COMM firing below an output payload separates them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoContextScopeComparison

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.Binding.RhoSchema.Authored
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-- The encoded source and reduct of the intrinsic output-payload step. -/
def outputCommSource : Pattern := encodeTerm (outputCarrying commSource)
def outputCommTarget : Pattern := encodeTerm (outputCarrying commTarget)

/-- The intrinsic contextual closure takes this step under `POutput`. -/
theorem intrinsic_output_step :
    rhoSourceWithDrop.Step (outputCarrying commSource)
      (outputCarrying commTarget) :=
  broad_contextual_output_step

private theorem comm_no_match_output :
    matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite
      outputCommSource = [] := by
  decide +kernel

private theorem parCong_no_match_output :
    matchPatternForRuleUsing rhoReflectionProfile rhoParCongRewrite
      outputCommSource = [] := by
  decide +kernel

private theorem drop_no_match_output :
    matchPatternForRuleUsing rhoReflectionProfile rhoDropRewrite
      outputCommSource = [] := by
  decide +kernel

/-- No authored rule is rooted at the output constructor. In particular,
the declared `ParCong` does not silently descend into output payloads. -/
theorem authored_output_rewriteAt_nil (fuel : Nat) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      rhoRuleInterpretation rhoBasePremises rhoCalcWithDrop
      fuel outputCommSource = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      change (rhoCalcWithDrop.rewrites.flatMap fun rule =>
        Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing
          rhoRuleInterpretation rhoBasePremises rhoCalcWithDrop
          (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
            rhoRuleInterpretation rhoBasePremises rhoCalcWithDrop fuel)
          rule outputCommSource) = []
      simp [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
        rhoCalcWithDrop, rhoCalc, rhoRuleInterpretation,
        comm_no_match_output, parCong_no_match_output,
        drop_no_match_output]

/-- The source is inert in the canonical authored relation with Drop added,
at every finite proof depth and for every proposed target. -/
theorem authored_output_no_step (target : Pattern) :
    ¬ Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      rhoRuleInterpretation rhoBasePremises rhoCalcWithDrop
      outputCommSource target := by
  rintro ⟨fuel, bounded⟩
  have member :=
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.mem_rewriteAt_iff_stepAt.mpr
      bounded
  rw [authored_output_rewriteAt_nil] at member
  exact List.not_mem_nil member

/-- Therefore no unconditional translation of all raw intrinsic contextual
steps to the authored rho rule relation can use this term encoding. The
comparison must restrict contextual authority or explicitly extend it. -/
theorem unrestricted_step_translation_fails :
    ¬ ∀ {source target : Term sig [] Srt.pr},
      rhoSourceWithDrop.Step source target →
        Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
          rhoRuleInterpretation rhoBasePremises rhoCalcWithDrop
          (encodeTerm source) (encodeTerm target) := by
  intro translation
  exact authored_output_no_step outputCommTarget
    (translation intrinsic_output_step)

end Mettapedia.OSLF.Binding.RhoContextScopeComparison
