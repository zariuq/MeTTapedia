import Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation
import Mettapedia.GSLT.LanguageDef.NIKGSLT
import Mettapedia.GSLT.LanguageDef.PreparedEquationCompilation
import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
import Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel
import Mettapedia.Languages.MeTTa.Prime.InternalDataTransport
import Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionTheory
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-!
# Prime motivation curriculum gate

The executable curriculum in `MettaKernel/Curriculum/PrimeMotivation`
starts with ordinary HE and PeTTa programs.  This gate parses a representative
expression from each lesson at Lean elaboration time and checks that both
explicit dialect selectors expand to the same kernel-checked `Pattern`.

The linked theorem surfaces are checked below as declarations, rather than
copied into a second pedagogical model.  Runtime speed remains a future CeTTa
measurement; the current Lean results establish the licenses and semantic
comparisons that can justify such an optimization.
-/

namespace Mettapedia.Languages.MeTTa.Prime.PrimeMotivationCurriculum

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-! ## The same authored probes in the two ordinary dialects -/

def dfaProbePeTTa : Pattern :=
  metta% petta "(dfa-run q0 (Cons one (Cons zero (Cons one Nil))))"

def dfaProbeHE : Pattern :=
  metta% he "(dfa-run q0 (Cons one (Cons zero (Cons one Nil))))"

theorem dfa_probe_dialects_agree : dfaProbePeTTa = dfaProbeHE := by
  rfl

def protocolProbePeTTa : Pattern :=
  metta% petta
    "(validate-response ticket-7 1 (response ticket-7 (payload datum)))"

def protocolProbeHE : Pattern :=
  metta% he
    "(validate-response ticket-7 1 (response ticket-7 (payload datum)))"

theorem protocol_probe_dialects_agree :
    protocolProbePeTTa = protocolProbeHE := by
  rfl

def separatedWavePeTTa : Pattern :=
  metta% petta
    "(describe-wave purse-left purse-right (Cons zero Nil) (Cons one Nil))"

def separatedWaveHE : Pattern :=
  metta% he
    "(describe-wave purse-left purse-right (Cons zero Nil) (Cons one Nil))"

theorem separated_wave_dialects_agree :
    separatedWavePeTTa = separatedWaveHE := by
  rfl

def contestedWavePeTTa : Pattern :=
  metta% petta
    "(describe-wave shared-purse shared-purse (Cons zero Nil) (Cons one Nil))"

/-- Negative control: source syntax retains the resource distinction that
Prime's effect analysis uses when deciding whether to issue a parallel
license. -/
theorem separated_wave_ne_contested_wave :
    separatedWavePeTTa ≠ contestedWavePeTTa := by
  decide

def proofArticleProbePeTTa : Pattern :=
  metta% petta
    "(article-accepted (Cons hyp-A (Cons hyp-A-implies-B (Cons mp (Cons end Nil)))))"

def proofArticleProbeHE : Pattern :=
  metta% he
    "(article-accepted (Cons hyp-A (Cons hyp-A-implies-B (Cons mp (Cons end Nil)))))"

theorem proof_article_probe_dialects_agree :
    proofArticleProbePeTTa = proofArticleProbeHE := by
  rfl

def unfinishedProofArticlePeTTa : Pattern :=
  metta% petta "(article-accepted (Cons hyp-A (Cons hyp-A-implies-B Nil)))"

/-- Negative control: a finished and unfinished proof article remain distinct
kernel terms before any proof checker is invoked. -/
theorem finished_article_ne_unfinished_article :
    proofArticleProbePeTTa ≠ unfinishedProofArticlePeTTa := by
  decide

def previewProbePeTTa : Pattern :=
  metta% petta
    "(use-payload preview (Cons zero Nil) (Cons one Nil))"

def previewProbeHE : Pattern :=
  metta% he
    "(use-payload preview (Cons zero Nil) (Cons one Nil))"

theorem preview_probe_dialects_agree : previewProbePeTTa = previewProbeHE := by
  rfl

def commitProbePeTTa : Pattern :=
  metta% petta
    "(use-payload commit (Cons zero Nil) (Cons one Nil))"

/-- Negative control: the source retains whether validation is demanded; the
checked-plan layer may not silently turn preview into commit. -/
theorem preview_probe_ne_commit_probe : previewProbePeTTa ≠ commitProbePeTTa := by
  decide

def promotionProbePeTTa : Pattern :=
  metta% petta "(promote (ZeroApp f (ZeroApp g (ZeroAtom a))))"

def promotionProbeHE : Pattern :=
  metta% he "(promote (ZeroApp f (ZeroApp g (ZeroAtom a))))"

theorem promotion_probe_dialects_agree :
    promotionProbePeTTa = promotionProbeHE := by
  rfl

def reverseDirectionProbePeTTa : Pattern :=
  metta% petta "(promote (PrimeAtom already-prime))"

/-- Negative control: the ordinary syntax permits the wrong-direction call,
but it remains distinct from a source-language promotion.  Prime removes this
case by indexing the operation over its source and target languages. -/
theorem source_promotion_ne_reverse_direction_call :
    promotionProbePeTTa ≠ reverseDirectionProbePeTTa := by
  decide

/-! ## Checked links from lessons to theory -/

#check Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core.modeFits
#check Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation.runCompiled_eq_runSource_of_compile?
#check Mettapedia.GSLT.LanguageDef.PreparedEquationCompilation.runAdmittedOrSource_eq_instantiate_of_compileEquation?
#check Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation.indexedProtocolTy
#check Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation.one_request_rejects_two_field_response
#check Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation.rejected_blame_does_not_gate_raw_execution
#check Mettapedia.Languages.MeTTa.Prime.NativeInteractionSeam.unknownCommPlan_raw_reachable
#check Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.CostEffectSeparation.realizes_productSquare
#check Mettapedia.Languages.MeTTa.Prime.NativeFibredCost.compiledSchedule_workSpan
#check Mettapedia.Languages.MeTTa.Prime.NativeFibredCost.Examples.contested_has_no_prime_parallel_license
#check Mettapedia.Languages.MeTTa.Prime.NativeFibredCost.Examples.contested_analysis_produces_no_schedule
#check Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost.parallel_two_events_ne_sequential
#check Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation.Builder.finish?_closed_sound
#check Mettapedia.GSLT.LanguageDef.NIKGSLT.Family.acceptance_implies_certified
#check Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.NativeCanary.rejected_check_does_not_gate_raw_execution
#check Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.demandCheck_evaluationCount
#check Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.executionWorkSpanWithDemand_ne_withoutDemand
#check Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.cachedValue_zero_work_one_observation
#check Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.variables_are_fixed
#check Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.constructor_translation_is_nontrivial
#check Mettapedia.Languages.MeTTa.Prime.InternalDataTransport.transport_commutes_with_opening
#check Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax.no_reverse_gslt_operation_has_syntax

end Mettapedia.Languages.MeTTa.Prime.PrimeMotivationCurriculum
