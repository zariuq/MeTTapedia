import Mettapedia.Languages.VibeITP.Presentation.SoundDefinitions
import Mettapedia.Languages.VibeITP.Presentation.RuleShapes

/-!
# Vibe-ITP presentation: assembled fixed-rule semantics

Each family theorem connects the actual rule-instance shapes to the
independent specification meanings. The dispatcher covers every named
kernel rule; built-in declarations and theory admissions are handled
by the admission module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-- Every instance of a rule preserves the independent judgment meaning. -/
def RuleMeaningSound (T : Theory) (r : FORule) : Prop :=
  ∀ args : List Pattern, args.length = r.vars.length →
    (∀ p ∈ r.instPremises args, Meaning T p) → Meaning T (r.instConclusion args)

theorem psuccRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ psuccRules) : RuleMeaningSound T r := by
  simp only [psuccRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sound_rPsucc1 (ms_rPsucc1 T)
  · exact sound_rPsuccO (ms_rPsuccO T)
  · exact sound_rPsuccI (ms_rPsuccI T)

theorem paddRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ paddRules) : RuleMeaningSound T r := by
  simp only [paddRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rPadd1l (ms_rPadd1l T)
  · exact sound_rPadd1r (ms_rPadd1r T)
  · exact sound_rPaddOo (ms_rPaddOo T)
  · exact sound_rPaddOi (ms_rPaddOi T)
  · exact sound_rPaddIo (ms_rPaddIo T)
  · exact sound_rPaddIi (ms_rPaddIi T)

theorem paddcRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ paddcRules) : RuleMeaningSound T r := by
  simp only [paddcRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rPaddc11 (ms_rPaddc11 T)
  · exact sound_rPaddc1o (ms_rPaddc1o T)
  · exact sound_rPaddc1i (ms_rPaddc1i T)
  · exact sound_rPaddcO1 (ms_rPaddcO1 T)
  · exact sound_rPaddcI1 (ms_rPaddcI1 T)
  · exact sound_rPaddcOo (ms_rPaddcOo T)
  · exact sound_rPaddcOi (ms_rPaddcOi T)
  · exact sound_rPaddcIo (ms_rPaddcIo T)
  · exact sound_rPaddcIi (ms_rPaddcIi T)

theorem naddRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ naddRules) : RuleMeaningSound T r := by
  simp only [naddRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sound_rNadd0l (ms_rNadd0l T)
  · exact sound_rNadd0r (ms_rNadd0r T)
  · exact sound_rNaddPp (ms_rNaddPp T)

theorem orderRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ orderRules) : RuleMeaningSound T r := by
  simp only [orderRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rNlt (ms_rNlt T)
  · exact sound_rNle (ms_rNle T)
  · exact sound_rNmonusLe (ms_rNmonusLe T)
  · exact sound_rNmonusGt (ms_rNmonusGt T)
  · exact sound_rNmaxLe (ms_rNmaxLe T)
  · exact sound_rNmaxGt (ms_rNmaxGt T)
  · exact sound_rBorFf (ms_rBorFf T)
  · exact sound_rBorFt (ms_rBorFt T)
  · exact sound_rBorTf (ms_rBorTf T)
  · exact sound_rBorTt (ms_rBorTt T)

theorem wordRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ wordRules) : RuleMeaningSound T r := by
  simp only [wordRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact sound_rPbits1 (ms_rPbits1 T)
  · exact sound_rPbitsO (ms_rPbitsO T)
  · exact sound_rPbitsI (ms_rPbitsI T)
  · exact sound_rNword0 (ms_rNword0 T)
  · exact sound_rNwordP (ms_rNwordP T)

theorem mulRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ mulRules) : RuleMeaningSound T r := by
  simp only [mulRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rPmul1 (ms_rPmul1 T)
  · exact sound_rPmulO (ms_rPmulO T)
  · exact sound_rPmulI (ms_rPmulI T)
  · exact sound_rNmul0l (ms_rNmul0l T)
  · exact sound_rNmul0r (ms_rNmul0r T)
  · exact sound_rNmulPp (ms_rNmulPp T)
  · exact sound_rNdivmod (ms_rNdivmod T)
  · exact sound_rNmod64 (ms_rNmod64 T)

theorem listRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ listRules) : RuleMeaningSound T r := by
  simp only [listRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rLenNil (ms_rLenNil T)
  · exact sound_rLenCons (ms_rLenCons T)
  · exact sound_rNth0 (ms_rNth0 T)
  · exact sound_rNthS (ms_rNthS T)
  · exact sound_rBytesNil (ms_rBytesNil T)
  · exact sound_rBytesCons (ms_rBytesCons T)

theorem termRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ termRules) : RuleMeaningSound T r := by
  simp only [termRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rWfBvar (ms_rWfBvar T)
  · exact sound_rWfLit (ms_rWfLit T)
  · exact sound_rWfApp (ms_rWfApp T)
  · exact sound_rWfargsNil (ms_rWfargsNil T)
  · exact sound_rWfargsCons (ms_rWfargsCons T)
  · exact sound_rKindfvConst (ms_rKindfvConst T)
  · exact sound_rKindfvFvar (ms_rKindfvFvar T)
  · exact sound_rDepthBvar (ms_rDepthBvar T)
  · exact sound_rDepthLit (ms_rDepthLit T)
  · exact sound_rDepthApp (ms_rDepthApp T)
  · exact sound_rHasfvBvar (ms_rHasfvBvar T)
  · exact sound_rHasfvLit (ms_rHasfvLit T)
  · exact sound_rHasfvApp (ms_rHasfvApp T)
  · exact sound_rAnnargsNil (ms_rAnnargsNil T)
  · exact sound_rAnnargsCons (ms_rAnnargsCons T)

theorem shiftRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ shiftRules) : RuleMeaningSound T r := by
  simp only [shiftRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rShiftZero (ms_rShiftZero T)
  · exact sound_rShiftLow (ms_rShiftLow T)
  · exact sound_rShiftBvar (ms_rShiftBvar T)
  · exact sound_rShiftApp (ms_rShiftApp T)
  · exact sound_rShiftargsNil (ms_rShiftargsNil T)
  · exact sound_rShiftargsCons (ms_rShiftargsCons T)

theorem substRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ substRules) : RuleMeaningSound T r := by
  simp only [substRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rSubstLow (ms_rSubstLow T)
  · exact sound_rSubstParam (ms_rSubstParam T)
  · exact sound_rSubstAbove (ms_rSubstAbove T)
  · exact sound_rSubstApp (ms_rSubstApp T)
  · exact sound_rSubstargsNil (ms_rSubstargsNil T)
  · exact sound_rSubstargsCons (ms_rSubstargsCons T)
  · exact sound_rSubsttop0 (ms_rSubsttop0 T)
  · exact sound_rSubsttopP (ms_rSubsttopP T)

theorem instRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ instRules) : RuleMeaningSound T r := by
  simp only [instRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rInstNofv (ms_rInstNofv T)
  · exact sound_rInstConst (ms_rInstConst T)
  · exact sound_rInstOtherLt (ms_rInstOtherLt T)
  · exact sound_rInstOtherGt (ms_rInstOtherGt T)
  · exact sound_rInstHit (ms_rInstHit T)
  · exact sound_rInstargsNil (ms_rInstargsNil T)
  · exact sound_rInstargsCons (ms_rInstargsCons T)

theorem literalRules_meaningSound (T : Theory)
    {r : FORule} (hr : r ∈ literalRules) : RuleMeaningSound T r := by
  simp only [literalRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sound_rNatlitSmall (ms_rNatlitSmall T)
  · exact sound_rNatlitLarge (ms_rNatlitLarge T)

theorem theoremRules_meaningSound (T : Theory) (hb : BuiltinsFixed T.sig)
    {r : FORule} (hr : r ∈ theoremRules) : RuleMeaningSound T r := by
  simp only [theoremRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rMp (ms_rMp T)
  · exact sound_rInst (ms_rInst T)
  · exact sound_rLitIsnat (ms_rLitIsnat (T := T) hb)
  · exact sound_rLitLt (ms_rLitLt (T := T) hb)
  · exact sound_rLitAdd (ms_rLitAdd (T := T) hb)
  · exact sound_rLitMul (ms_rLitMul (T := T) hb)
  · exact sound_rLitDiv (ms_rLitDiv (T := T) hb)
  · exact sound_rLitLength (ms_rLitLength (T := T) hb)
  · exact sound_rLitGet (ms_rLitGet (T := T) hb)

theorem definitionRules_meaningSound (T : Theory) (hb : BuiltinsFixed T.sig) (hf : FvarsBindNothing T.sig)
    {r : FORule} (hr : r ∈ definitionRules) : RuleMeaningSound T r := by
  simp only [definitionRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_rAritiesNil (ms_rAritiesNil T)
  · exact sound_rAritiesCons (ms_rAritiesCons T)
  · exact sound_rHintsinNil (ms_rHintsinNil T)
  · exact sound_rHintsinCons (ms_rHintsinCons T)
  · exact sound_rOccBvar (ms_rOccBvar T)
  · exact sound_rOccLit (ms_rOccLit T)
  · exact sound_rOccConst (ms_rOccConst T)
  · exact sound_rOccFvar (ms_rOccFvar T)
  · exact sound_rOccargsNil (ms_rOccargsNil T)
  · exact sound_rOccargsCons (ms_rOccargsCons T)
  · exact sound_rDesc0 (ms_rDesc0 T)
  · exact sound_rDescS (ms_rDescS T)
  · exact sound_rEtasNil (ms_rEtasNil T)
  · exact sound_rEtasCons (ms_rEtasCons T hf)
  · exact sound_rDefstmt (ms_rDefstmt T hb)

theorem arithmeticRules_meaningSound (T : Theory) {r : FORule}
    (hr : r ∈ arithmeticRules) : RuleMeaningSound T r := by
  simp only [arithmeticRules, List.mem_append, or_assoc] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr
  · exact psuccRules_meaningSound T hr
  · exact paddRules_meaningSound T hr
  · exact paddcRules_meaningSound T hr
  · exact naddRules_meaningSound T hr
  · exact orderRules_meaningSound T hr
  · exact wordRules_meaningSound T hr
  · exact mulRules_meaningSound T hr

/-- Induction over real first-order derivations, with a semantic fact for
every rule instance of the supplied package. -/
theorem FODerivable.meaning {T : Theory} {R : List FORule} {goal : Pattern}
    (hsound : ∀ r ∈ R, RuleMeaningSound T r)
    (derivation : FODerivable R goal) : Meaning T goal := by
  induction derivation with
  | rule r hr args hlen _ _ ih => exact hsound r hr args hlen ih

end Mettapedia.Languages.VibeITP.Presentation
