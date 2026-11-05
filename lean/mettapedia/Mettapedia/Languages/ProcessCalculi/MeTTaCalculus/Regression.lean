import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PaperMap
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedCongruence

/-!
# MeTTa-Calculus Regression Corpus

Focused positive/negative regression corpus with exact expected outputs of the
corrected step. `reg_*_raw_exact` capture the raw list of `Corrected.cstep`,
`reg_*_exact` its duplicate-insensitive set, and `reg_*_bag_exact` the step
modulo the bag laws, `Corrected.cstepBag`, which fires COMM at any pair of
guards and so returns the reduct in both orders.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

/-- Positive COMM raw regression: the capture-free reduct `@0 | a`. -/
theorem reg_comm_raw_exact :
    Corrected.cstep demoCommSource = [demoCommReduct] := by
  decide +kernel

/-- Positive COMM canonical regression: duplicate-insensitive singleton target. -/
theorem reg_comm_exact :
    (Corrected.cstep demoCommSource).toFinset = ({demoCommReduct} : Finset Proc) := by
  decide +kernel

/-- Positive COMM regression modulo the bag laws: the reduct in both orders. -/
theorem reg_comm_bag_exact :
    Corrected.cstepBag demoCommSource =
      [pPar [demoCommReduct], pPar [par (.fvar "a") (nQuote pZero)]] := by
  decide +kernel

/-- Negative COMM raw regression: mismatched terms produce no result. -/
theorem reg_comm_blocked_raw_exact :
    Corrected.cstep demoBlocked = [] := by
  decide +kernel

/-- Negative COMM canonical regression: empty canonical output. -/
theorem reg_comm_blocked_exact :
    (Corrected.cstep demoBlocked).toFinset = (∅ : Finset Proc) := by
  decide +kernel

/-- Negative COMM regression modulo the bag laws. -/
theorem reg_comm_blocked_bag_exact :
    Corrected.cstepBag demoBlocked = [] := by
  decide +kernel

/-- Positive REFL raw regression: the listener quotes the capture-free reduct. -/
theorem reg_refl_raw_exact :
    Corrected.cstep demoReflectSource = [demoReflectReduct] := by
  decide +kernel

/-- Positive REFL canonical regression: duplicate-insensitive singleton target. -/
theorem reg_refl_exact :
    (Corrected.cstep demoReflectSource).toFinset = ({demoReflectReduct} : Finset Proc) := by
  decide +kernel

/-- Negative REFL raw regression: non-stepping body produces no reflection result. -/
theorem reg_refl_blocked_raw_exact :
    Corrected.cstep (pReflect demoChan demoBlocked) = [] := by
  decide +kernel

/-- Negative REFL canonical regression: empty canonical output. -/
theorem reg_refl_blocked_exact :
    (Corrected.cstep (pReflect demoChan demoBlocked)).toFinset = (∅ : Finset Proc) := by
  decide +kernel

/-- Context regression: COMM fires inside a parallel bag context at one position. -/
def regContextSource : Proc := pPar [demoCommSource, pZero]
def regContextTarget : Proc := pPar [demoCommReduct, pZero]

theorem reg_context_raw_exact :
    Corrected.cstep regContextSource = [regContextTarget] := by
  decide +kernel

theorem reg_context_exact :
    (Corrected.cstep regContextSource).toFinset = ({regContextTarget} : Finset Proc) := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
