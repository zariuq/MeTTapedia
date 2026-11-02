import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PaperMap

/-!
# MeTTa-Calculus Regression Corpus

Focused positive/negative regression corpus with exact expected outputs.
`reg_*_raw_exact` capture raw list-level enumerator behavior, while
`reg_*_exact` use canonical duplicate-insensitive outputs.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

/-- Positive COMM raw regression: symmetric duplicate witness in list output. -/
theorem reg_comm_raw_exact :
    step demoCommSource = [demoCommTarget, demoCommTarget] := by
  decide +kernel

/-- Positive COMM canonical regression: duplicate-insensitive singleton target. -/
theorem reg_comm_exact :
    stepCanonical demoCommSource = ({demoCommTarget} : Finset Proc) := by
  decide +kernel

/-- Negative COMM raw regression: mismatched terms produce no result. -/
theorem reg_comm_blocked_raw_exact :
    step demoBlocked = [] := by
  decide +kernel

/-- Negative COMM canonical regression: empty canonical output. -/
theorem reg_comm_blocked_exact :
    stepCanonical demoBlocked = (∅ : Finset Proc) := by
  decide +kernel

/-- Positive REFL raw regression: symmetric duplicate witness in list output. -/
theorem reg_refl_raw_exact :
    step demoReflectSource = [demoReflectTarget, demoReflectTarget] := by
  decide +kernel

/-- Positive REFL canonical regression: duplicate-insensitive singleton target. -/
theorem reg_refl_exact :
    stepCanonical demoReflectSource = ({demoReflectTarget} : Finset Proc) := by
  decide +kernel

/-- Negative REFL raw regression: non-stepping body produces no reflection result. -/
theorem reg_refl_blocked_raw_exact :
    step (pReflect demoChan demoBlocked) = [] := by
  decide +kernel

/-- Negative REFL canonical regression: empty canonical output. -/
theorem reg_refl_blocked_exact :
    stepCanonical (pReflect demoChan demoBlocked) = (∅ : Finset Proc) := by
  decide +kernel

/-- Context regression: COMM fires inside a parallel bag context at one position. -/
def regContextSource : Proc := pPar [demoCommSource, pZero]
def regContextTarget : Proc := pPar [demoCommTarget, pZero]

theorem reg_context_raw_exact :
    step regContextSource = [regContextTarget, regContextTarget] := by
  decide +kernel

theorem reg_context_exact :
    stepCanonical regContextSource = ({regContextTarget} : Finset Proc) := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
