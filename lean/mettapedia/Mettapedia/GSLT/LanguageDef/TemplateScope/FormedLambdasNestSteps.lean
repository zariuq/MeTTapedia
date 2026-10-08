import Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas

/-!
One-step kernel proofs that `bag cfgLF` equals the route answer.
Each step rewrites one call of the shipped `step`. The bag theorem
lifts that run to fuel 16 with `run_mono`.
-/

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

set_option maxHeartbeats 80000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem gdSome {α : Type} (a d : α) : (some a).getD d = a := rfl
private theorem gdNone {α : Type} (d : α) : (none : Option α).getD d = d := rfl

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas

/- nest root nest_j10 calls 11 -/
theorem nest_j0 : run .static noProg 4 [0] (Store.empty) (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.src ([2], Sp.y)))))) = some [(.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.src ([2], Sp.y))))), Store.empty)] := by
  rfl

theorem nest_j1 : run .static noProg 4 [1] (Store.empty) (.sym Sy.n7) = some [(.sym Sy.n7, Store.empty)] := by
  rfl

theorem nest_j2 : run .static noProg 3 [2, 0] (Store.empty) (.sym Sy.n7) = some [(.sym Sy.n7, Store.empty)] := by
  rfl

theorem nest_j3 : run .static noProg 2 [2, 1, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) = some [(.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y)))), (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rfl

theorem nest_j4 : run .static noProg 2 [2, 1, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.var (.inst [2] (.src ([2], Sp.y)))) = some [(.var (.inst [2] (.src ([2], Sp.y))), (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rfl

theorem nest_j5 : run .static noProg 1 [2, 1, 2, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.var (.inst [2] (.src ([2], Sp.y)))) = some [(.var (.inst [2] (.src ([2], Sp.y))), (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rfl

theorem nest_j6 : run .static noProg 1 [2, 1, 2, 1] ((fun n => if n = .inst [2, 1, 2] (.src ([2, 2], Sp.y)) then some (.sym Sy.n7) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y)))) = some [(.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2] (.src ([2, 2], Sp.y)) then some (.sym Sy.n7) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rfl

theorem nest_j7 : run .static noProg 2 [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.letP (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y)))) (.var (.inst [2] (.src ([2], Sp.y)))) (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))))) = some [(.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2] (.src ([2, 2], Sp.y)) then some (.sym Sy.n7) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rw [show run .static noProg 2 [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.letP (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y)))) (.var (.inst [2] (.src ([2], Sp.y)))) (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))))) = step .static noProg (run .static noProg 1) [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.letP (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y)))) (.var (.inst [2] (.src ([2], Sp.y)))) (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [nest_j5]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, ↓reduceIte]
  repeat rw [if_neg (by decide)]
  rfl

theorem nest_j8 : run .static noProg 3 [2, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.inst [2] (.src ([2], Sp.y))))) = some [(.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2] (.src ([2, 2], Sp.y)) then some (.sym Sy.n7) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rw [show run .static noProg 3 [2, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.inst [2] (.src ([2], Sp.y))))) = step .static noProg (run .static noProg 2) [2, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none)) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.inst [2] (.src ([2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [nest_j3]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [nest_j4]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [nest_j7]

theorem nest_j9 : run .static noProg 4 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.y)))) (.sym Sy.n7) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.inst [2] (.src ([2], Sp.y)))))) = some [(.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2] (.src ([2, 2], Sp.y)) then some (.sym Sy.n7) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rw [show run .static noProg 4 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.y)))) (.sym Sy.n7) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.inst [2] (.src ([2], Sp.y)))))) = step .static noProg (run .static noProg 3) [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.y)))) (.sym Sy.n7) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.inst [2] (.src ([2], Sp.y)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [nest_j2]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [nest_j8]

theorem nest_j10 : run .static noProg 5 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.src ([2], Sp.y)))))) (.sym Sy.n7)) = some [(.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2] (.src ([2, 2], Sp.y)) then some (.sym Sy.n7) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rw [show run .static noProg 5 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.src ([2], Sp.y)))))) (.sym Sy.n7)) = step .static noProg (run .static noProg 4) [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.src ([2], Sp.y)))))) (.sym Sy.n7)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [nest_j0]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [nest_j1]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [nest_j9]

theorem nest_run : run .static noProg 5 [] Store.empty (elabCfg cfgLF [] nest) = some [(.var (.inst [2, 1, 2] (.src ([2, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2] (.src ([2, 2], Sp.y)) then some (.sym Sy.n7) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n7) else none))] := by
  rw [show elabCfg cfgLF [] nest = (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.y)) [([2, 2], Sp.y)] (.letP (.var (.src ([2, 2], Sp.y))) (.pvar (.src ([2, 2, 7], Sp.y))) (.var (.src ([2, 2], Sp.y))))) (.var (.src ([2], Sp.y)))))) (.sym Sy.n7)) from rfl]
  exact nest_j10

theorem nest_answers : answers .static noProg 5 (elabCfg cfgLF [] nest) = some [.sym Sy.n7] := by
  unfold answers
  rw [nest_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

theorem nest_bag : bag cfgLF nest = some [.sym Sy.n7] := by
  unfold bag answersCfg answers
  rw [show cfgLF.disc = .static from rfl]
  rw [run_mono .static noProg (by decide : 5 ≤ 16) nest_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
