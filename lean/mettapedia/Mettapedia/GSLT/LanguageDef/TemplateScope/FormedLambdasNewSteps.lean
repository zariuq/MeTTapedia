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

/- formedNew root formedNew_j34 calls 35 -/
theorem formedNew_j0 : run .static noProg 9 [0] (Store.empty) (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) = some [(.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)))), Store.empty)] := by
  rfl

theorem formedNew_j1 : run .static noProg 9 [1] (Store.empty) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))), Store.empty)] := by
  rfl

theorem formedNew_j2 : run .static noProg 6 [2, 0, 0] (Store.empty) (.sym Sy.Pair) = some [(.sym Sy.Pair, Store.empty)] := by
  rfl

theorem formedNew_j3 : run .static noProg 5 [2, 0, 1, 0] (Store.empty) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))), Store.empty)] := by
  rfl

theorem formedNew_j4 : run .static noProg 5 [2, 0, 1, 1] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem formedNew_j5 : run .static noProg 4 [2, 0, 1, 2, 0] (Store.empty) (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1))) = some [(.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1)), Store.empty)] := by
  rfl

theorem formedNew_j6 : run .static noProg 4 [2, 0, 1, 2, 1] (Store.empty) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))) = some [(.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))), Store.empty)] := by
  rfl

theorem formedNew_j7 : run .static noProg 3 [2, 0, 1, 2, 2, 0] (Store.empty) (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) = some [(.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y))))), Store.empty)] := by
  rfl

theorem formedNew_j8 : run .static noProg 3 [2, 0, 1, 2, 2, 1] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem formedNew_j9 : run .static noProg 2 [2, 0, 1, 2, 2, 2, 0] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem formedNew_j10 : run .static noProg 1 [2, 0, 1, 2, 2, 2, 1, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.g) = some [(.sym Sy.g, (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j11 : run .static noProg 1 [2, 0, 1, 2, 2, 2, 1, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) = some [(.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j12 : run .static noProg 2 [2, 0, 1, 2, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 2 [2, 0, 1, 2, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 1) [2, 0, 1, 2, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j10]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j11]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem formedNew_j13 : run .static noProg 3 [2, 0, 1, 2, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 3 [2, 0, 1, 2, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) = step .static noProg (run .static noProg 2) [2, 0, 1, 2, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j9]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [formedNew_j12]

theorem formedNew_j14 : run .static noProg 4 [2, 0, 1, 2, 2] (Store.empty) (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1)) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 0, 1, 2, 2] (Store.empty) (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 3) [2, 0, 1, 2, 2] (Store.empty) (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j7]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j8]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j13]

theorem formedNew_j15 : run .static noProg 5 [2, 0, 1, 2] (Store.empty) (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 5 [2, 0, 1, 2] (Store.empty) (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))) = step .static noProg (run .static noProg 4) [2, 0, 1, 2] (Store.empty) (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n1))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j5]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j6]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j14]

theorem formedNew_j16 : run .static noProg 6 [2, 0, 1] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1)) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 6 [2, 0, 1] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 5) [2, 0, 1] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j3]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j4]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j15]

theorem formedNew_j17 : run .static noProg 7 [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1))) = some [(.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 7 [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1))) = step .static noProg (run .static noProg 6) [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j2]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j16]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem formedNew_j18 : run .static noProg 6 [2, 1, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j19 : run .static noProg 6 [2, 1, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j20 : run .static noProg 5 [2, 1, 2, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2))) = some [(.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2)), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j21 : run .static noProg 5 [2, 1, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))) = some [(.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j22 : run .static noProg 4 [2, 1, 2, 2, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) = some [(.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j23 : run .static noProg 4 [2, 1, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j24 : run .static noProg 3 [2, 1, 2, 2, 2, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j25 : run .static noProg 2 [2, 1, 2, 2, 2, 1, 0] ((fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.g) = some [(.sym Sy.g, (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j26 : run .static noProg 2 [2, 1, 2, 2, 2, 1, 1] ((fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) = some [(.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem formedNew_j27 : run .static noProg 3 [2, 1, 2, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 3 [2, 1, 2, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 2) [2, 1, 2, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j25]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j26]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem formedNew_j28 : run .static noProg 4 [2, 1, 2, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 1, 2, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) = step .static noProg (run .static noProg 3) [2, 1, 2, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j24]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [formedNew_j27]

theorem formedNew_j29 : run .static noProg 5 [2, 1, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 5 [2, 1, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 4) [2, 1, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j22]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j23]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j28]

theorem formedNew_j30 : run .static noProg 6 [2, 1, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 6 [2, 1, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))) = step .static noProg (run .static noProg 5) [2, 1, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.sym Sy.n2))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j20]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j21]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j29]

theorem formedNew_j31 : run .static noProg 7 [2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n2)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 7 [2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 6) [2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j18]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j19]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j30]

theorem formedNew_j32 : run .static noProg 8 [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n2))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 8 [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n2))) = step .static noProg (run .static noProg 7) [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.sym Sy.n2))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j17]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j31]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem formedNew_j33 : run .static noProg 9 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 9 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)))) = step .static noProg (run .static noProg 8) [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y)))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)))) from rfl]
  simp only [step, letLam?]
  simp only [subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j32]

theorem formedNew_j34 : run .static noProg 10 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 10 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))))) = step .static noProg (run .static noProg 9) [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [formedNew_j0]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [formedNew_j1]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [formedNew_j33]

theorem formedNew_run : run .static noProg 10 [] Store.empty (elabCfg cfgLF [] formedNew) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2, 2] (.src ([1, 0, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show elabCfg cfgLF [] formedNew = (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 8], Sp.y)) [([1, 0, 0], Sp.y)] (.app (.lam (.src ([1, 0, 0, 2, 7], Sp.y)) [([1, 0, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.lam (.src ([1, 0, 8], Sp.y)) [] (.pvar (.src ([1, 0, 8], Sp.y))))))) from rfl]
  exact formedNew_j34

theorem formedNew_answers : answers .static noProg 10 (elabCfg cfgLF [] formedNew) = some [.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.sym Sy.n1))) (.app (.sym Sy.g) (.sym Sy.n2))] := by
  unfold answers
  rw [formedNew_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

theorem formedNew_bag : bag cfgLF formedNew = some [.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.sym Sy.n1))) (.app (.sym Sy.g) (.sym Sy.n2))] := by
  unfold bag answersCfg answers
  rw [show cfgLF.disc = .static from rfl]
  rw [run_mono .static noProg (by decide : 10 ≤ 16) formedNew_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
