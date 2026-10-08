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

/- sameOut root sameOut_j33 calls 34 -/
theorem sameOut_j0 : run .static noProg 10 [0] (Store.empty) (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))))) = some [(.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))))), Store.empty)] := by
  rfl

theorem sameOut_j1 : run .static noProg 10 [1] (Store.empty) (.sym Sy.n99) = some [(.sym Sy.n99, Store.empty)] := by
  rfl

theorem sameOut_j2 : run .static noProg 9 [2, 0] (Store.empty) (.sym Sy.n99) = some [(.sym Sy.n99, Store.empty)] := by
  rfl

theorem sameOut_j3 : run .static noProg 8 [2, 1, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) = some [(.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2)))), (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j4 : run .static noProg 8 [2, 1, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))), (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j5 : run .static noProg 5 [2, 1, 2, 0, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.Pair) = some [(.sym Sy.Pair, (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j6 : run .static noProg 4 [2, 1, 2, 0, 1, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))), (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j7 : run .static noProg 4 [2, 1, 2, 0, 1, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.n1) = some [(.sym Sy.n1, (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j8 : run .static noProg 3 [2, 1, 2, 0, 1, 2, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) = some [(.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j9 : run .static noProg 3 [2, 1, 2, 0, 1, 2, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.n1) = some [(.sym Sy.n1, (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j10 : run .static noProg 2 [2, 1, 2, 0, 1, 2, 2, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.n1) = some [(.sym Sy.n1, (fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j11 : run .static noProg 1 [2, 1, 2, 0, 1, 2, 2, 1, 0] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.g) = some [(.sym Sy.g, (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j12 : run .static noProg 1 [2, 1, 2, 0, 1, 2, 2, 1, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) = some [(.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j13 : run .static noProg 2 [2, 1, 2, 0, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 2 [2, 1, 2, 0, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 1) [2, 1, 2, 0, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j11]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j12]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem sameOut_j14 : run .static noProg 3 [2, 1, 2, 0, 1, 2, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 3 [2, 1, 2, 0, 1, 2, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) = step .static noProg (run .static noProg 2) [2, 1, 2, 0, 1, 2, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j10]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [sameOut_j13]

theorem sameOut_j15 : run .static noProg 4 [2, 1, 2, 0, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.sym Sy.n1)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 4 [2, 1, 2, 0, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 3) [2, 1, 2, 0, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j8]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j9]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [sameOut_j14]

theorem sameOut_j16 : run .static noProg 5 [2, 1, 2, 0, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 5 [2, 1, 2, 0, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 4) [2, 1, 2, 0, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j6]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j7]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [sameOut_j15]

theorem sameOut_j17 : run .static noProg 6 [2, 1, 2, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) = some [(.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 6 [2, 1, 2, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) = step .static noProg (run .static noProg 5) [2, 1, 2, 0] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j5]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j16]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem sameOut_j18 : run .static noProg 5 [2, 1, 2, 1, 0] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j19 : run .static noProg 5 [2, 1, 2, 1, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j20 : run .static noProg 4 [2, 1, 2, 1, 2, 0] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) = some [(.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j21 : run .static noProg 4 [2, 1, 2, 1, 2, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j22 : run .static noProg 3 [2, 1, 2, 1, 2, 2, 0] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j23 : run .static noProg 2 [2, 1, 2, 1, 2, 2, 1, 0] ((fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.sym Sy.g) = some [(.sym Sy.g, (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j24 : run .static noProg 2 [2, 1, 2, 1, 2, 2, 1, 1] ((fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) = some [(.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rfl

theorem sameOut_j25 : run .static noProg 3 [2, 1, 2, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 3 [2, 1, 2, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 2) [2, 1, 2, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j23]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j24]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem sameOut_j26 : run .static noProg 4 [2, 1, 2, 1, 2, 2] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 4 [2, 1, 2, 1, 2, 2] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) = step .static noProg (run .static noProg 3) [2, 1, 2, 1, 2, 2] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j22]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [sameOut_j25]

theorem sameOut_j27 : run .static noProg 5 [2, 1, 2, 1, 2] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.sym Sy.n2)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 5 [2, 1, 2, 1, 2] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 4) [2, 1, 2, 1, 2] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j20]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j21]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [sameOut_j26]

theorem sameOut_j28 : run .static noProg 6 [2, 1, 2, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 6 [2, 1, 2, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 5) [2, 1, 2, 1] ((fun n => if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j18]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j19]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [sameOut_j27]

theorem sameOut_j29 : run .static noProg 7 [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 7 [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2))) = step .static noProg (run .static noProg 6) [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j17]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j28]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem sameOut_j30 : run .static noProg 8 [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.sym Sy.n2)))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 8 [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.sym Sy.n2)))) = step .static noProg (run .static noProg 7) [2, 1, 2] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.letP (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2, 1, 2] (.src ([2, 2], Sp.f)))) (.sym Sy.n2)))) from rfl]
  simp only [step, letLam?]
  simp only [subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [sameOut_j29]

theorem sameOut_j31 : run .static noProg 9 [2, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 9 [2, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))) = step .static noProg (run .static noProg 8) [2, 1] ((fun n => if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none)) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j3]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j4]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [sameOut_j30]

theorem sameOut_j32 : run .static noProg 10 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.y)))) (.sym Sy.n99) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 10 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.y)))) (.sym Sy.n99) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))))) = step .static noProg (run .static noProg 9) [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.y)))) (.sym Sy.n99) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j2]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [sameOut_j31]

theorem sameOut_j33 : run .static noProg 11 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))))) (.sym Sy.n99)) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show run .static noProg 11 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))))) (.sym Sy.n99)) = step .static noProg (run .static noProg 10) [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))))) (.sym Sy.n99)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [sameOut_j0]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [sameOut_j1]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [sameOut_j32]

theorem sameOut_run : run .static noProg 11 [] Store.empty (elabCfg cfgLF [] sameOut) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 1, 2, 0, 1, 2, 2] (.src ([2, 1, 0, 2], Sp.y)) then some (.sym Sy.n1) else if n = .inst [2] (.src ([2], Sp.y)) then some (.sym Sy.n99) else none))] := by
  rw [show elabCfg cfgLF [] sameOut = (.app (.lam (.src ([2, 7], Sp.y)) [([2], Sp.y)] (.letP (.var (.src ([2], Sp.y))) (.pvar (.src ([2, 7], Sp.y))) (.app (.lam (.src ([2, 2, 7], Sp.f)) [([2, 2], Sp.f)] (.letP (.var (.src ([2, 2], Sp.f))) (.pvar (.src ([2, 2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2, 2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([2, 1, 0, 2, 7], Sp.y)) [([2, 1, 0, 2], Sp.y)] (.letP (.var (.src ([2, 1, 0, 2], Sp.y))) (.pvar (.src ([2, 1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([2, 1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))))) (.sym Sy.n99)) from rfl]
  exact sameOut_j33

theorem sameOut_answers : answers .static noProg 11 (elabCfg cfgLF [] sameOut) = some [.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.sym Sy.n1))) (.app (.sym Sy.g) (.sym Sy.n2))] := by
  unfold answers
  rw [sameOut_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

theorem sameOut_bag : bag cfgLF sameOut = some [.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.sym Sy.n1))) (.app (.sym Sy.g) (.sym Sy.n2))] := by
  unfold bag answersCfg answers
  rw [show cfgLF.disc = .static from rfl]
  rw [run_mono .static noProg (by decide : 11 ≤ 16) sameOut_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
