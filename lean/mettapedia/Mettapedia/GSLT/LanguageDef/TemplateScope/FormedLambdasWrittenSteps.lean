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

/- writtenOwns root writtenOwns_j28 calls 29 -/
theorem writtenOwns_j0 : run .static noProg 8 [0] (Store.empty) (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) = some [(.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)))), Store.empty)] := by
  rfl

theorem writtenOwns_j1 : run .static noProg 8 [1] (Store.empty) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))), Store.empty)] := by
  rfl

theorem writtenOwns_j2 : run .static noProg 5 [2, 0, 0] (Store.empty) (.sym Sy.Pair) = some [(.sym Sy.Pair, Store.empty)] := by
  rfl

theorem writtenOwns_j3 : run .static noProg 4 [2, 0, 1, 0] (Store.empty) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))), Store.empty)] := by
  rfl

theorem writtenOwns_j4 : run .static noProg 4 [2, 0, 1, 1] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem writtenOwns_j5 : run .static noProg 3 [2, 0, 1, 2, 0] (Store.empty) (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) = some [(.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y))))), Store.empty)] := by
  rfl

theorem writtenOwns_j6 : run .static noProg 3 [2, 0, 1, 2, 1] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem writtenOwns_j7 : run .static noProg 2 [2, 0, 1, 2, 2, 0] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem writtenOwns_j8 : run .static noProg 1 [2, 0, 1, 2, 2, 1, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.g) = some [(.sym Sy.g, (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j9 : run .static noProg 1 [2, 0, 1, 2, 2, 1, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) = some [(.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j10 : run .static noProg 2 [2, 0, 1, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 2 [2, 0, 1, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 1) [2, 0, 1, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j8]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j9]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem writtenOwns_j11 : run .static noProg 3 [2, 0, 1, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 3 [2, 0, 1, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) = step .static noProg (run .static noProg 2) [2, 0, 1, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n1) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j7]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [writtenOwns_j10]

theorem writtenOwns_j12 : run .static noProg 4 [2, 0, 1, 2] (Store.empty) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.sym Sy.n1)) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 0, 1, 2] (Store.empty) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 3) [2, 0, 1, 2] (Store.empty) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j5]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j6]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [writtenOwns_j11]

theorem writtenOwns_j13 : run .static noProg 5 [2, 0, 1] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) = some [(.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 5 [2, 0, 1] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 4) [2, 0, 1] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j3]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j4]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [writtenOwns_j12]

theorem writtenOwns_j14 : run .static noProg 6 [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) = some [(.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 6 [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) = step .static noProg (run .static noProg 5) [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j2]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j13]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem writtenOwns_j15 : run .static noProg 5 [2, 1, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j16 : run .static noProg 5 [2, 1, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j17 : run .static noProg 4 [2, 1, 2, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) = some [(.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j18 : run .static noProg 4 [2, 1, 2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j19 : run .static noProg 3 [2, 1, 2, 2, 0] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j20 : run .static noProg 2 [2, 1, 2, 2, 1, 0] ((fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.g) = some [(.sym Sy.g, (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j21 : run .static noProg 2 [2, 1, 2, 2, 1, 1] ((fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) = some [(.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem writtenOwns_j22 : run .static noProg 3 [2, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 3 [2, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 2) [2, 1, 2, 2, 1] ((fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j20]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j21]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem writtenOwns_j23 : run .static noProg 4 [2, 1, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 1, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) = step .static noProg (run .static noProg 3) [2, 1, 2, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n2) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j19]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, Store.empty, ↓reduceIte]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  rw [writtenOwns_j22]

theorem writtenOwns_j24 : run .static noProg 5 [2, 1, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.sym Sy.n2)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 5 [2, 1, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 4) [2, 1, 2] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j17]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j18]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [writtenOwns_j23]

theorem writtenOwns_j25 : run .static noProg 6 [2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) = some [(.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 6 [2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 5) [2, 1] ((fun n => if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j15]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j16]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [writtenOwns_j24]

theorem writtenOwns_j26 : run .static noProg 7 [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 7 [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2))) = step .static noProg (run .static noProg 6) [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1))) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j14]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j25]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem writtenOwns_j27 : run .static noProg 8 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 8 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)))) = step .static noProg (run .static noProg 7) [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1))) (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)))) from rfl]
  simp only [step, letLam?]
  simp only [subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [writtenOwns_j26]

theorem writtenOwns_j28 : run .static noProg 9 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 9 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))) = step .static noProg (run .static noProg 8) [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [writtenOwns_j0]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [writtenOwns_j1]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [writtenOwns_j27]

theorem writtenOwns_run : run .static noProg 9 [] Store.empty (elabCfg cfgLF [] writtenOwns) = some [(.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.var (.inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)))))) (.app (.sym Sy.g) (.var (.inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y))))), (fun n => if n = .inst [2, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show elabCfg cfgLF [] writtenOwns = (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1))) (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.app (.sym Sy.g) (.var (.src ([1, 0, 2], Sp.y)))))) (.pvar (.src ([], Sp.z)))))) from rfl]
  exact writtenOwns_j28

theorem writtenOwns_answers : answers .static noProg 9 (elabCfg cfgLF [] writtenOwns) = some [.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.sym Sy.n1))) (.app (.sym Sy.g) (.sym Sy.n2))] := by
  unfold answers
  rw [writtenOwns_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

theorem writtenOwns_bag : bag cfgLF writtenOwns = some [.app (.app (.sym Sy.Pair) (.app (.sym Sy.g) (.sym Sy.n1))) (.app (.sym Sy.g) (.sym Sy.n2))] := by
  unfold bag answersCfg answers
  rw [show cfgLF.disc = .static from rfl]
  rw [run_mono .static noProg (by decide : 9 ≤ 16) writtenOwns_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
