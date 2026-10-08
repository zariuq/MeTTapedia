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

/- escapingDistinct root escapingDistinct_j38 calls 39 -/
theorem escapingDistinct_j0 : run .static noProg 8 [0] (Store.empty) (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)) (.sym Sy.n8))))) = some [(.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)) (.sym Sy.n8)))), Store.empty)] := by
  rfl

theorem escapingDistinct_j1 : run .static noProg 8 [1] (Store.empty) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z)))), Store.empty)] := by
  rfl

theorem escapingDistinct_j2 : run .static noProg 5 [2, 0, 0] (Store.empty) (.sym Sy.Pair) = some [(.sym Sy.Pair, Store.empty)] := by
  rfl

theorem escapingDistinct_j3 : run .static noProg 3 [2, 0, 1, 0, 0] (Store.empty) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z)))), Store.empty)] := by
  rfl

theorem escapingDistinct_j4 : run .static noProg 3 [2, 0, 1, 0, 1] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem escapingDistinct_j5 : run .static noProg 2 [2, 0, 1, 0, 2, 0] (Store.empty) (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) = some [(.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w)))))), Store.empty)] := by
  rfl

theorem escapingDistinct_j6 : run .static noProg 2 [2, 0, 1, 0, 2, 1] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem escapingDistinct_j7 : run .static noProg 1 [2, 0, 1, 0, 2, 2, 0] (Store.empty) (.sym Sy.n1) = some [(.sym Sy.n1, Store.empty)] := by
  rfl

theorem escapingDistinct_j8 : run .static noProg 1 [2, 0, 1, 0, 2, 2, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w))))) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j9 : run .static noProg 2 [2, 0, 1, 0, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n1) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))))) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 2 [2, 0, 1, 0, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n1) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))))) = step .static noProg (run .static noProg 1) [2, 0, 1, 0, 2, 2] (Store.empty) (.letP (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n1) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j7]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, ↓reduceIte]
  repeat rw [if_neg (by decide)]
  rfl

theorem escapingDistinct_j10 : run .static noProg 3 [2, 0, 1, 0, 2] (Store.empty) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.sym Sy.n1)) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 3 [2, 0, 1, 0, 2] (Store.empty) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 2) [2, 0, 1, 0, 2] (Store.empty) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j5]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j6]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j9]

theorem escapingDistinct_j11 : run .static noProg 4 [2, 0, 1, 0] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 0, 1, 0] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) = step .static noProg (run .static noProg 3) [2, 0, 1, 0] (Store.empty) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j3]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j4]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j10]

theorem escapingDistinct_j12 : run .static noProg 4 [2, 0, 1, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n7) = some [(.sym Sy.n7, (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j13 : run .static noProg 2 [2, 0, 1, 2, 0, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.Pair) = some [(.sym Sy.Pair, (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j14 : run .static noProg 2 [2, 0, 1, 2, 0, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) = some [(.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j15 : run .static noProg 3 [2, 0, 1, 2, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) = some [(.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 3 [2, 0, 1, 2, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 2) [2, 0, 1, 2, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j13]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j14]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem escapingDistinct_j16 : run .static noProg 3 [2, 0, 1, 2, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n7) = some [(.sym Sy.n7, (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j17 : run .static noProg 4 [2, 0, 1, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7)) = some [(.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 0, 1, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7)) = step .static noProg (run .static noProg 3) [2, 0, 1, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j15]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j16]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem escapingDistinct_j18 : run .static noProg 5 [2, 0, 1] (Store.empty) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7)) = some [(.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 5 [2, 0, 1] (Store.empty) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7)) = step .static noProg (run .static noProg 4) [2, 0, 1] (Store.empty) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j11]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j12]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j17]

theorem escapingDistinct_j19 : run .static noProg 6 [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7))) = some [(.app (.sym Sy.Pair) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7)), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 6 [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7))) = step .static noProg (run .static noProg 5) [2, 0] (Store.empty) (.app (.sym Sy.Pair) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j2]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j18]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem escapingDistinct_j20 : run .static noProg 4 [2, 1, 0, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) = some [(.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z)))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j21 : run .static noProg 4 [2, 1, 0, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j22 : run .static noProg 3 [2, 1, 0, 2, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) = some [(.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w)))))), (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j23 : run .static noProg 3 [2, 1, 0, 2, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j24 : run .static noProg 2 [2, 1, 0, 2, 2, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n2) = some [(.sym Sy.n2, (fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j25 : run .static noProg 2 [2, 1, 0, 2, 2, 1] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w))))) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j26 : run .static noProg 3 [2, 1, 0, 2, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n2) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))))) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 3 [2, 1, 0, 2, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n2) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))))) = step .static noProg (run .static noProg 2) [2, 1, 0, 2, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.letP (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) (.sym Sy.n2) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))))) from rfl]
  simp only [step, letLam?]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j24]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [act, envSub, subst, Sub.none, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Tm.toGVal?, GVal.toTm, matchT, refineStep, ↓reduceIte]
  repeat rw [if_neg (by decide)]
  rfl

theorem escapingDistinct_j27 : run .static noProg 4 [2, 1, 0, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.sym Sy.n2)) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 1, 0, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 3) [2, 1, 0, 2] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j22]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j23]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j26]

theorem escapingDistinct_j28 : run .static noProg 5 [2, 1, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) = some [(.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.pvar (.src ([], Sp.w)))), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 5 [2, 1, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) = step .static noProg (run .static noProg 4) [2, 1, 0] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j20]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j21]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j27]

theorem escapingDistinct_j29 : run .static noProg 5 [2, 1, 1] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n8) = some [(.sym Sy.n8, (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j30 : run .static noProg 3 [2, 1, 2, 0, 0] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.Pair) = some [(.sym Sy.Pair, (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j31 : run .static noProg 3 [2, 1, 2, 0, 1] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))) = some [(.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j32 : run .static noProg 4 [2, 1, 2, 0] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) = some [(.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)))), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 4 [2, 1, 2, 0] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) = step .static noProg (run .static noProg 3) [2, 1, 2, 0] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j30]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j31]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem escapingDistinct_j33 : run .static noProg 4 [2, 1, 2, 1] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.sym Sy.n8) = some [(.sym Sy.n8, (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rfl

theorem escapingDistinct_j34 : run .static noProg 5 [2, 1, 2] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8)) = some [(.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 5 [2, 1, 2] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8)) = step .static noProg (run .static noProg 4) [2, 1, 2] ((fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j32]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j33]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem escapingDistinct_j35 : run .static noProg 6 [2, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) (.sym Sy.n8)) = some [(.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 6 [2, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) (.sym Sy.n8)) = step .static noProg (run .static noProg 5) [2, 1] ((fun n => if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none)) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) (.sym Sy.n8)) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j28]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j29]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j34]

theorem escapingDistinct_j36 : run .static noProg 7 [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) (.sym Sy.n8))) = some [(.app (.app (.sym Sy.Pair) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7))) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8)), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 7 [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) (.sym Sy.n8))) = step .static noProg (run .static noProg 6) [2] (Store.empty) (.app (.app (.sym Sy.Pair) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.sym Sy.n2)) (.sym Sy.n8))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j19]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j35]
  simp only [bindOpt_some_singleton, bindAll_singleton]

theorem escapingDistinct_j37 : run .static noProg 8 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)) (.sym Sy.n8)))) = some [(.app (.app (.sym Sy.Pair) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7))) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8)), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 8 [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)) (.sym Sy.n8)))) = step .static noProg (run .static noProg 7) [2] (Store.empty) (.letP (.var (.inst [2] (.src ([2], Sp.f)))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z))))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.inst [2] (.src ([2], Sp.f)))) (.sym Sy.n2)) (.sym Sy.n8)))) from rfl]
  simp only [step, letLam?]
  simp only [subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j36]

theorem escapingDistinct_j38 : run .static noProg 9 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)) (.sym Sy.n8))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z)))))) = some [(.app (.app (.sym Sy.Pair) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7))) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8)), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show run .static noProg 9 [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)) (.sym Sy.n8))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z)))))) = step .static noProg (run .static noProg 8) [] (Store.empty) (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)) (.sym Sy.n8))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z)))))) from rfl]
  simp only [step]
  simp only [List.nil_append, List.cons_append]
  rw [escapingDistinct_j0]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  rw [escapingDistinct_j1]
  simp only [bindOpt_some_singleton, bindAll_singleton]
  simp only [activate, renameOwn, subst, Sub.single, Sub.hideOwn, Sub.hideParam, Sub.none, Option.getD_some, Option.getD_none]
  repeat (first | rw [if_pos (by decide)] | rw [if_neg (by decide)])
  try simp only [↓reduceIte]
  simp only [gdSome, gdNone]
  rw [escapingDistinct_j37]

theorem escapingDistinct_run : run .static noProg 9 [] Store.empty (elabCfg cfgLF [] escapingDistinct) = some [(.app (.app (.sym Sy.Pair) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n7))) (.app (.app (.sym Sy.Pair) (.var (.inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y))))) (.sym Sy.n8)), (fun n => if n = .inst [2, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n2) else if n = .inst [2, 0, 1, 0, 2, 2] (.src ([1, 0, 2], Sp.y)) then some (.sym Sy.n1) else none))] := by
  rw [show elabCfg cfgLF [] escapingDistinct = (.app (.lam (.src ([2, 7], Sp.f)) [([2], Sp.f)] (.letP (.var (.src ([2], Sp.f))) (.pvar (.src ([2, 7], Sp.f))) (.app (.app (.sym Sy.Pair) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.var (.src ([2], Sp.f))) (.sym Sy.n2)) (.sym Sy.n8))))) (.lam (.src ([], Sp.z)) [] (.app (.lam (.src ([1, 0, 2, 7], Sp.y)) [([1, 0, 2], Sp.y)] (.letP (.var (.src ([1, 0, 2], Sp.y))) (.pvar (.src ([1, 0, 2, 7], Sp.y))) (.lam (.src ([], Sp.w)) [] (.app (.app (.sym Sy.Pair) (.var (.src ([1, 0, 2], Sp.y)))) (.pvar (.src ([], Sp.w))))))) (.pvar (.src ([], Sp.z)))))) from rfl]
  exact escapingDistinct_j38

theorem escapingDistinct_answers : answers .static noProg 9 (elabCfg cfgLF [] escapingDistinct) = some [.app (.app (.sym Sy.Pair) (.app (.app (.sym Sy.Pair) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.sym Sy.Pair) (.sym Sy.n2)) (.sym Sy.n8))] := by
  unfold answers
  rw [escapingDistinct_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

theorem escapingDistinct_bag : bag cfgLF escapingDistinct = some [.app (.app (.sym Sy.Pair) (.app (.app (.sym Sy.Pair) (.sym Sy.n1)) (.sym Sy.n7))) (.app (.app (.sym Sy.Pair) (.sym Sy.n2)) (.sym Sy.n8))] := by
  unfold bag answersCfg answers
  rw [show cfgLF.disc = .static from rfl]
  rw [run_mono .static noProg (by decide : 9 ≤ 16) escapingDistinct_run]
  simp only [List.map, act, envSub, subst, Sub.none, Option.getD_some, Option.getD_none, ↓reduceIte, Store.empty]
  rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
