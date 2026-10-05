import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionPaths
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context

/-!
# Positive paths in flat parallel contexts

Flattening a nested parallel bag at any position preserves structural
congruence. A positive reduction path can therefore be spliced into a flat
parallel context without changing its step count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem StructuralCongruence.flatten_at (before nested after : List Pattern) :
    StructuralCongruence
      (.collection .hashBag (before ++ [.collection .hashBag nested none] ++ after) none)
      (.collection .hashBag (before ++ nested ++ after) none) := by
  have moveToHead : (before ++ [Pattern.collection .hashBag nested none] ++ after).Perm
      (Pattern.collection .hashBag nested none :: (before ++ after)) := by
    simpa only [List.append_assoc, List.singleton_append] using
      (List.perm_middle (a := Pattern.collection .hashBag nested none) (l₁ := before) (l₂ := after))
  refine .trans _ _ _ (StructuralCongruence.par_perm _ _ moveToHead) ?_
  refine .trans _ _ _ (Context.par_flatten_head nested (before ++ after)) ?_
  apply StructuralCongruence.par_perm
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := nested) (l₂ := before)).append_right after

noncomputable def ReducesN.splice {count : Nat} {source target : List Pattern}
    (path : ReducesN (count + 1) (.collection .hashBag source none)
      (.collection .hashBag target none)) (before after : List Pattern) :
    ReducesN (count + 1) (.collection .hashBag (before ++ source ++ after) none)
      (.collection .hashBag (before ++ target ++ after) none) :=
  (path.par_any_pos (before := before) (after := after)).transport
    (.symm _ _ (StructuralCongruence.flatten_at before source after))
    (StructuralCongruence.flatten_at before target after)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
