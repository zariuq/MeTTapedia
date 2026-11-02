import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance
import Mettapedia.OSLF.MeTTaIL.CanonicalBags

/-! Canonical bag/set arrangement fixes constructor and ordered-vector
terms. This is a shape property independent of any language instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax

theorem VectorFirstOrder.canon_fixed {pattern : Pattern} (shape : VectorFirstOrder pattern) :
    CanonicalBags.canon pattern = pattern := by
  induction shape with
  | metavariable name => simp only [CanonicalBags.canon]
  | constructor label arguments _ ih =>
    rw [CanonicalBags.canon_apply]
    congr 1
    exact (List.map_congr_left (fun child member => ih child member)).trans (by simp)
  | vector arguments _ ih =>
    simp only [CanonicalBags.canon, CanonicalBags.arrange_vec]
    congr 1
    exact (List.map_congr_left (fun child member => ih child member)).trans (by simp)

#print axioms VectorFirstOrder.canon_fixed

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
