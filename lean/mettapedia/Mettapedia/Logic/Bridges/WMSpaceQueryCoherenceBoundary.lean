import Mettapedia.Logic.Bridges.WMMeTTaSpaceAlgebra

/-!
# Storage/query coherence does not imply additive query behavior

The MeTTa storage/query API requires an exact lookup for a designated result,
but it permits additional result relations. A coherent query can therefore
observe a multiplicity-specific result that disappears under space union.
Consequently a WM revision law for a chosen evidence extraction is an extra
backend contract, not a consequence of storage/query coherence alone.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMSpaceQueryCoherenceBoundary

open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
open Mettapedia.Logic.Bridges.WMMeTTaSpaceAlgebra

/-- `false` is the designated membership result. The additional `true`
result records exactly one occurrence and is deliberately sensitive to
multiplicity rather than only to membership. -/
def exactOneExtraResult : QueryOps (MSpace Unit) Unit Bool where
  QueryRel := fun space _ result =>
    if result then space () = 1 else 0 < space ()

/-- The extra result does not interfere with the established coherence law:
the designated lookup still sees exactly the positive multiplicity. -/
theorem exactOneExtraResult_coherent :
    QueryCoherent (multiplicitySpaceOps (Atom := Unit))
      exactOneExtraResult (fun _ => false) where
  visible_iff_present := by
    intro space atom
    cases atom
    rfl

/-- Each singleton offers the extra result, but their union does not. -/
theorem exactOneExtraResult_cross_union :
    exactOneExtraResult.QueryRel (singletonSpace ()) () true ∧
    ¬ exactOneExtraResult.QueryRel
      (sUnion (singletonSpace ()) (singletonSpace ())) () true := by
  simp [exactOneExtraResult, singletonSpace, sUnion]

/-- Even together with the counted-bag storage laws and query coherence,
arbitrary query results need not obey the union-as-disjunction law. -/
theorem coherentQuery_not_unionHomomorphic :
    ¬ ∀ first second : MSpace Unit,
      exactOneExtraResult.QueryRel (sUnion first second) () true ↔
        exactOneExtraResult.QueryRel first () true ∨
          exactOneExtraResult.QueryRel second () true := by
  intro alleged
  have both := alleged (singletonSpace ()) (singletonSpace ())
  exact exactOneExtraResult_cross_union.2
    (both.mpr (Or.inl exactOneExtraResult_cross_union.1))

end Mettapedia.Logic.Bridges.WMSpaceQueryCoherenceBoundary
