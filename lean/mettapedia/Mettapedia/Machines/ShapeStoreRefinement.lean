import Mettapedia.Machines.ShapeHeadRouting
import Mettapedia.Machines.IndexedTupleJoin
import Mettapedia.Machines.PersistentOccurrenceSegments

/-!
# Shape-store refinement and persistent occurrence contracts

Joined entry point for per-head promotion, three posting layouts, bound-column
selection, nested-probe joins and stable domain-qualified occurrence IDs.

The bridge below states the capture boundary explicitly: a table enumerates
the selected logical rows of the current head-store view. Given that capture,
the constructed index query agrees with the independent all-rows operation
trace. Native capture, index invalidation, concurrency, file encoding and
ownership remain implementation obligations, not premises silently discharged
by this logical theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShapeStoreRefinement

variable {Head Fact Id Value : Type} {k : Nat}
variable [DecidableEq Head] [DecidableEq Fact] [DecidableEq Id] [LinearOrder Value]

/-- The composed differential oracle: routed updates, selected head capture,
indexed selection, and duplicate-preserving payload observation. -/
theorem routed_indexed_oracle (head : Fact → Head) (eligible : Fact → Bool)
    (ops : List (ShapeHeadRouting.Op Head Fact)) (s : ShapeHeadRouting.State Head Fact)
    (project : Fact → Option (IndexedTupleJoin.Tuple k Value))
    (table : IndexedTupleJoin.Table Id Value k)
    (captured : (table.ids.map table.row : Multiset (IndexedTupleJoin.Tuple k Value)) =
      (ShapeHeadRouting.observe (ShapeHeadRouting.run head eligible ops s).2).filterMap project)
    (cache : IndexedTupleJoin.Cache Id Value k) (valid : IndexedTupleJoin.Valid table cache)
    (bounds : IndexedTupleJoin.Bounds k Value) :
    IndexedTupleJoin.payloads table (IndexedTupleJoin.query table cache bounds) =
      ((ShapeHeadRouting.referenceRun ops (ShapeHeadRouting.observe s)).2.filterMap project).filter
        (fun row => IndexedTupleJoin.acceptsBounds bounds row = true) := by
  rw [IndexedTupleJoin.payloads_exact table cache valid, captured]
  have source := congrArg Prod.snd (ShapeHeadRouting.run_refines head eligible ops s)
  dsimp only at source
  rw [source]

theorem routed_indexed_maintenance_oracle (head : Fact → Head) (eligible : Fact → Bool)
    (ops : List (ShapeHeadRouting.Op Head Fact)) (s : ShapeHeadRouting.State Head Fact)
    (project : Fact → Option (IndexedTupleJoin.Tuple k Value))
    (table : IndexedTupleJoin.Table Id Value k)
    (captured : (table.ids.map table.row : Multiset (IndexedTupleJoin.Tuple k Value)) =
      (ShapeHeadRouting.observe (ShapeHeadRouting.run head eligible ops s).2).filterMap project)
    (cache : IndexedTupleJoin.Cache Id Value k) (valid : IndexedTupleJoin.Valid table cache)
    (actions : List (IndexedTupleJoin.Maintenance Value k)) (bounds : IndexedTupleJoin.Bounds k Value) :
    IndexedTupleJoin.payloads table (IndexedTupleJoin.query table
      (IndexedTupleJoin.maintain table actions cache) bounds) =
      ((ShapeHeadRouting.referenceRun ops (ShapeHeadRouting.observe s)).2.filterMap project).filter
        (fun row => IndexedTupleJoin.acceptsBounds bounds row = true) := by
  rw [IndexedTupleJoin.query_maintenance table actions cache valid]
  exact routed_indexed_oracle head eligible ops s project table captured cache valid bounds

#print axioms routed_indexed_oracle
#print axioms routed_indexed_maintenance_oracle

end Mettapedia.Machines.ShapeStoreRefinement
