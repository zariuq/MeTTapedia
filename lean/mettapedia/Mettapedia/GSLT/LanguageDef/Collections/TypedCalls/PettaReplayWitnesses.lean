import Lean
import Mathlib.Data.Finset.Sort
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay

/-!
# Data witnesses for checked finite typed-host replays

These elaborator-side constructors quote a candidate transition. The store
is retained by the name of a closed backing expression; input, output,
constraints, frames, alternatives and source occurrences are explicit data.
This generator is not a proof and may not justify changing a store. Each
candidate must be checked against the actual machine step by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReplayWitnesses

open Lean
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator Cell)
open PettaOccurrenceOverlay

deriving instance ToExpr for GroundedValue
deriving instance ToExpr for Atom
deriving instance ToExpr for Sum
deriving instance ToExpr for Ty

def stringSet (names : List String) : Finset String := names.toFinset

private instance : ToExpr (Finset String) where
  toTypeExpr := mkApp (mkConst ``Finset [0]) (mkConst ``String)
  toExpr names := mkApp (mkConst ``stringSet) (toExpr names.sort)

deriving instance ToExpr for Cell
deriving instance ToExpr for Allocator
deriving instance ToExpr for EagerDFS.Destination.Goal
deriving instance ToExpr for EagerDFS.Destination.Control
deriving instance ToExpr for EagerDFS.Destination.CollectedAnswer
deriving instance ToExpr for Row
deriving instance ToExpr for Phase
deriving instance ToExpr for CallFrame
deriving instance ToExpr for Context
deriving instance ToExpr for EagerDFS.Scope
deriving instance ToExpr for EagerDFS.Destination.Boundary
deriving instance ToExpr for Effects.Fault
deriving instance ToExpr for EagerDFS.Destination.ScopeBoundary
deriving instance ToExpr for Request

def worldExpr (backing : Name) (world : EagerDFS.World) : Expr :=
  mkApp3 (mkConst ``EagerDFS.World.mk) (mkConst backing) (toExpr world.input) (toExpr world.output)

def configurationType : Expr :=
  mkApp3 (mkConst ``EagerDFS.Configuration)
    (toTypeExpr (Work Unit)) (toTypeExpr EagerDFS.Destination.CollectedAnswer)
      (toTypeExpr (EagerDFS.Destination.CollectionCaller (Context Unit)))

def stateType : Expr := mkApp2 (mkConst ``Prod [0, 0]) (toTypeExpr Allocator) configurationType

def stateExpr (backing : Name) (state : State Unit) : Expr :=
  let config := mkAppN (mkConst ``EagerDFS.Configuration.mk)
    #[toTypeExpr (Work Unit), toTypeExpr EagerDFS.Destination.CollectedAnswer,
      toTypeExpr (EagerDFS.Destination.CollectionCaller (Context Unit)), worldExpr backing state.2.world, toExpr state.2.scopes]
  mkApp4 (mkConst ``Prod.mk [0, 0]) (toTypeExpr Allocator) configurationType (toExpr state.1) config

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReplayWitnesses
