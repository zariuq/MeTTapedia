import Mettapedia.OSLF.Framework.GovernanceInstance

/-!
# Governance Norm Cycle: A Proper Reactive Loop Language

Provides a concrete `ClosedGovAccessibility` instance using a minimal 2-state
deterministic reactive loop:

```
GovDeliberate  ⟷  GovEnact
```

Both states are permanently live.  Seriality and closure are constructively proven
from the loop structure.  This gives a sorry-free, axiom-free governance accessibility
context for use in `GovernanceDDLBundle`.

## Design

PyashCore (a terminating language) cannot provide a `ClosedGovAccessibility` instance
because its `isGovLive` predicate (`instr ≠ Done`) is not forward-closed under
reduction — proven by `pyashCore_isGovLive_not_closed`.

The `GovNormCycle` language avoids this by having only two states (both permanently
live) that cycle indefinitely: deliberation alternates with enactment.  This models
an idealized governance process that never terminates.

## Usage

```lean
-- Instantiate govNormCycleAccessibility as the accessibility component of any bundle:
def myBundle (gf : GovFrame { p : Pattern // govNormLive p }) : GovernanceDDLBundle :=
  { acc := govNormCycleAccessibility, frame := gf }
```
-/

namespace Mettapedia.OSLF.Framework.GovNormCycle

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GovernanceInstance

/-! ## §1 Norm-Cycle States -/

/-- The deliberation state: norms are under consideration / being formulated. -/
def govDeliberateState : Pattern := .apply "GovDeliberate" []

/-- The enactment state: norms are being applied / enacted. -/
def govEnactState : Pattern := .apply "GovEnact" []

/-! ## §2 Transition Relation -/

/-- One-step transition for the governance norm cycle: deliberate ↔ enact. -/
inductive GovNormCycleStep : Pattern → Pattern → Prop where
  | deliberateToEnact : GovNormCycleStep govDeliberateState govEnactState
  | enactToDeliberate : GovNormCycleStep govEnactState govDeliberateState

/-! ## §3 Live Predicate -/

/-- The norm-cycle live predicate: exactly the two cycle states are live. -/
def govNormLive : Pattern → Prop :=
  fun p => p = govDeliberateState ∨ p = govEnactState

/-! ## §4 Seriality and Closure Proofs -/

/-- Every live norm-cycle state has a successor. -/
theorem govNormCycle_serial :
    ∀ p, govNormLive p → ∃ q, GovNormCycleStep p q := by
  intro p hp
  rcases hp with rfl | rfl
  · exact ⟨govEnactState, .deliberateToEnact⟩
  · exact ⟨govDeliberateState, .enactToDeliberate⟩

/-- The live predicate is closed under norm-cycle transitions. -/
theorem govNormCycle_closed :
    ∀ p q, govNormLive p → GovNormCycleStep p q → govNormLive q := by
  intro p q _hp hpq
  cases hpq
  · right; rfl  -- deliberateToEnact: q = govEnactState
  · left; rfl   -- enactToDeliberate: q = govDeliberateState

/-! ## §5 Canonical ClosedGovAccessibility Instance -/

/-- The governance norm cycle provides a `ClosedGovAccessibility` instance.
    Both states are permanently live; transitions are the deliberate ↔ enact cycle.
    Seriality and closure are constructively proven — no sorries, no axioms. -/
def govNormCycleAccessibility : ClosedGovAccessibility where
  live   := govNormLive
  step   := GovNormCycleStep
  serial := govNormCycle_serial
  closed := govNormCycle_closed

/-! ## §6 Summary -/

#check @govNormCycleAccessibility
#check @govNormCycle_serial
#check @govNormCycle_closed

end Mettapedia.OSLF.Framework.GovNormCycle
