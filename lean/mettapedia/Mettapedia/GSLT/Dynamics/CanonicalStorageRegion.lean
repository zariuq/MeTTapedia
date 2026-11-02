import Mettapedia.Machines.OrderedCutStore
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Finite canonical storage planning in the region portfolio

The classifier enumerates bounded structural cuts, chooses a minimal declared
cell-cost layout and returns the actual ordered occurrence store. Decoding,
matching, occurrence identity and duplicates are preserved. The plan is not
globally optimal over all storage policies or physical native representations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.CanonicalStorage

open Mettapedia.Machines ShapeStore FiniteCutCatalogue OrderedCutStore

variable {Id Atom : Type}

structure Layout (Id Atom : Type) where
  mask : Mask
  rows : OrderedCutStore.Rows Id Atom

def questions : RegionObservations.Family (Option (Facts Id Atom)) where
  Question := Option (Facts Id Atom) → Bool
  Answer _ := Bool
  read question facts := question facts

def boundary : Boundary (Facts Id Atom) (Option (Facts Id Atom)) (Option (Facts Id Atom)) where
  source := some
  summarize := id
  future := questions
  sufficient _ _ same question := congrArg question same

def plan [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom) : Layout Id Atom :=
  let mask := OrderedCutStore.select depth facts
  ⟨mask, OrderedCutStore.encode mask facts⟩

def region [DecidableEq Atom] (depth : Nat) : CertifiedRegion (boundary (Id := Id) (Atom := Atom)) Nat where
  regime := depth
  Artifact := Layout Id Atom
  attempt facts := .committed (plan depth facts)
  decode layout := OrderedCutStore.decode layout.rows
  restores _ _ impossible := by cases impossible
  exact facts _ committed := by
    cases committed
    exact OrderedCutStore.decode_encode _ _

theorem plan_exact [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom) :
    OrderedCutStore.decode (plan depth facts).rows = some facts := OrderedCutStore.selected_store_exact depth facts

theorem plan_optimal_in_catalogue [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom)
    (other : Mask) (bounded : other.depth ≤ depth) :
    OrderedCutStore.cells (plan depth facts).rows ≤ OrderedCutStore.cost facts other :=
  OrderedCutStore.selected_minimal depth facts other bounded

theorem plan_canonical [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom) :
    normalize (plan depth facts).mask = (plan depth facts).mask := OrderedCutStore.selected_canonical depth facts

theorem plan_keeps_matching [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom)
    (pattern : Pat Atom) (captured : Subst Atom) :
    OrderedCutStore.queryRows pattern captured (plan depth facts).rows =
      OrderedCutStore.queryFacts pattern captured facts := OrderedCutStore.query_encoded_exact _ _ _ _

def transferBoundary :
    Boundary (OrderedCutStore.Rows Id Atom) (Option (Facts Id Atom)) (Option (Facts Id Atom)) where
  source := OrderedCutStore.decode
  summarize := id
  future := questions
  sufficient _ _ same question := congrArg question same

def transferRegion (destination : Mask) :
    CertifiedRegion (transferBoundary (Id := Id) (Atom := Atom)) Nat where
  regime := 0
  Artifact := OrderedCutStore.Rows Id Atom
  attempt := OrderedCutStore.transfer destination
  decode := OrderedCutStore.decode
  restores := OrderedCutStore.transfer_restores destination
  exact before after completed := OrderedCutStore.completed_transfer_exact destination before after completed

theorem malformed_transfer_retains_entrance (destination : Mask) (rows : OrderedCutStore.Rows Id Atom)
    (malformed : OrderedCutStore.decode rows = none) :
    (transferRegion destination).attempt rows = .declined rows := by
  simp [transferRegion, OrderedCutStore.transfer, malformed]

end Mettapedia.GSLT.Dynamics.ObservationQualified.CanonicalStorage
