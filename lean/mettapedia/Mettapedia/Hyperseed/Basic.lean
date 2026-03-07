import Mettapedia.Logic.PLNWorldModelFixpointClosure

/-!
# Hyperseed: Basic Structures

Minimal core structures for the Hyperseed exploration/state-accumulation layer.

Hyperseed sits above `GenericWorldModel` and WM closure as a thin wrapper
that lets an external agent (e.g. OpenClaw) feed observations into a WM state
and derive consequences via the existing fixpoint closure machinery.

## Design constraints

- Generic over evidence carrier and WM state.
- Reuses `PLNWorldModelFixpointClosure.RuleSet` directly.
- Does not invent new closure semantics.
- Does not assume PureKernel or OSLF as the only rule source.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelFixpointClosure

/-! ## Observation envelope -/

/-- An observation tagged with source and timestamp metadata.
Generic over payload, source identifier, and time representation. -/
structure ObservationEnvelope (Obs Source Time : Type*) where
  source : Source
  time : Time
  payload : Obs

/-! ## Hyperseed kernel -/

/-- The Hyperseed exploration kernel: packages an ingestion function, a seed
query set, and a consequence rule pool over an existing WM state/query space.

- `ingest` folds a single observation into the WM state.
- `seedQueries` are the initial query obligations for closure.
- `rules` is the consequence rule pool (reused from `PLNWorldModelFixpointClosure`).
-/
structure HyperseedKernel (Obs State Query : Type*)
    [EvidenceType State] [WorldModel State Query] where
  /-- Fold a single observation into the WM state. -/
  ingest : Obs → State → State
  /-- Initial query obligations for closure. -/
  seedQueries : Set Query
  /-- Consequence rule pool (reused from fixpoint closure). -/
  rules : RuleSet State Query

end Mettapedia.Hyperseed
