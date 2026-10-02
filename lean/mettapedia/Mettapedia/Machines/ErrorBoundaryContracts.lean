import Mettapedia.Machines.ErrorBoundaryContracts.ResultObservation
import Mettapedia.Machines.ErrorBoundaryContracts.Presentation
import Mettapedia.Machines.ErrorBoundaryContracts.Supervision
import Mettapedia.Machines.ErrorBoundaryContracts.AttemptIdentity
import Mettapedia.Machines.ErrorBoundaryContracts.DispatchPermit

/-!
# Error boundaries: observation, presentation, and supervised tasks

These component laws extend the existing run contracts without replacing a
dialect's exception terms or redefining ordinary symbolic data as failure.

Result observation has explicit handler scope and completion admission.
Diagnostic projection retains status while restricting public information.
Task supervision reserves durable permits and records terminal outcomes before
acknowledgement; uncertainty about external effects is separate from failure.
Task and attempt identities prevent delayed replies from settling a newer call.

The pure models do not establish native CeTTa correspondence, physical ledger
durability, exactly-once IO, or unconditional liveness of external services.
Each module contains controls that expose its admission boundary.
-/
