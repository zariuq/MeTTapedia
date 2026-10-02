import Mettapedia.Machines.RunContracts.TestPlan
import Mettapedia.Machines.RunContracts.ScopedOutcome
import Mettapedia.Machines.RunContracts.Completion
import Mettapedia.Machines.RunContracts.Diagnostics
import Mettapedia.Machines.RunContracts.Runner
import Mettapedia.Machines.RunContracts.Document
import Mettapedia.Machines.RunContracts.ProcessReceipt

/-!
# Run contracts, scoped outcomes, and process reporting

Independent specifications and executable models for expected-error tests,
exact test identity accounting, demand-relative observation completion,
worker ownership, output/cleanup acknowledgement, bounded diagnostics, and
terminal framing. `Runner.exitCode_zero_iff` composes these contracts.

Diagnostic witnesses need not be ordered. `Runner.faulting_reports_same_status`
allows different observed faults without imposing complete fault enumeration.
Neither equality of exit codes nor diagnostic permutation is a substitute for
an optimization proof about program answers, effects, and handler scopes.

The package proves abstract finite protocol and algorithm laws. It does not
claim native runtime, discovery, serializer, or OS process correspondence.
`Document.exitCode_zero_iff` checks each query's separate contract and the
document's framing and finalization. See each component's header for its
precise admitted fragment.
-/
