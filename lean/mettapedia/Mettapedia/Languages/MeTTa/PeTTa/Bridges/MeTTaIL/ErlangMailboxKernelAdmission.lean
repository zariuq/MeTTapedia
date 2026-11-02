import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CanonicalEmissionSupport

/-! The concrete mailbox module is admitted by the existing class emitter.
Namespace freshness and the actual plan obligations are checked separately
from the entry-body and linked-runtime execution proofs. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelAdmission

open ErlangMailboxKernelSource

theorem entry_checks : CompleteEmissionSupport.entryChecks name = true := by decide +kernel

theorem fresh : CompleteEmission.namesFresh spec name .classes = true :=
  CompleteEmissionSupport.namesFresh_of_canonical_entryChecks spec name rfl entry_checks

theorem pending_empty : CompleteEmission.pendingFor spec .classes = [] := by decide_cbv

theorem balanced : Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.equationsChecked spec.plan = true :=
  Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Runner.equations_checked

theorem finite_provider : spec.plan.snapshot.provider.dynamicRelations.isEmpty = true := rfl

theorem emitted_ok : CompleteEmission.emit? spec name .classes = .ok emitted := by
  unfold CompleteEmission.emit?
  rw [pending_empty, balanced, finite_provider, fresh]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelAdmission
