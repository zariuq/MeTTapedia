import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorDeliveryCorrespondence
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorNetworkControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorWorldStoreExecution
import Mettapedia.Languages.Erlang.ActorIdentityControls

import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxMachineExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxAgreementControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxCursorAgreement

import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxValueExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxExecution

import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxValueAdmissionControls

import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLiteralExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelLinkedExecution
/-! Loaded E0 actor-network execution and indexed source readback. The
actual channel-presence and delivery selectors preserve and reflect FIFO
selection, channel queues and unselected occurrences. Reachable source pid
stores agree with the loaded process lookup/update and world commit, including
retained network state and administrative history. Authored mailbox operations
have finite source paths and unique completed answers, joined to the actual
canonical runner and full-machine begin/advance calls. All finite source values
have uniform mailbox admission, including closure captures. Pending callbacks
retain their entire account; waiting callbacks preserve the source world and
record administration once. The real library provides the undefined atom for
empty peeks; fixture-only helper definitions have been removed. The explicit
kernel/rho/actor namespace checks and retained-row transport are checked.
The generated begin/resume/kernel entries execute the canonical class machine
on sorted inputs, retaining its complete pending work. Their execution transports
through the rho, actor and portable library extensions.
Value-returning callback dispatch,
local sequential simulation, scheduler and native-rho transfer, and ordinary
source frontend adequacy retain their separate correspondence obligations.
-/
