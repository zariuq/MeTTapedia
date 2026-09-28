import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.Cursor.Relational
import Mettapedia.Machines.Cursor.ClientMap
import Mettapedia.Machines.Cursor.Composition
import Mettapedia.Machines.Cursor.Transfer
import Mettapedia.Machines.Cursor.Amortized
import Mettapedia.Machines.Cursor.Sequence
import Mettapedia.Machines.Cursor.Fold
import Mettapedia.Machines.Cursor.SequenceCost
import Mettapedia.Machines.Cursor.SuffixSummary
import Mettapedia.Machines.Cursor.Scheduling
import Mettapedia.Machines.Cursor.Controls
import Mettapedia.Machines.Cursor.RelationalTransfer
import Mettapedia.Machines.Cursor.RelationalAmortized
import Mettapedia.Machines.Cursor.QueueCost
import Mettapedia.Machines.Cursor.AdaptiveBudget
import Mettapedia.Machines.Cursor.QueryLowerBound
import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.Machines.Cursor.TailSummary
import Mettapedia.Machines.Cursor.GenerationalSharing
import Mettapedia.Machines.Cursor.ListCells
import Mettapedia.Machines.Cursor.PrefixBuffer

/-!
# Cursor protocol algebra

Indexed request/reply protocols reuse polynomial coalgebras for client
control. Local provider and client refinements preserve bounded execution,
live residuals, and declared observations. Guarded transfer, independent
composition, and amortized resource laws support multiple realizations.

The sequence instances cover remaining lists, shared array windows, and
bounded prefetch. Concrete MeTTa and trie adapters live with those subjects;
the generic algebra imports neither. Executable positive and negative
controls are in `Mettapedia.Machines.Cursor.Controls`.

`Fold` is a resumable consumer whose accumulator need not collect a bag.
`SequenceCost` compares copying tails with retained views under the same client,
and `SuffixSummary` prepares the summaries of all tails in one pass.
`Scheduling` proves exact residual and receipt preservation for independently
owned work under per-item allocation equality; shared mutations are excluded.

`RelationalTransfer` moves a residual between representations without a
canonical decoder, and `RelationalAmortized` bounds the resources of such
moves; `QueueCost` is the two-list queue under that account.  `AdaptiveBudget`
lets a policy choose each round's budget without authority over the
computation, `QueryLowerBound` proves that observing an arbitrary prefix must
read it, and `OwnedLifecycle` publishes and cancels owned answer cursors.
`TailSummary` and `GenerationalSharing` are the summaries and storage
generations that retained tails rely on; `ListCells` and `PrefixBuffer` are
the PeTTa lane's list cells and constant-time `cons` onto flat lists.
-/
