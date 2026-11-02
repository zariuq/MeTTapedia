import Mettapedia.GSLT.Coordination.ConsensusNumbers.Framework
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Valence
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Race
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Registers
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Spaces
import Mettapedia.GSLT.Coordination.ConsensusNumbers.StepSpace
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Rho
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Absence
import Mettapedia.GSLT.Coordination.ConsensusNumbers.RemovalAnswers
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Linearizability
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Universal
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Universality
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Hierarchy
import Mettapedia.GSLT.Coordination.ConsensusNumbers.HierarchyGeneral
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Existence

/-!
# Consensus numbers of spaces, steps and rho communication

Herlihy's wait-free hierarchy (*Wait-free synchronization*, 1991) for the ways MeTTa and rho
let processes act on a shared space.

* `Framework`: objects, protocols, wait-free consensus, the consensus number.
* `Valence`: the valence argument once, for every deterministic object: if one of two processes
  cannot tell the order of any two operations, no two-process consensus; if a bystander cannot,
  no three-process consensus. Both survive using many objects together.
* `Race`: one claim-then-read protocol solves consensus for every number of processes over any
  object with a race; compare-and-swap has one.
* `Registers`: consensus number 1.
* `Spaces`: MeTTa's separate `add-atom`, `remove-atom`, `match`: consensus number 2 when removal
  reports success, 1 when it answers nothing (what Hyperon Experimental, PeTTa and CeTTa do for
  data atoms); also with registers and many spaces.
* `StepSpace`: the atomic step: consensus number ∞; steps that only keep and make: 1; take and
  make without conditions: ∞; absence-guarded make without take: ∞. A take-and-re-send is the
  same operation as a peek.
* `Rho`: rho COMM, which waits on empty channels: ∞; every deterministic object runs over rho
  with its history in one message.
* `Absence`: what COMM lacks: no encoding that keeps parallel composition expresses an absence
  check, into positive rules over bags or into the rho calculus.
* `RemovalAnswers`: whatever a removal answers (nothing, whether it removed, how many, which
  atoms), the separate operations give no consensus to three processes; counting removal, and
  PeTTa's removal of every match answering the count, have consensus number exactly 2.
* `Linearizability`: implementations, histories, linearizability (a history the object used
  atomically could show) and wait-freedom.
* `Universal`: Herlihy's universal construction over any base offering consensus slots and
  announcements; linearizable and wait-free.
* `Universality`: from consensus objects and registers, and from steps (even steps that take
  nothing), every object has a wait-free linearizable implementation.
* `Hierarchy`: implementing a consensus object gives consensus; so MeTTa's separate operations are
  not universal (silent removal: 2 or more processes; any answer: 3 or more).
* `HierarchyGeneral`: if `X` (with a read) implements `Y` and `Y` solves `n`-process consensus, so
  does `X`; an object cannot implement one of a higher consensus number.
* `Existence`: an object has a consensus number exactly when it has a state.

| object | consensus number | Lean |
|---|---|---|
| read/write registers | 1 | `registers_hasConsensusNumber_one` |
| space, separate ops, silent removal (as implemented) | 1 | `silentSpace_hasConsensusNumber_one` |
| space, steps that keep and make | 1 | `monotoneSpace_hasConsensusNumber_one` |
| space, separate ops, reported removal | 2 | `separateSpace_hasConsensusNumber_two` |
| compare-and-swap | ∞ | `casRegister_hasConsensusNumber_top` |
| space, steps with take and make | ∞ | `positiveSpace_hasConsensusNumber_top` |
| space, absence-guarded make | ∞ | `noTakeSpace_hasConsensusNumber_top` |
| space, the step | ∞ | `stepSpace_hasConsensusNumber_top` |
| rho COMM | ∞ | `rho_hasConsensusNumber_top` |
| space, separate ops, counting removal | 2 | `countSpace_hasConsensusNumber_two` |
| space, add + match + remove every match (count) | 2 | `patternSpace_hasConsensusNumber_two` |
| space, add + match + remove one (0/1) | 2 | `oneRemovalSpace_hasConsensusNumber_two` |
| space, separate ops, any answers | ≤ 2 | `spaceWith_not_solvable_three` |

| statement | Lean |
|---|---|
| consensus objects + registers implement every object | `Universal.consensus_universal` |
| steps implement every object | `Universal.steps_universal`, `Universal.noTakeSteps_universal` |
| implementing a consensus object gives consensus | `solvable_of_implements_consensus` |
| an implementation carries consensus over | `solvable_of_implements`, `not_implements_of_consensusNumber` |
| an object has a consensus number iff it has a state | `hasConsensusNumber_iff` |
-/
