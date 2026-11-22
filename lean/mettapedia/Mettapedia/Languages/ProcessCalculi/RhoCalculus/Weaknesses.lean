import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Monotone
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Symmetry
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Rights
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Saturation

/-!
# Where rho is weak, proved

Four modules, each a limit of the rho calculus or of Rholang stated as a theorem, with the
positive control that shows what the step language (one atomic step over a space: take, keep,
make, and predicate queries) does instead.

* `Monotone`: in rho a neighbour can only add behaviour (`weakBarb_par`), so firing now or else,
  priority and exact counts have no compositional rho encoding
  (`rho_cannot_encode_tryReceive`, `rho_cannot_encode_priority`, `rho_cannot_encode_exactlyOne`).
  Absence itself is `ConsensusNumbers.rho_cannot_encode_absence`.
* `Symmetry`: binary steps, such as rho's COMM, cannot break symmetry: no leader is elected from a
  split symmetric configuration (`no_symmetric_election`, `rho_no_symmetric_election`); one join
  step elects (`Controls.joinTable_elects`).
* `Rights`: Rholang's bundles cannot hand out reading without removing (`no_peekOnly_bundle`,
  `bundle_reader_removes`); a peek-only handle keeps a shared datum for everyone
  (`peekOnly_keeps`).
* `Saturation`: a persistent send meeting a persistent receive never comes to rest
  (`persistent_never_rests`); a guard checked after taking steps forever where a pattern with a
  shared variable rests at once (`checkAfterTake_never_rests`, `pattern_rests`).
-/
