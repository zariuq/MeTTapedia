import Mettapedia.Logic.HOL.LogicalInduction.Code
import Mettapedia.Logic.HOL.LogicalInduction.DeductiveProcess
import Mettapedia.Logic.HOL.LogicalInduction.Market
import Mettapedia.Logic.HOL.LogicalInduction.Criterion
import Mettapedia.Logic.HOL.LogicalInduction.Conditioning
import Mettapedia.Logic.HOL.LogicalInduction.Calibration

/-!
# Logical-Induction-Ready HOL Belief Infrastructure

Public entrypoint for the dynamic belief/process layer above real HOL.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), this subtree provides:

- canonical coding of closed HOL formulas,
- deductive processes,
- time-indexed rational belief days,
- trader/exploitability vocabulary,
- theory-extension conditioning interfaces,
- and calibration/timely-learning specifications.

This layer is deliberately an overlay on top of canonical HOL semantics, not a
replacement for them.

The PLN-facing WM empirical special case and its regression wrapper live under
`Mettapedia.PLN.Bridges.HOL.LogicalInduction`.

The Pure-kernel artifact boundary for encoded HOL formulas lives on the language
side under
`Mettapedia.Languages.MeTTa.PureKernel.HOLLogicalInductionBridge`.
-/
