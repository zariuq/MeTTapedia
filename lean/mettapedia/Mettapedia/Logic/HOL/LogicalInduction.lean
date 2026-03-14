import Mettapedia.Logic.HOL.LogicalInduction.Code
import Mettapedia.Logic.HOL.LogicalInduction.DeductiveProcess
import Mettapedia.Logic.HOL.LogicalInduction.Market
import Mettapedia.Logic.HOL.LogicalInduction.Criterion
import Mettapedia.Logic.HOL.LogicalInduction.Conditioning
import Mettapedia.Logic.HOL.LogicalInduction.Calibration
import Mettapedia.Logic.HOL.LogicalInduction.PureBridge
import Mettapedia.Logic.HOL.LogicalInduction.WorldModelBridge
import Mettapedia.Logic.HOL.LogicalInduction.EmpiricalSpecialCase
import Mettapedia.Logic.HOL.LogicalInduction.Regression

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
- calibration/timely-learning specifications,
- the current artifact-only Pure bridge contract shape,
- and a thin WM-facing belief-day interface plus the empirical special case.
- a bundled positive/negative regression target for the current toy layer.

This layer is deliberately an overlay on top of canonical HOL semantics, not a
replacement for them.
-/
