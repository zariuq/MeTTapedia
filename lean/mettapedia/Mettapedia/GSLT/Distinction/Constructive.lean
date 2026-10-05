import Mettapedia.GSLT.Distinction.Constructive.Scale
import Mettapedia.GSLT.Distinction.Constructive.DepthBound
import Mettapedia.GSLT.Distinction.Constructive.Transport
import Mettapedia.GSLT.Distinction.Constructive.ClassicalBridge
import Mettapedia.GSLT.Distinction.Constructive.Controls
import Mettapedia.GSLT.Distinction.Constructive.ScaleTolerance
import Mettapedia.GSLT.Distinction.Constructive.ScaleToleranceControls

/-!
# A constructive, depth-indexed graded observation layer

Beside the classical behavioural metric of `BehaviouralMetric`, on the same
`HennessyMilner.System`.

* `Scale`: value scales (a linearly ordered additive group, a unit, a
  contracting discount), finite suprema, infima and Hausdorff values over
  lists, and the choice-free integer scale.
* `DepthBound`: presented systems (readings in a scale and an authored
  successor enumeration), formula values, and the depth-`n` bound over listed
  vocabularies: adequacy and exact expressivity at each depth, a pseudometric
  monotone in the depth, zero as the `n`-step approximant, the geometric tail,
  and reflection from a stabilization certificate.
* `Transport`: observation maps with an error, supplied vocabulary sections,
  formula and bound transport, sections computed from enumerations, and errors
  that add under composition.
* `ClassicalBridge` (**classical**): realizations in the reals; the classical
  logical and behavioural distances are the supremum and limit of the depth
  bounds, with rate `c ^ n / (1 - c)` below discount one; classical zero-distance
  reflection; exact maps as classical isometries with sections in place of
  `Function.surjInv`.
* `ScaleTolerance`: tolerances valued in the scale, with the unit in place of
  `1`; each depth bound is a metric tolerance without a choice principle; over
  a linearly ordered field they are the tolerances of the distinction
  calculus, and a rational reading carries them to `ℚ`.
  `ScaleToleranceControls`: a depth bound as a tolerance, read as `1/2` in
  `ℚ`; a tolerance that is not metric.
* `Controls`: the stream probe (agreement at every depth, bisimilarity exactly
  LLPO, finite-depth reflection implies LLPO, and where the classical step
  enters), a finite system with a stabilization certificate, exact transport
  along a collapse, a map without a section, a vocabulary that cannot be
  listed, a convergence modulus at discount one implying LPO, and an attained
  composite error.

Only `ClassicalBridge`, the two theorems marked classical in `Controls`, and
the readings into `ℚ` in `ScaleTolerance` use `Classical.choice`.  Approximate
transport of dependent families, exact dependent equality and `J` are not
claimed.
-/
