import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Cast
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Upper
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Lower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Verdicts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Layers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Dual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.OnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.StepControls

/-!
# Checked behavioural certificates

The bisimulation metric of a finite labelled Markov chain is bracketed by certificates that a
Boolean function checks in exact rational arithmetic; each acceptance is a theorem about the metric
of the chain read in the reals. The mathematics is the tree's (`CouplingBound`,
`bisimulationMetric_le`, `abs_eval_sub_le_bisimulationMetric`, `approxMetric_eq_depthDistance`,
`behaviouralMetric`); this folder adds the checkers, the transport from rational to real chains, two
missing lemmas, and the reading on the transform step.

* **Rational to real** (`Cast`): chains, couplings, coupling bounds and expressions keep their values.
* **Upper certificate** (`Upper`): a prefixpoint kernel with listed couplings; the checker fills in the
  diagonal, reversed pairs and independent couplings, computing every cost. Acceptance implies
  `metric ≤ kernel` at every discount `0 ≤ c`. Soundness needs only the core conditions; the shape
  (bounded by one, symmetric) loses no bound and makes the fill-ins succeed.
* **Lower certificate** (`Lower`): a test formula as a DAG with shared nodes, each node entered once
  into a cache of value functions; the DAGs are exactly the formulas of the tree's test language,
  and a gap is the gap of the unfolded formula, below the iterate of its depth at `0 ≤ c` and below
  the metric at `0 ≤ c ≤ 1`.
* **Answers** (`Verdicts`): exact when the bounds meet, otherwise an interval that does not close; for
  "at most `ε`", holds, fails, or not decided, with sound decided outcomes, refinement that never
  flips a decided outcome, and consistency between brackets.
* **Layers** (`Layers`): kernels each above the step of the previous bound the depth-indexed distances
  at `0 ≤ c`; the iterates are the least such layers. A rational checker of layered certificates
  reuses the prefixpoint's coverage from one layer to the next; a test meeting a layer makes the
  distance at that horizon exact.
* **Dual post-fixpoint** (`Dual`): below the metric at `0 ≤ c < 1`; a rational checker with potentials;
  exactness when it meets a prefixpoint.
* **Controls** (`Controls`): a leaking chain whose metric at discount `9/10` is decided exactly, with
  `9/11` at the leak pair, four refusals each for one fault, tests that never close the leak pair,
  the horizon-two distance `261/400` there by layers, and a post-fixpoint above the metric at
  discount one.
* **On the transform step** (`OnTheStep`, `StepControls`): a finite region of step states closed under
  a stochastic policy is the step's system on the region, its metric vanishes exactly on the step's
  Larsen–Skou bisimilarity, and rational data describing it give a chain on which the same checkers
  decide the region's behavioural distances.
-/
