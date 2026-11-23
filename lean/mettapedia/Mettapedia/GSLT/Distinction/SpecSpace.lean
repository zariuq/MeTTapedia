import Mettapedia.GSLT.Distinction.SpecSpace.SpecBasis
import Mettapedia.GSLT.Distinction.SpecSpace.SpecQuasimetric
import Mettapedia.GSLT.Distinction.SpecSpace.ChuWitnessTopology
import Mettapedia.GSLT.Distinction.SpecSpace.SpecLocale
import Mettapedia.GSLT.Distinction.SpecSpace.LocalDeformation
import Mettapedia.GSLT.Distinction.SpecSpace.FrameDiagramCMTT
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.RealCalculi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.CoreSpecimens
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.HigherSpecimens
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.ParallelCSPSpec
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.WCOJOptimality

/-!
# Specification-Exploration Space: Real Calculi, 8-Primitive Basis, Topology, Frame Diagrams, and WCOJ/Parallel CSP

Index module assembling the specification-space theory web directly over `Mettapedia`'s real
calculi (`RuleSyntax.step`, `ParallelCalculus`, `FragmentsOfTheStep`, `NullsOnTheStep.ParallelClosed`,
`ReflectiveCalculus.Encodings`, `OSLF.MeTTaIL.{ReflectiveQuoteAdmission, ReflectiveContextualQuote}`,
`HE.Space`/`HE.matchAtoms`, and `PeTTaSpace`/`PeTTaSpace.spaceMatch`):

* `SpecSpecimens.RealCalculi`: real `ParallelCalculus` instances for HE MeTTa bidirectional matching
  (`heMatchParallel`) and PeTTa `spaceMatch` (`pettaMatchParallel`) with persistence & Gorla
  non-encodability walls, plus structural `RuleSyntax.step` / `Selection.Valid` walls for
  bounded take-arity vs. bulk retraction, `take`, `read`, and `make`.
* `SpecSpace.SpecBasis`: real 8-primitive AIT basis `{take, read, make, tell, guards, fresh, frame,
  size}` of the step, with eight kernel-verified semantic separation theorems (`sep_take` through
  `sep_size`) and `all_eight_step_primitives_separated`.
* `SpecSpace.SpecQuasimetric`: directed Lawvere quasimetric over `RouteGrades`, exact hosting
  preorder, Morita equivalence, forward open-ball topology, asymmetric hosting control, and
  nontrivial 2-cell route distinction control.
* `SpecSpace.ChuWitnessTopology`: Boolean and graded Chu spaces of specifications and witnesses,
  continuity of Chu transforms, syntax–semantics Galois polarity, closed obstruction walls,
  specialization = witness refinement, and finite-witness compactness.
* `SpecSpace.SpecLocale`: completely prime locale points of the witness frame, Stone duality and
  atomless/perfect-space indefinite-refinement boundary (`StoneGunkDuality`), and symmetric
  spec-space automorphism control.
* `SpecSpecimens.CoreSpecimens` & `SpecSpecimens.HigherSpecimens`: ten motivating spec-by-example
  dimensions (D1–D10) grounded in real `RuleSyntax.step`, `RuleSyntax.RegionalEquality`,
  `SharedUnknown`/`FreshOpenings`/`OwnedStore`, `ReflectiveQuoteAdmission`/`ReflectiveContextualQuote`,
  `AnnotatedRuns.AmplitudeRuns.Contextuality`, and `Relation.ReflTransGen` reachability controls.
* `SpecSpace.LocalDeformation`: general local deformation & Operational Lindström theory
  instantiated on REAL `ParallelCalculus` points (`realParallelChu`), REAL composable Gorla uniform
  routes (`uniformRouteQuasimetric`), REAL persistence and equation-consistency Pareto walls,
  genuine `IsRemovableArtifact` upgrades, positive bisimulation/lfp/uniform routes, and explicit
  Gorla criterion-sensitivity controls (`gorla_criterion_sensitivity_controls`).
* `SpecSpace.FrameDiagramCMTT`: multi-action frame-change diagrams (`FrameDiagram`,
  `CompatibleSection`, `ArithCore ⟶ SemNat` controls), REAL `PackedFrames` and quotient `FrameMap`
  over `Pattern` modulo `ReflectiveCanonical.canonicalEquivalent` (`ReflectiveViewFrames`,
  `substituteUnderHom`, `rho_quote_drop_separates_syntactic_from_canonical_frames`), and lifting
  step admission & runs over arbitrary frame-change diagrams (`DiagramStep`, `DiagramStep.Run`).
* `SpecSpecimens.ParallelCSPSpec`: relational CSP sharding, static Dwork–Kanellakis–Mitchell
  complexity-class dispatch, exact deterministic `k`-thread equivalence
  (`evalRuleSharded_eq_evalRuleSeq`), read-footprint invalidation, and Helly-round batch
  commutativity.
* `SpecSpecimens.WCOJOptimality`: generalized Hölder inequality (`sum_prod_rpow_le`),
  Atserias–Grohe–Marx (AGM) fractional edge-cover bound (`agm_bound`), fractional hypertree-width
  materialization bounds (`hypertree_bag_agm_bound`, `hypertree_all_bags_bounded`), triangle tight
  bound & binary-join blowup control, and `k`-way Generic Join soundness, completeness, and dynamic
  join-order invariance (`genericJoin_order_invariant`).
-/
