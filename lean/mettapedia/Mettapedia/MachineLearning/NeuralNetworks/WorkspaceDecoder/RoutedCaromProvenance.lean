import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromInheritance
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearCommutation
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromPathCompleteStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromContinuousChannel
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromAutonomousSemiflow
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutingNilpotentStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromJointNilpotentStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromScalarShiftStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromBalancedScalarShiftStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromBlockStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromSimultaneousBlocks
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromHermitianWordStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromHermitianDirectSum
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutingHermitianStability
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromRealSchurStability

/-!
# Content accounting for softmax-routed CAROM

This family-level ledger records which routed-CAROM results directly reuse
the sealed workspace and forgetting-geometry spine, which are new algebra or
adapters, which proposed generalizations are formally refuted, and which
claims remain outside the linear/structural scope.  Counts are checked by
Lean rather than reported informally.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom

/-- Formalization rungs for routed CAROM. -/
inductive ProvenanceRung
  | simplexMixture
  | opacityAndRetention
  | affineCommutation
  | nonlinearCommutation
  | switchedStability
  | safetyInheritance
  deriving DecidableEq, Repr

/-- Provenance class for one theorem family. -/
inductive ContributionKind
  | directLift
  | newContent
  | refutation
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One family in the routed-CAROM contribution ledger. -/
structure Contribution where
  kind : ContributionKind
  family : String
  source : String
  deriving Repr

/-- Exhaustive family-level ledger for all routed-CAROM rungs. -/
def contributions : ProvenanceRung → List Contribution
  | .simplexMixture =>
      [ ⟨.directLift, "gated interpolation semantics", "Dynamics and Carom"⟩
      , ⟨.newContent, "simplex gain and proposal collapse", "RoutedCarom"⟩
      , ⟨.newContent, "unit-interval mixed-gain theorem", "RoutedCarom"⟩
      , ⟨.scopeBoundary, "zero mixed gain and no nonlinear learning claim",
          "RoutedCarom"⟩ ]
  | .opacityAndRetention =>
      [ ⟨.directLift, "fixed typed workspace addresses", "TypedRegisters"⟩
      , ⟨.newContent, "commands quotiented by simplex schedules", "RoutedCarom"⟩
      , ⟨.newContent, "immutable evidence-fixed-workspace triple",
          "RoutedCarom"⟩
      , ⟨.scopeBoundary, "workspace behavior remains unrestricted",
          "RoutedCarom"⟩ ]
  | .affineCommutation =>
      [ ⟨.directLift, "zero interference energy iff linear commutation",
          "InterferenceGram"⟩
      , ⟨.directLift, "symmetric two-factor holonomy iff commutation",
          "ElementaryHolonomy"⟩
      , ⟨.newContent, "affine composition discrepancy decomposition",
          "RoutedCaromCommutation"⟩
      , ⟨.newContent, "linear and bias compatibility iff order independence",
          "RoutedCaromCommutation"⟩
      , ⟨.refutation, "linear commutation alone is insufficient with bias",
          "RoutedCaromCommutation"⟩
      , ⟨.scopeBoundary, "arbitrary nonlinear phases without derivative control",
          "RoutedCaromCommutation"⟩ ]
  | .nonlinearCommutation =>
      [ ⟨.directLift, "mean-value control of first-order remainder", "Mathlib"⟩
      , ⟨.directLift, "affine composition boundary through the Euler lift",
          "RoutedCaromCommutation"⟩
      , ⟨.newContent, "finite-step Lie bracket and cubic remainder bound",
          "RoutedCaromNonlinearCommutation"⟩
      , ⟨.newContent, "suffix-amplified swap and finite-path accumulation",
          "RoutedCaromNonlinearCommutation"⟩
      , ⟨.newContent,
          "declared-region adjacent-swap certificates with heterogeneous path budgets",
          "RoutedCaromNonlinearCommutation"⟩
      , ⟨.refutation, "nonlinear command maps need not be order independent",
          "RoutedCaromNonlinearCommutation"⟩
      , ⟨.scopeBoundary, "trained-router efficacy and automatic region-bound discovery",
          "RoutedCaromNonlinearCommutation"⟩ ]
  | .switchedStability =>
      [ ⟨.directLift, "geometric-power limit", "Mathlib"⟩
      , ⟨.newContent, "common quadratic schedule bound",
          "RoutedCaromStability"⟩
      , ⟨.newContent, "commutation-stability combined crown",
          "RoutedCaromStability"⟩
      , ⟨.newContent, "constructed common metric for commuting square-zero commands",
          "RoutedCaromCommutingNilpotentStability"⟩
      , ⟨.newContent, "recursive common metric for finite jointly nilpotent families",
          "RoutedCaromJointNilpotentStability"⟩
      , ⟨.newContent, "commuting individual nilpotence implies a finite joint budget",
          "RoutedCaromJointNilpotentStability"⟩
      , ⟨.newContent, "common metric for scalar contractions with jointly nilpotent residuals",
          "RoutedCaromScalarShiftStability"⟩
      , ⟨.newContent,
          "balanced common metric for every strict real scalar radius with jointly nilpotent residuals",
          "RoutedCaromBalancedScalarShiftStability"⟩
      , ⟨.newContent, "dependent block assembly of local common metrics",
          "RoutedCaromBlockStability"⟩
      , ⟨.newContent,
          "simultaneous generalized blocks have commuting jointly nilpotent residuals",
          "RoutedCaromSimultaneousBlocks"⟩
      , ⟨.newContent,
          "strict Hermitian word metrics on every stable simultaneous complex block",
          "RoutedCaromHermitianWordStability"⟩
      , ⟨.newContent,
          "finite Hermitian product assembly and exact non-orthogonal coordinate transport",
          "RoutedCaromHermitianDirectSum"⟩
      , ⟨.newContent,
          "global common Hermitian metric for commuting complex families under an active-character disk bound",
          "RoutedCaromCommutingHermitianStability"⟩
      , ⟨.newContent,
          "uniform spectral-radius extraction and exact real quadratic schedule certificate",
          "RoutedCaromCommutingHermitianStability and RoutedCaromRealSchurStability"⟩
      , ⟨.newContent,
          "common regional nonlinear Lyapunov schedule and observation bounds",
          "RoutedCaromNonlinearStability"⟩
      , ⟨.newContent,
          "genuinely nonlinear common-certificate command family",
          "RoutedCaromNonlinearStability"⟩
      , ⟨.newContent,
          "path-complete regional energy, distance, and observation-itinerary bounds",
          "RoutedCaromPathCompleteStability"⟩
      , ⟨.newContent,
          "nonconstant moving-center itinerary with phase-indexed energies",
          "RoutedCaromPathCompleteStability"⟩
      , ⟨.newContent,
          "continuous phase-flow entry, attraction, dwell, exit, activation, and halt composition",
          "RoutedCaromContinuousChannel"⟩
      , ⟨.newContent,
          "two-phase exponential dwell itinerary and absorbing halt",
          "RoutedCaromContinuousChannel"⟩
      , ⟨.newContent,
          "shared-semiflow phase execution equals one flow at total duration",
          "RoutedCaromAutonomousSemiflow"⟩
      , ⟨.newContent,
          "smooth autonomous vector-field channel with transverse contraction and observable halt",
          "RoutedCaromAutonomousSemiflow"⟩
      , ⟨.refutation, "individual nilpotence does not imply switch stability",
          "RoutedCaromStability"⟩
      , ⟨.refutation,
          "individually nilpotent switches have no global coercive common regional certificate",
          "RoutedCaromNonlinearStability"⟩
      , ⟨.refutation,
          "an unlicensed phase edge can violate the geometric energy bound",
          "RoutedCaromPathCompleteStability"⟩
      , ⟨.refutation,
          "a continuous metastable phase cannot have zero dwell",
          "RoutedCaromContinuousChannel"⟩
      , ⟨.refutation,
          "valid continuous phases need not compose in reverse order",
          "RoutedCaromContinuousChannel"⟩
      , ⟨.refutation,
          "compatible continuous phases need not share one autonomous evolution",
          "RoutedCaromAutonomousSemiflow"⟩
      , ⟨.scopeBoundary, "a shared metric is stronger than per-map stability",
          "RoutedCaromStability"⟩
      , ⟨.scopeBoundary,
          "matrix representation of the coordinate-free real quadratic energy",
          "RoutedCaromRealSchurStability"⟩
      , ⟨.scopeBoundary,
          "automatic invariant-region and Lyapunov discovery for trained nonlinear routers",
          "RoutedCaromNonlinearStability"⟩
      , ⟨.scopeBoundary,
          "source-derived phase graphs and trained-router certificate extraction",
          "RoutedCaromPathCompleteStability"⟩
      , ⟨.scopeBoundary,
          "heteroclinic generalized Lotka--Volterra and trained-router realization",
          "RoutedCaromAutonomousSemiflow"⟩ ]
  | .safetyInheritance =>
      [ ⟨.directLift, "legal-action acceptance soundness and recall",
          "TypedRegisters"⟩
      , ⟨.newContent, "convex closure of expert-family steps",
          "RoutedCaromInheritance"⟩
      , ⟨.newContent, "temperature-route-schedule decoder adapter",
          "RoutedCaromInheritance"⟩
      , ⟨.scopeBoundary, "safety constrains support rather than score quality",
          "RoutedCaromInheritance"⟩ ]

/-- Count one provenance class on one rung. -/
def contributionCount (rung : ProvenanceRung) (kind : ContributionKind) : Nat :=
  ((contributions rung).filter fun entry => entry.kind = kind).length

/-- Counts are ordered as direct lift, new content, refutation, and scope
boundary. -/
theorem simplexMixture_counts :
    (contributionCount .simplexMixture .directLift,
      contributionCount .simplexMixture .newContent,
      contributionCount .simplexMixture .refutation,
      contributionCount .simplexMixture .scopeBoundary) = (1, 2, 0, 1) := by
  decide

theorem opacityAndRetention_counts :
    (contributionCount .opacityAndRetention .directLift,
      contributionCount .opacityAndRetention .newContent,
      contributionCount .opacityAndRetention .refutation,
      contributionCount .opacityAndRetention .scopeBoundary) = (1, 2, 0, 1) := by
  decide

theorem affineCommutation_counts :
    (contributionCount .affineCommutation .directLift,
      contributionCount .affineCommutation .newContent,
      contributionCount .affineCommutation .refutation,
      contributionCount .affineCommutation .scopeBoundary) = (2, 2, 1, 1) := by
  decide

theorem nonlinearCommutation_counts :
    (contributionCount .nonlinearCommutation .directLift,
      contributionCount .nonlinearCommutation .newContent,
      contributionCount .nonlinearCommutation .refutation,
      contributionCount .nonlinearCommutation .scopeBoundary) = (2, 3, 1, 1) := by
  decide

theorem switchedStability_counts :
    (contributionCount .switchedStability .directLift,
      contributionCount .switchedStability .newContent,
      contributionCount .switchedStability .refutation,
      contributionCount .switchedStability .scopeBoundary) = (1, 21, 6, 5) := by
  decide

theorem safetyInheritance_counts :
    (contributionCount .safetyInheritance .directLift,
      contributionCount .safetyInheritance .newContent,
      contributionCount .safetyInheritance .refutation,
      contributionCount .safetyInheritance .scopeBoundary) = (1, 2, 0, 1) := by
  decide

/-- Status vocabulary prevents structural linear theorems from being reported
as trained nonlinear performance results. -/
inductive ClaimStatus
  | formallySealed
  | empiricalOnly
  deriving DecidableEq, Repr

/-- Learning quality of nonlinear softmax/SwiGLU routers is deliberately not
entailed by the routed structural theory. -/
def nonlinearRouterPerformanceStatus : ClaimStatus := .empiricalOnly

/-- Near-identity command-order control is formal under the derivative and
tail-Lipschitz hypotheses stated by the nonlinear commutation theorems. -/
def nonlinearCommandOrderTheoryStatus : ClaimStatus := .formallySealed

/-- Uniform nonlinear schedule stability and the observation-margin corollary
are sealed under one declared invariant region and common coercive Lyapunov
certificate.  Extracting that certificate from a trained router is not part
of the theorem. -/
def nonlinearRegionalSwitchedStabilityStatus : ClaimStatus := .formallySealed

/-- Finite path-complete regional stability is sealed for a declared labeled
phase graph, including phase-indexed centers, all-handoff observation margins,
and a nonconstant moving-center fixture.  Source-derived graph discovery and
continuous metastable dynamics remain outside this status. -/
def pathCompleteRegionalStabilityStatus : ClaimStatus := .formallySealed

/-- Continuous phase-flow composition is sealed for declared phase evolutions,
regions, transverse bounds, positive dwell intervals, exit links, activation
floors, and an absorbing halt.  This status does not construct the phases from
an autonomous vector field or identify them with a trained routed carrier. -/
def continuousMetastableChannelStatus : ClaimStatus := .formallySealed

/-- Autonomous realization is sealed when every phase evolution is identified
with one shared semiflow.  A smooth two-dimensional vector-field fixture
realizes a nonconstant two-phase itinerary and observable halt.  This does not
construct a heteroclinic GLV system or bind a trained routed carrier. -/
def autonomousContinuousChannelStatus : ClaimStatus := .formallySealed

/-- A common strict quadratic metric is constructively sealed for every
finite jointly nilpotent family, with commuting individual nilpotence as a
checkable sufficient condition.  The same construction covers a common
scalar contraction plus jointly nilpotent residuals; general commuting Schur
families remain a strictly broader boundary. -/
def scalarShiftedJointNilpotentMetricStatus : ClaimStatus := .formallySealed

/-- The scalar-shifted construction has no extra quantitative radius gap in
the real case: every nonnegative scalar radius strictly below one admits a
positive balance and residual scale yielding a strict common rate. -/
def balancedScalarShiftedMetricStatus : ClaimStatus := .formallySealed

/-- Finite dependent block-diagonal families inherit a shared strict rate
from local block certificates at that rate. -/
def blockDiagonalMetricAssemblyStatus : ClaimStatus := .formallySealed

/-- A finite pairwise-commuting family over an algebraically closed field
spans the state space by simultaneous maximal generalized eigenspaces.  On
each such block, every command is its character value times the identity plus
a residual; those residuals commute and are jointly nilpotent for finite
command families. -/
def simultaneousGeneralizedBlockStatus : ClaimStatus := .formallySealed

/-- Every stable simultaneous complex generalized block has a positive
Hermitian word energy shared by all commands. -/
def simultaneousBlockHermitianMetricStatus : ClaimStatus := .formallySealed

/-- Under one strict active-character disk bound, finite commuting complex
families have a global common Hermitian contraction energy.  The construction
assembles non-orthogonal simultaneous blocks through an exact internal direct
sum rather than the ambient norm. -/
def commutingComplexHermitianMetricStatus : ClaimStatus := .formallySealed

/-- Finite pairwise-commuting real matrix families whose exact
complexifications are individually Schur-stable have one positive real
quadratic contraction energy and hence one geometric energy bound for every
finite command schedule. -/
def commutingRealSchurQuadraticEnergyStatus : ClaimStatus := .formallySealed

#print axioms simplexMixture_counts
#print axioms opacityAndRetention_counts
#print axioms affineCommutation_counts
#print axioms nonlinearCommutation_counts
#print axioms switchedStability_counts
#print axioms safetyInheritance_counts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom
