import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromInheritance

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
      , ⟨.scopeBoundary, "nonlinear switched phases remain empirical",
          "RoutedCaromCommutation"⟩ ]
  | .switchedStability =>
      [ ⟨.directLift, "geometric-power limit", "Mathlib"⟩
      , ⟨.newContent, "common quadratic schedule bound",
          "RoutedCaromStability"⟩
      , ⟨.newContent, "commutation-stability combined crown",
          "RoutedCaromStability"⟩
      , ⟨.refutation, "individual nilpotence does not imply switch stability",
          "RoutedCaromStability"⟩
      , ⟨.scopeBoundary, "a shared metric is stronger than per-map stability",
          "RoutedCaromStability"⟩ ]
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

theorem switchedStability_counts :
    (contributionCount .switchedStability .directLift,
      contributionCount .switchedStability .newContent,
      contributionCount .switchedStability .refutation,
      contributionCount .switchedStability .scopeBoundary) = (1, 2, 1, 1) := by
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

#print axioms simplexMixture_counts
#print axioms opacityAndRetention_counts
#print axioms affineCommutation_counts
#print axioms switchedStability_counts
#print axioms safetyInheritance_counts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom
