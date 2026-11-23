# Native execution, evidence and qualified realization

This layer studies raw execution together with optional typing, retained
proofs, revision checks and observation-preserving optimization. It contains
adapters over several named profiles. Each adapter states the actual syntax,
world and observation it consumes.

[Language](Language.lean) defines the parameterized occurrence/Need/quotation
assembly through `Language.Model`: an occurrence point, a bag observation and
revision authority. `QueryFirstModel.toAssemblyModel` is its query-first
instance. This model type does not select an intensional calculus.

[GradualExecutionPlan](GradualExecutionPlan.lean) retains raw, typed and checked
plans. [GradualDependentCapability](GradualDependentCapability.lean) connects
shared displayed evidence to the existing Need checker and formed judgments.
The generic families, evidence statuses and transport laws live in
`TypeTheory.DisplayedEvidence`; raw values remain the indices of those laws.

Principal boundaries and results:

- `NativeProgramElaboration.erase_prepareRows` preserves every authored
  command under program preparation, including islands whose checking fails.
- `NativeGradualDependentInteraction.observe_transport_exact` retains ordered
  occurrences, rather than just target reachability.
- `NativeInteractionEffectAnalysis` instantiates shared linear-resource
  analysis. In `ResourceInteraction`, `System.pairSeparation_iff_concurrent`
  requires read-free occurrences; `consumption_separation_does_not_supply_reads`
  rejects the stronger claim without its read premises.
- `ParallelEffectRealization` keeps effect separation distinct from an actual
  execution diamond. An effect description alone supplies no scheduler authority.
- Revision-current admissions and exact fallback codecs preserve their named
  observations. Source ambiguity and receipt provenance can carry information
  absent from a runtime-only trace.

The work/span interface uses `Algebra.WorkSpan`. Rho cost interpretations,
parallel execution, typed source admission and profitability remain distinct
contracts. Native artifact qualification is recorded separately from these
formal semantic results.
