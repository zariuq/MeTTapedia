# Evaluation strategies and observation-sensitive comparisons

These studies reuse the branch-local Need machine and generic occurrence,
demand and resumption theories. Each comparison fixes its programs and
observer; strategy agreement does not imply equality of retained computations
under every later consumer.

Start with [CallSharingVerdict](CallSharingVerdict.lean),
[DemandNeedSimulation](DemandNeedSimulation.lean) and
[QuotationDemand](QuotationDemand.lean).

Principal results and controls:

- `CallSharingVerdict.perCandidate_iff_perSource` quantifies over every program,
  call, store, environment and ordered result list in the declared call-time
  choice semantics. The two call-sharing policies derive the same results.
- `CallSharingVerdict.Witness.verdict` narrows the four-policy comparison under
  its six separating workloads to per-source and per-candidate policies.
  `keep_no_policy_gives_4_9_7` rejects that answer-count vector for all four.
- `QuotationDemand` compares exactly two finite evaluators. Both preserve
  quoted syntax; discarded effects separate eager and by-name evaluation.
- `Trinity.Demand.NeedInstance` connects answer-agreement conditions to actual
  reference-machine runs. Value support, answer multiplicity and effect traces
  are distinct observations.

The generic weighted and probabilistic laws live in
`Machines.BranchLocalNeed.WeightedResumption` and
`GSLT.Dynamics.ProbabilisticResumption`. The declared uniform-per-transition
profile preserves completed and pending probability mass through every finite
pause/resume split. It does not turn nondeterminism into a global probability
policy.

`Weighted.StressAndCommitments.ProbabilityControls` derives the captured and
resampled draw laws from the machine: equal single-call marginals coexist with
different joint distributions. `joint_not_factors_marginal` gives the exact
observation-loss obstruction. Physical duplicate and zero-weight occurrences
remain in the operational representation.

Native equation and weighted-handler adapters belong to this strategy family
and instantiate the same branch-local Need machinery.
