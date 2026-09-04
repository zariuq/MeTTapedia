# Enactive reasoning and semantic weakness

This directory formalizes Michael Timothy Bennett's enactive task and
weakness programme, then develops explicitly attributed comparisons and
extensions.

- `Basic.lean` is the finiteness-free 2024 layer: worlds, facts, abstraction
  vocabularies, aspects, completions, tasks, policies, and generations.
- `Finite.lean` is the finite counting projection used for cardinal weakness.
- `CompletionFibre.lean` retains the compatible completions themselves as a
  dependent type. Exact presentation equivalences and contravariant embeddings
  are proved before finite cardinal weakness is read out.
- `Bennett2023.lean` reconstructs the earlier Boolean-program presentation and
  proves its relationship to the later semantic layer.
- `GeneralizationOptimality.lean` proves the uniform future-task theorem with
  its distributional premise visible.
- `StochasticTaskProcess.lean` states Eray Ozkural's four task-process models
  and the exact certificate needed for a nonuniform process to preserve the
  weakness order.
- `Razor.lean` compares Bennett, Ockham, description length, Bayesian,
  Solomonoff-shaped, structural-risk, and quantale-valued profiles through the
  weakest common interface: admissibility plus a preference preorder.
- `CredalWeakness.lean`, `AntiUnificationWeakness.lean`, `GSLTPolicyBridge.lean`,
  `PrimeSupport.lean`, and `PrimeGeneration.lean` contain named bridges rather
  than silently enlarging Bennett's original claims.
- `IndividuationGeneration.lean` requires a process and task interpretation
  before individuation warrants a new generation; static closure alone is an
  explicit negative control.
- `MetasystemTransition.lean` constructs level introduction from constrained
  variation plus a task interpretation and proves that aggregation with an
  external selector is insufficient.
- `ProtectedFreedom.lean` separates semantic freedom, epistemic latitude, and
  currently executable freedom. Self-modification preserves a named family of
  protected completions rather than maximizing cardinality without qualification.

Bennett weakness is a semantic least-commitment profile, not the definition of
all simplicity. The directory retains counterexamples where code length,
nonuniform task probability, or proof multiplicity distinguishes candidates
that cardinal weakness does not.
