# Prime specification evidence and research questions

[Specification](Specification.lean) indexes six connected question families:
observation, identity, admission, evaluation, mathematical host and reasoning.
Each checked claim retains an actual Lean theorem term. Descriptions and
suggested experiments are metadata; the theorem's own parameters determine its
scope. [DevelopmentPlan](DevelopmentPlan.lean) retains stable obligation IDs,
acceptance statements and dependencies.

[Requirements](Requirements.lean) provides bookkeeping for predicates on an
explicitly supplied system or assembly type. `Specification.Evidence` keeps one
assembly index throughout; `Evidence.complete` checks all required predicates
there. `pullback` reads the component actually present in that assembly, and
`conjoin` combines requirements at the same index. These operations supply no
implicit class of Prime systems and impose no type theory or strategy.

[DecisionSurface](DecisionSurface.lean) connects concrete separating examples
to the questions. Its `Sharing.no_observation_recovery_from_value_support`
shows why value support cannot recover a richer execution observation.
[ScopedIdentityStatus](ScopedIdentityStatus.lean) records the actual J/iota
bridge and the limits of the available identity interpretations.

Theorems `Specification.identity_direction_selected` and
`Specification.unselected_families` describe this index's selection records.
They are not a count of all settled or unsettled language-design questions.
The option graph in `PrimeOptions/Manifest.lean` records further distinctions.
The sharing results are linked as EVAL-028 through EVAL-030.

`RegularIntegrationBuild`, `NativeCandidateTheoryCrown` and the motivation
curriculum are import/qualification boundaries. Their presence in one gate
does not assert a joint model of all imported profiles. TRACE-004 and ASM-005
retain the remaining shared-assembly obligations under their original scope.

The paper's specification-space map distinguishes universal interface laws,
actual joint witnesses, separating examples and open kernel/candidate links.
