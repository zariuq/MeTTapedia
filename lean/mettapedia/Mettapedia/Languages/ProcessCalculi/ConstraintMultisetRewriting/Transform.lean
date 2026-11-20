import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.DependentEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.All
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.GradedStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualRunComposition

/-!
# Transform: indexed terms, operational instances and verified comparisons

This is an entry point to the existing transform foundations and their
binding-aware integration. It introduces no replacement term carrier, state,
unifier, or distinguished execution policy.

## Terms and substitution

`Interface.Frames` supplies indexed term carriers, an equivalence, frame maps
and their action on terms. The identity, composition and equality-preservation
laws concern this action; a bundled category or categorical universal property
is not an additional field of this interface.

Instances include nested first-order terms, intrinsic terms over a binding
signature, and the typed dependent frames. The representation of a term is
independent of whether a store holds occurrences, support, or annotations.
An occurrence can contain a term with arbitrarily nested object binders.

The binding constructions distinguish:

* Object variables, intrinsically scoped by `OSLF.Binding.Term` and its context.
* Contextual metavariables, each with its declared parameter context and sort.
* Fresh helper declarations, introduced by frame extensions such as
  `RuleSyntax.Contextual.declarations`; these are new unknowns, not nominal atoms.
* Rigid symbols and names, supplied by a particular signature or name model.
  Freshness of a helper does not establish generative freshness of a rigid name.

Object binders and row-schema locals are different. A stored lambda need not
freshen its object variables when read; a schematic row can freshen its local
metavariables even when its payload has no object binder. Captured arguments
remain shared across schema activations.

## Operational instances

`RuleSyntax.Core` defines one explicit instance: a bag of occurrences, one match
per firing, guards at solutions including its tells, a fixed rule set beside
the store, and one knowledge store. It is not a requirement on every instance.

The existing constructions also provide jointly enabled bags, synchronous
rounds, exhaustive and maximal disciplines, before/after-tell comparisons,
set stores, rules held as resources, schematic rows, and world-local systems.
Their comparison theorems carry the necessary freshness, compatibility,
query-stability and observation hypotheses. These alternatives are not asserted
to form an unrestricted Cartesian product of independently interchangeable
options.

Programs in `RuleSyntax.Core` are sets and may be infinite. Semantic matching
and guards quantify over solutions; the interface does not supply an enumerator
or a total decision procedure. An executable fragment needs its own certified
solver and enumeration assumptions. A supported principal answer may solve a
prefix while retaining further equations in its target frame.

`StepWeb.GradedStore` is a ground, guard-free, keep-only propagation instance.
It does not establish arbitrary graded consumption, live higher-order
constraints, or equivalence with a native implementation. With noncommutative
annotations the written order of read products remains meaningful.

## The binding execution chain

The following theorems are in `RuleSyntax.BindingIntegration`.

| Construction | Actual carrier and observation | Main theorem |
| --- | --- | --- |
| Intrinsic application | Existing Lean ABT graft, checked context/sort readback | `Syntax.intrinsic_application_readback` |
| Authored application | Source patterns modulo their alpha equivalence; exact refusal | `Syntax.authored_application_exact`, `Syntax.authored_application_refusal` |
| Solved prefix | Full occurrence problem and remaining equations/check interface | `Admission.valid_iff_of_principal_prefix` |
| Indexed solver transport | Mixed-index contextual observations in every future frame | `Admission.Frames.observed_residual_models_iff` |
| Actual rule admission | Original freshness/enabling and all residual guards/collect query | `Admission.Frames.firing_admission_iff` |
| Schematic read | Actual direct read and held two-step protocol; decoded live view | `Rows.read_expansion_of_reading` |
| Repeated activation | Actual nested-binder outputs in a common final model | `Rows.Example.actual_outputs_at_common_model` |
| Local world events | Actual activation choices, selected origins and result observer | `Worlds.dead_neighbour_observer` |
| Composed application | The same computed intrinsic term in schema, event and readback | `Pipeline.application_materializes` |
| Composed solver | The same output witness factored through full held information | `Pipeline.application_materializes_with_solver` |
| Concrete application and solver | Nonidentity physical graft of a nested binder term, with its actual capture equation | `PipelineExample.compiled_application_with_capture_solver` |

Here ABT representation and physical graft refer to the existing Lean data
representation and executable function. No C-memory, C-runtime or ISA
refinement is implied.

The local world adapter is an explicit persistent materialization discipline.
Its fixed schema catalogue and capture policy are part of its environment;
they are not reconstructed from arbitrary live-rule states. Capture-policy
coherence is proved for the anchored construction under its stated freshness
conditions. Arbitrary policies may inspect dead slots, so live-view congruence
requires an additional invariance argument.

The one-world comparison concerns singleton-to-singleton moves with empty
shared space. Fork, publication and merge remain separate moves. Counted
isolation is established for the local asynchronous event systems, not by
identifying all administrative world moves with local events. Joint information
must have a common solution when a selected operation combines it; unrelated
worlds need no global consistency premise.

The abstract `Worlds.Joining` record supplies an operation and left/right
solvability consequences. It does not by itself specify a shared-name
interface or characterize joint models. The joint-information claims here
concern the proved snapshot-publication and captured-schema constructions.

`RuleSyntax.Dependent.dependent_eq` compares the existing dependent full step
restricted to program-generated fresh openings with the rule-syntax instance.
It does not equate unrestricted dependent firings with a program, nor decide
every dependent unification problem.

## Positive examples and boundaries

`BindingIntegrationControls` pairs scoped nested application with escape
refusal, permuted pattern spines with their repeated-spine boundary, retained
occurrences with a support-erasure counterexample, and licensed guard timing
with actual changed admission. `BindingIntegration.Algebra` exhibits valid AC
rewriting and proves that the written-left observer cannot descend through it.
Neither AC equality nor a particular quotation discipline is imposed globally.

`BindingIntegration.Interaction.actual_compatibility_boundary` compares two
actual canonical activations with valid freshness, shape and allocation. The
compatible captured information admits one; the incompatible capture refuses
the other despite separately solvable reader and schema knowledge.

`BindingIntegration.Boundary` uses the same actual budgeted procedure at the
same budget on two firings with opposite semantic admission. Exhaustion is
neither admission nor refutation. Failure of a particular binding procedure
likewise need not mean that its equation has no solution.

`BindingIntegration.RuleMetadata.availability_does_not_descend` shows why
ordinary rows cannot recover arbitrary held-rule availability: an actual
linear-rule firing can consume its rule resource without changing those rows.
Endpoint equality, live-view equality, event-fibre correspondence and
contextual program equivalence are separate claims. This entry point does not
upgrade one of them to another.
-/
