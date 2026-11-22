import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Carrier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Readback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Operational
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Reactions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Parallel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Observations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.CompilerFacts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Controls

/-!
# Rho onto the determinate closed-row transform fragment

This entry connects the existing closed rho calculus to a whole invariant
domain of its existing transform implementation. The target is not a new
machine: `CleanFragment.Point` is a subtype of `ByInstantiation.State`, and
`CleanFragment.Move` is the actual step of `ByInstantiation.program`.

## Fixed instance

* Source: `LanguageDefGSLT.RhoProcess`, with its existing scope and sealed
  quotation condition, structural equations and reduction relation.
* Terms: the intrinsically scoped contextual twin-binder signature. An input
  continuation binds the received name and process; communication instantiates
  the continuation at `(@Q, Q)`. Terms can have nested binders and syntax.
* Knowledge: `ByInstantiation.knowledge`, including the existing closed-name
  equivalence. Admission here is the semantic rule-syntax relation.
* Store: finite occurrence identities with contextual observations as labels.
  Equal labels retain their separate occurrences.
* Program: exactly `commRule`, `heatRule`, `clearBagRule`, `clearZeroRule`.
  One admitted firing is the selected reduction grain of this instance.
* Composition: `Encodings.tensor`, with disjoint declaration frames and
  occurrence identities. It is not a shared-unknown composition policy.

These settings specialize the parameterized transform foundation. They are
not universal restrictions on its equality, binding signatures, programs,
store disciplines, worlds, or firing grains. No C implementation result is
claimed by this entry.

## Target criterion and onto theorem

`CleanFragment.Certificate` states local properties of actual target rows:
knowledge has a ground solution; every present row has a closed process value;
and every ground solution determines that value up to `Similar`. It assumes
neither a source process nor an execution correspondence. Unused declarations,
absent occurrence labels and other consistent knowledge are not restricted.

The finite occurrence inventory constructs a canonical rho readback. The
theorem `clean_iff_representable` identifies this local domain with the whole
existing closed-row representation domain. `clean_domain_isGreatest` gives
the precise greatest-domain property **relative to that representation
criterion**. It does not classify every behaviourally rho-equivalent transform
state or assert a largest fragment across different transform instances.

`quotientEquiv` is the onto equivalence:

    rho processes / source equations
                   ≃
    all clean target states / equality of canonical process inventories

The target equivalence is characterized by `same_iff_inventory` and
`same_iff_common_process`. It forgets administrative layout and knowledge
invisible to this process representation. It is stronger than the separately
studied weak barbed bisimilarity; the two relations are not identified here.
Raw compiler surjectivity is false: `Controls.metadata_not_literal_image`
exhibits a clean state with a real extra equation, while `metadata_is_covered`
shows it is included by the quotient theorem.

## Execution and observation map

| Result | Meaning and boundary |
|---|---|
| `clean_closed`, `every_firing_lifts` | Every actual admitted firing starting clean remains clean; no extra transition filter is imposed. |
| `move_reads`, `runs_read` | A firing is one source reduction or unchanged canonical readback; finite runs read as source runs. |
| `source_step_lifts`, `source_runs_lift` | Source reductions and runs have actual target implementations from every clean representative. |
| `source_step_iff_reaction` | Exactly one source reduction corresponds to finite administration followed by one actual communication. |
| `quotient_reduction_iff` | `quotientEquiv` preserves and reflects the resulting reduction graphs. |
| `administrative_bound` | Administrative work is bounded by the represented term-spine measure, rather than allowed to diverge silently. |
| `compile_parallel`, `parallel_respects` | The actual tensor remains inside the domain, compilation preserves parallel composition, and process-inventory equality respects it. |
| `reachable_outputs` | Reachable outputs agree on each declared closed channel. |
| `indexed_barbed_iff` | Existing indexed weak barbed bisimilarities agree on arbitrary clean points, with every output on an observed channel counted as a barb. |
| `point_divergence_iff_source` | Infinite target and source executions correspond. |

The barbed theorem does not assert congruence under arbitrary transform
contexts, programs or observers. In particular, observations of unrelated
target metadata are outside the declared source observation.

## Executable support and controls

`compile` is a function on the existing source syntax.
`Certificate.inventory` and `Certificate.readback` compute from supplied row
values. Selecting such values from mere semantic `Clean` membership uses
choice; this package does not provide a general cleanliness decision procedure
or an unrestricted contextual unification solver. The existing certified
communication-admission cases remain available from `ByInstantiation.Decision`.

`CleanFragment.Controls` checks real communication with name-equivalent
channels, silent heating, duplicate occurrences, extra knowledge outside the
literal compiler image, and a genuine divergent source process. Negative
controls exclude inconsistent knowledge, undetermined rows and a quote
crossing outside the selected sealed carrier. Set support erases multiplicity
and cannot recover the declared process meaning. Another quotation policy or
observer may justify a different domain; no uniqueness of quotation design
is claimed.
-/
