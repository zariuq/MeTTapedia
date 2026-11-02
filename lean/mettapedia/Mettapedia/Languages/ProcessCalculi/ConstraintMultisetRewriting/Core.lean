import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationExtensions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventExecution

/-!
# The transform candidate: equations, occurrences and guarded interaction

The atomic calculus is `OccurrenceStep`: a configuration contains an equation
store and a finite set of physical occurrences. A freshened `RuleInstance`
has take, read, tell, check and produce ports. `Selection.Valid` checks their
shape, resource availability, joint consistency and universally entailed
guards; `Selection.result` preserves the surviving occurrences under the same
joint constraints. Equal labels never identify occurrence identities.

This entry uses those definitions without adding a second step relation.
For scoped terms, `ContextualTransportedActivation.SemanticAdmission` checks
the actual prepared views, original guards and solvability in any future
declaration family. Within the structural-pattern fragment it is equivalent
to an actual admitted, completed worklist return. `realize_semantic_admission`
constructs the full inventory endpoint and firing from that semantic data;
each actual firing recovers it. `ContextualGuardedStep.Valid` is the older
fixed-family restriction and can reject a solution needing a fresh helper.
Pure arity-preserving declaration extensions preserve and reflect semantic
admission, including output shape and guards at the same original cut.
`ContextualPairFrames.realize_causal_pair` constructs two actual scoped
events from common producer-origin constraints, without supplied solver
returns or paths. A consumer can read or take newly produced live data;
those uses share the producer's variables instead of freshening them as
schemas. The complete second problem retains the first event's equations.
`realize_ordered_pair` recovers the independently available-input profile.
`realize_two_orders` constructs both orders and preserves and reflects all
final equality, absence and occurrence-count questions over the common event
interface. It retains original and intermediate guard obligations, and is
restricted to independently available inputs in the structural-pattern
fragment. Arbitrary surrounding continuations, joined-schema guards,
authority integration and comparison of intermediate effect histories remain
stronger targets. A concrete causal count guard holds before taking its one
matching occurrence and fails afterward; rebasing it to the final world is
an incorrect rejection of a valid execution. Joint inconsistency also does
not erase an already executed prefix.

The independent lambda comparison is a concrete client of these steps.
`LambdaComparison.source_step_iff_executes` realizes every rule of the
context-indexed four-rule lambda source through a completed worklist run.
`LambdaExecution.finite_execution_iff` compares finite source reductions
with a selected semantic transform profile over retained raw endpoints.
The latter carries old equations, live output terms and scope inventories
across changing binder depths. Every old joint solution extends through a
step. `LambdaExecution.finite_execution_with_solvers_iff` supplies actual
incremental worklist computations along these paths. Completed prefixes
expose each next represented input as a supported pattern problem; raw
compound applications are not silently classified as patterns. This result
does not choose Prime's demanded evaluation policy or supply effects and
sharing from ordinary unrestricted beta reduction.

`ContextualCommunicationAdequacy.source_path_iff_firings` compares finite
paths of the declared intrinsic rho profile with retained occurrence
firings. Its ordinary substitution and optional free Drop must remain
distinct from paper-faithful semantic COMM substitution. The profile
controls show that a public absence observer distinguishes communication
from a later activation stage. `QuotedLambdaRetained.finite_execution_with_solvers_iff`
now supplies the mixed lambda/quotation profile: lexical captures survive,
quotation is inert, and explicit activation runs through the same retained
scope/equation inventories and incremental worklist. Pure lambda paths agree
with the previous client. This is not yet demanded sharing, effects, general
syntax inspection or composition with the communication/query clients.

The theorem below supplies a guarded two-way diamond. Each event is admitted
at its original cut, both sets of equations are jointly consistent, physical
commits are independent, and the other event's writes cannot match an
occurrence-dependent guard. Equations may be nontrivial and share variables.
Resource disjointness alone does not establish these information conditions.
After the diamond, every fixed continuation schedule sees the same solutions
and physical occurrences. The theorem does not erase intermediate effects or
authorize arbitrary rule fusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- Independently admitted events can compose when their information and
resource obligations remain compatible. Both executions are constructed. -/
theorem independently_ready_commute
    (first second : ConditionalSchedule.Firing T O) (before : Configuration T O)
    (firstReady : first.2.Valid A label first.1 before)
    (secondReady : second.2.Valid A label second.1 before)
    (resources : Independent label first.2.commit second.2.commit)
    (joint : A.Consistent ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2))
    (firstChecks : ∀ check ∈ first.1.checks,
      Check.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label second.2 check)
    (secondChecks : ∀ check ∈ second.1.checks,
      Check.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label first.2 check) :
    second.2.Valid A label second.1 (first.2.result label first.1 before) ∧
    first.2.Valid A label first.1 (second.2.result label second.1 before) ∧
    SameUpTo A (second.2.result label second.1 (first.2.result label first.1 before))
      (first.2.result label first.1 (second.2.result label second.1 before)) := by
  have physical := (independent_iff_both_orders firstReady.occurrences secondReady.occurrences).mp resources
  have jointModels (σ : S) :
      A.Models σ ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2) ↔
        A.Models σ ((before.equations ++ added label second.1 second.2) ++ added label first.1 first.2) := by
    simp only [A.models_append]
    tauto
  have secondAfter : second.2.Valid A label second.1 (first.2.result label first.1 before) := by
    refine ⟨secondReady.take_distinct, secondReady.output_distinct, secondReady.take_length,
      secondReady.read_length, secondReady.outputs, physical.1, ?_, ?_⟩
    · simpa only [problem_eq, result_equations] using joint
    · intro check member σ model
      rw [problem_eq, result_equations] at model
      have old : A.Models σ (second.2.problem label second.1 before) := by
        rw [problem_eq]
        exact (A.models_append _ _ _).mpr
          ⟨((A.models_append _ _ _).mp ((A.models_append _ _ _).mp model).1).1,
            ((A.models_append _ _ _).mp model).2⟩
      exact (Check.holds_fire_iff_of_ignored A before.present first.2 check
        (secondChecks check member) σ model).mpr (secondReady.checks check member σ old)
  have firstAfter : first.2.Valid A label first.1 (second.2.result label second.1 before) := by
    refine ⟨firstReady.take_distinct, firstReady.output_distinct, firstReady.take_length,
      firstReady.read_length, firstReady.outputs, physical.2, ?_, ?_⟩
    · rw [problem_eq, result_equations]
      exact (A.equivalent_consistent jointModels).mp joint
    · intro check member σ model
      rw [problem_eq, result_equations] at model
      have original := (jointModels σ).mpr model
      have old : A.Models σ (first.2.problem label first.1 before) := by
        rw [problem_eq]
        exact ((A.models_append _ _ _).mp original).1
      exact (Check.holds_fire_iff_of_ignored A before.present second.2 check
        (firstChecks check member) σ original).mpr (firstReady.checks check member σ old)
  refine ⟨secondAfter, firstAfter, ?_, fire_comm firstReady.occurrences secondReady.occurrences⟩
  intro σ
  simpa only [result_equations] using jointModels σ

/-- Equal endpoint observations preserve admission of arbitrary fixed
continuations, including their later equality, absence and count checks. -/
theorem continuation_after_commuting
    (first second : ConditionalSchedule.Firing T O) (before : Configuration T O)
    (same : SameUpTo A (second.2.result label second.1 (first.2.result label first.1 before))
      (first.2.result label first.1 (second.2.result label second.1 before)))
    (continuation : List (ConditionalSchedule.Firing T O)) :
    ConditionalSchedule.Executable A label
        (second.2.result label second.1 (first.2.result label first.1 before)) continuation ↔
      ConditionalSchedule.Executable A label
        (first.2.result label first.1 (second.2.result label second.1 before)) continuation :=
  executable_congr A label continuation same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core
