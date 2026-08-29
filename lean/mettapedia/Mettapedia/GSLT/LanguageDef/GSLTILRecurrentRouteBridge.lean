import Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
import Mettapedia.GSLT.LanguageDef.GSLTILFiniteRevisionRouteBridge

/-!
# Recurrent occurrence routes in the GSLT-IL operational waist

A checked recurrent controller carries two independent kinds of evidence:

* every demanded finite prefix is a chronological, occurrence-retaining
  execution; and
* the selected accepting predicate recurs beyond every finite bound.

This module maps the first component into the existing GSLT-IL operational
equipment without weakening the second into finite reachability.  Each
controlled execution induces a coherent family of path-retaining finite
routes.  Every prefix projects to an ordinary execution path and then to an
institutional reachability sentence.  The Buechi witness remains a separate
liveness field on the same execution.

The negative control is load-bearing: a locally valid loop with no accepting
state has every finite operational prefix, but is not recurrent.  Finite
prefix productivity therefore cannot be used as a substitute for fairness,
recurrence, stream productivity, or complete closure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge

variable {AuthorityId : Type} {theory : GSLT}
variable (stepAuthority : StepAuthority AuthorityId theory)
variable (accepting : theory.Term -> Bool)
variable (claim : RecurrentTraceClaim theory stepAuthority.Certificate)

section Prefix

variable [DecidableEq theory.Term]

/-! ## Constructive retained prefixes -/

/-- The named chronological path selected by one controlled execution.
Unlike the existing proposition-valued history, this is data and can be
projected constructively into an execution-path fibre. -/
def namedRevisionPrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root) :
    (depth : Nat) ->
      NamedHistoryPath (auditedRevisionTheory stepAuthority accepting)
        (revisionPrefix stepAuthority claim execution depth)
        claim.root (execution.state depth)
  | 0 => by
      change NamedHistoryPath
        (auditedRevisionTheory stepAuthority accepting) [] claim.root
          (execution.state 0)
      rw [execution.starts]
      exact NamedHistoryPath.nil
        (theory := auditedRevisionTheory stepAuthority accepting) claim.root
  | depth + 1 => by
      let last : NamedHistoryPath
          (auditedRevisionTheory stepAuthority accepting)
          [claim.controller.action (execution.state depth)]
          (execution.state depth) (execution.state (depth + 1)) :=
        .cons
          ⟨audited_step_at stepAuthority accepting claim locallyValid
            execution depth⟩
          (.nil (theory := auditedRevisionTheory stepAuthority accepting)
            (execution.state (depth + 1)))
      change NamedHistoryPath
        (auditedRevisionTheory stepAuthority accepting)
        (revisionPrefix stepAuthority claim execution depth ++
          [claim.controller.action (execution.state depth)])
        claim.root (execution.state (depth + 1))
      exact (namedRevisionPrefix locallyValid execution depth).append last

/-- Every recurrent prefix retains temporal occurrence identity, named
revision identity, its endpoint, and the complete path constructor spine. -/
def retainedFinitePrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    PathRetainingFiniteRoute
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root where
  occurrences := occurrencePrefix stepAuthority claim execution depth
  revisions := revisionPrefix stepAuthority claim execution depth
  target := execution.state depth
  aligned := occurrencePrefix_length stepAuthority claim execution depth
  execution := namedRevisionPrefix stepAuthority accepting claim locallyValid
    execution depth

/-- The stronger retained prefix erases exactly to the established recurrent
finite route.  It is not a second execution semantics. -/
theorem retainedFinitePrefix_erases_to_finitePrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
      depth).erase =
      finitePrefix stepAuthority accepting claim locallyValid execution depth := by
  apply FiniteRoute.ext <;> rfl

omit [DecidableEq theory.Term] in
/-- A chronological controller prefix contains exactly one occurrence per
demanded epoch. -/
theorem occurrencePrefix_length_eq_depth
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (occurrencePrefix stepAuthority claim execution depth).length = depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [occurrencePrefix, inductionHypothesis]

/-- Projection into the ordinary GSLT path fibre preserves the demanded
finite depth exactly. -/
@[simp] theorem retainedFinitePrefix_executionPath_length
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
      depth).executionPath.length = depth := by
  calc
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
        depth).executionPath.length =
        (retainedFinitePrefix stepAuthority accepting claim locallyValid
          execution depth).occurrences.length :=
      PathRetainingFiniteRoute.executionPath_length
        (theory := auditedRevisionTheory stepAuthority accepting)
        (Occurrence := ControlledOccurrence theory
          stepAuthority.Certificate)
        (source := claim.root) _
    _ = depth :=
      occurrencePrefix_length_eq_depth stepAuthority claim execution depth

/-- The one retained edge extending the prefix at a selected epoch. -/
def retainedAtomicStep
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    PathRetainingFiniteRoute
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)
      (execution.state index) :=
  PathRetainingFiniteRoute.single
    (occurrenceAt stepAuthority claim execution index)
    (claim.controller.action (execution.state index))
    (audited_step_at stepAuthority accepting claim locallyValid execution index)

/-- Successive projections form one coherent execution-path cone: demanding
one more epoch appends exactly the selected checked edge. -/
theorem retainedFinitePrefix_executionPath_succ
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
        (depth + 1)).executionPath =
      (retainedFinitePrefix stepAuthority accepting claim locallyValid execution
          depth).executionPath.append
        (retainedAtomicStep stepAuthority accepting claim locallyValid execution
          depth).executionPath := by
  let last : NamedHistoryPath
      (auditedRevisionTheory stepAuthority accepting)
      [claim.controller.action (execution.state depth)]
      (execution.state depth) (execution.state (depth + 1)) :=
    .cons
      ⟨audited_step_at stepAuthority accepting claim locallyValid execution
        depth⟩
      (.nil (theory := auditedRevisionTheory stepAuthority accepting)
        (execution.state (depth + 1)))
  change
    ((namedRevisionPrefix stepAuthority accepting claim locallyValid execution
      depth).append last).toExecutionPath =
      (namedRevisionPrefix stepAuthority accepting claim locallyValid execution
        depth).toExecutionPath.append last.toExecutionPath
  exact NamedHistoryPath.toExecutionPath_append _ _

/-! ## One recurrent execution and its finite-prefix cone -/

/-- A particular controlled execution with independently visible local-edge
authority and Buechi liveness.  Prefix paths are derived from these fields;
they are not stored as unrelated witnesses. -/
structure AuditedRecurrentExecution where
  execution : ControlledExecution claim.controller claim.root
  locallyValid : claim.controller.LocallyValid
    (auditedLabeledSystem stepAuthority accepting) claim.root
  recurrent : forall lowerBound, exists visit,
    lowerBound <= visit /\ accepting (execution.state visit) = true

namespace AuditedRecurrentExecution

/-- An accepted recurrent checker constructs the route object for any
controlled execution. -/
def ofAccepted [Fintype theory.Term]
    (authorityId : AuthorityId) (measure : ProgressMeasure theory.Term)
    (accepted :
      (recurrentChecker authorityId stepAuthority accepting).check
        claim measure = true)
    (execution : ControlledExecution claim.controller claim.root) :
    AuditedRecurrentExecution stepAuthority accepting claim where
  execution := execution
  locallyValid :=
    ((ProgressMeasure.check_eq_true_iff
      (auditedLabeledSystem stepAuthority accepting)
      claim.controller measure claim.root).mp accepted).1
  recurrent :=
    (recurrentChecker_sound authorityId stepAuthority accepting
      claim measure accepted execution).2

/-- The retained finite prefix of this exact recurrent execution. -/
def retainedPrefix
    (route : AuditedRecurrentExecution stepAuthority accepting claim)
    (depth : Nat) :
    PathRetainingFiniteRoute
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root :=
  retainedFinitePrefix stepAuthority accepting claim route.locallyValid
    route.execution depth

/-- One prefix as a loose-route witness with its exact endpoint. -/
def prefixWitness
    (route : AuditedRecurrentExecution stepAuthority accepting claim)
    (depth : Nat) :
    retainedFiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)
      claim.root (route.execution.state depth) :=
  ⟨retainedPrefix stepAuthority accepting claim route depth, rfl⟩

/-- Every finite prefix enters the operational equipment and the semantic
institution at its exact depth and endpoint. -/
theorem prefix_enters_operational_waist
    (route : AuditedRecurrentExecution stepAuthority accepting claim)
    (depth : Nat) :
    ((retainedToExecutionPathSquare
      (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)).map
        (prefixWitness stepAuthority accepting claim route depth)).length =
        depth /\
      claim.root ∈ reachesTargetSentence
        (auditedRevisionTheory stepAuthority accepting)
        (route.execution.state depth) := by
  constructor
  · exact retainedFinitePrefix_executionPath_length stepAuthority accepting
      claim route.locallyValid route.execution depth
  · exact finiteRoute_in_reachesTargetSentence
      (retainedPrefix stepAuthority accepting claim route depth).erase

/-- The complete bridge keeps finite operational productivity and unbounded
recurrence as separate conjuncts over the same execution. -/
theorem operational_prefixes_and_recurrence
    (route : AuditedRecurrentExecution stepAuthority accepting claim) :
    (forall depth,
      ((retainedToExecutionPathSquare
        (auditedRevisionTheory stepAuthority accepting)
        (ControlledOccurrence theory stepAuthority.Certificate)).map
          (prefixWitness stepAuthority accepting claim route depth)).length =
          depth /\
        claim.root ∈ reachesTargetSentence
          (auditedRevisionTheory stepAuthority accepting)
          (route.execution.state depth)) /\
      (forall lowerBound, exists visit,
        lowerBound <= visit /\
          accepting (route.execution.state visit) = true) := by
  exact ⟨fun depth => prefix_enters_operational_waist stepAuthority accepting
      claim route depth,
    route.recurrent⟩

end AuditedRecurrentExecution

end Prefix

/-! ## Negative control: finite paths are not recurrence -/

namespace Canary

open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Canary

def nonacceptingExecution :
    ControlledExecution loopController loopClaim.root :=
  loopController.canonicalExecution loopClaim.root

/-- Even the nonaccepting loop constructs an exact retained path of every
finite depth and satisfies the corresponding endpoint reachability sentence. -/
theorem nonaccepting_loop_has_every_operational_prefix :
    forall depth,
      (retainedFinitePrefix loopStepAuthority neverAccepting loopClaim
          (loop_locally_valid neverAccepting) nonacceptingExecution
          depth).executionPath.length = depth /\
        loopClaim.root ∈ reachesTargetSentence
          (auditedRevisionTheory loopStepAuthority neverAccepting)
          (nonacceptingExecution.state depth) := by
  intro depth
  exact ⟨retainedFinitePrefix_executionPath_length loopStepAuthority
      neverAccepting loopClaim (loop_locally_valid neverAccepting)
      nonacceptingExecution depth,
    finiteRoute_in_reachesTargetSentence
      (retainedFinitePrefix loopStepAuthority neverAccepting loopClaim
        (loop_locally_valid neverAccepting) nonacceptingExecution depth).erase⟩

/-- Finite operational productivity does not imply Buechi recurrence.  This
rules out treating a stream of successful prefixes as a liveness proof. -/
theorem finite_operational_prefixes_do_not_imply_recurrence :
    (forall depth,
      (retainedFinitePrefix loopStepAuthority neverAccepting loopClaim
          (loop_locally_valid neverAccepting) nonacceptingExecution
          depth).executionPath.length = depth /\
        loopClaim.root ∈ reachesTargetSentence
          (auditedRevisionTheory loopStepAuthority neverAccepting)
          (nonacceptingExecution.state depth)) /\
      ¬ loopController.BuchiWinning
        (auditedLabeledSystem loopStepAuthority neverAccepting)
        loopClaim.root :=
  ⟨nonaccepting_loop_has_every_operational_prefix,
    nonaccepting_loop_not_recurrent⟩

end Canary

#print axioms namedRevisionPrefix
#print axioms retainedFinitePrefix_erases_to_finitePrefix
#print axioms retainedFinitePrefix_executionPath_length
#print axioms retainedFinitePrefix_executionPath_succ
#print axioms AuditedRecurrentExecution.ofAccepted
#print axioms AuditedRecurrentExecution.operational_prefixes_and_recurrence
#print axioms Canary.nonaccepting_loop_has_every_operational_prefix
#print axioms Canary.finite_operational_prefixes_do_not_imply_recurrence

end Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteBridge
