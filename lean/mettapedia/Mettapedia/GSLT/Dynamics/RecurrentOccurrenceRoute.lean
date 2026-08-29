import Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCheckerCapabilities

/-!
# Recurrent GSLT certificates as productive occurrence routes

The recurrent CertificateGSLT checker already proves two distinct facts:
every controller edge is accepted by the authored local step authority, and an
accepting state recurs beyond every finite bound.  This module connects the
first fact to the occurrence-preserving finite-route algebra.

For every controlled execution and every demanded finite depth, an accepted
progress certificate constructs an exact route prefix.  Each occurrence keeps
its temporal index, source, checked action, and target, so repeated traversal
of one syntactic edge remains occurrence-distinct.  The route's history maps
to a genuine multi-step execution of the admitted GSLT.

Prefix productivity and Buechi recurrence remain separate properties.  A
locally valid nonaccepting loop has every finite prefix but no recurrent
acceptance certificate.  Neither property is promoted here to occurrence
fairness, finite closure, or complete-bag observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities

universe uAuthority uCertificate

/-! ## The audited revision theory -/

/-- The local checked edge is the revision relation.  The unit query exposes
the current term only; recurrence remains a separate observation on the same
states. -/
def auditedRevisionTheory
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool) : Theory where
  World := theory.Term
  Revision := TraceLink theory stepAuthority.Certificate
  Query := Unit
  Observation := theory.Term
  Step := fun action source target =>
    (auditedLabeledSystem stepAuthority accepting).step
      source action target = true
  query := fun world _ => world

/-- One traversal occurrence is not merely an edge label.  Its temporal
position and endpoints remain part of its identity. -/
structure ControlledOccurrence
    (theory : GSLT)
    (StepCertificate : Type uCertificate) where
  index : Nat
  source : theory.Term
  action : TraceLink theory StepCertificate
  target : theory.Term

section Prefix

variable {AuthorityId : Type uAuthority} {theory : GSLT}
variable (stepAuthority : StepAuthority.{uAuthority, uCertificate}
  AuthorityId theory)
variable (accepting : theory.Term -> Bool)
variable (claim : RecurrentTraceClaim theory stepAuthority.Certificate)

/-- The exact occurrence performed at one controller index. -/
def occurrenceAt
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    ControlledOccurrence theory stepAuthority.Certificate where
  index := index
  source := execution.state index
  action := claim.controller.action (execution.state index)
  target := execution.state (index + 1)

/-- Chronological physical occurrence prefix. -/
def occurrencePrefix
    (execution : ControlledExecution claim.controller claim.root) :
    Nat -> List (ControlledOccurrence theory stepAuthority.Certificate)
  | 0 => []
  | depth + 1 => occurrencePrefix execution depth ++
      [occurrenceAt stepAuthority claim execution depth]

/-- Chronological semantic revision prefix, defined independently from the
physical occurrence projection. -/
def revisionPrefix
    (execution : ControlledExecution claim.controller claim.root) :
    Nat -> List (TraceLink theory stepAuthority.Certificate)
  | 0 => []
  | depth + 1 => revisionPrefix execution depth ++
      [claim.controller.action (execution.state depth)]

/-- Projecting the checked action from every occurrence recovers exactly the
independently defined semantic revision prefix. -/
theorem occurrencePrefix_actions
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (occurrencePrefix stepAuthority claim execution depth).map
          (fun occurrence => occurrence.action) =
        revisionPrefix stepAuthority claim execution depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [occurrencePrefix, revisionPrefix, occurrenceAt,
        inductionHypothesis]

theorem occurrencePrefix_length
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (occurrencePrefix stepAuthority claim execution depth).length =
        (revisionPrefix stepAuthority claim execution depth).length := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [occurrencePrefix, revisionPrefix, inductionHypothesis]

/-- Traversing the same labeled edge at two different indices still produces
distinct occurrences. -/
theorem occurrenceAt_index_injective
    (execution : ControlledExecution claim.controller claim.root)
    {first second : Nat} (different : first ≠ second) :
    occurrenceAt stepAuthority claim execution first ≠
      occurrenceAt stepAuthority claim execution second := by
  intro equalOccurrences
  exact different
    (congrArg ControlledOccurrence.index equalOccurrences)

variable [DecidableEq theory.Term]

/-- Local validity propagates along every controlled execution. -/
theorem execution_active
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root) :
    forall index, claim.controller.active (execution.state index) = true := by
  intro index
  induction index with
  | zero => simpa [execution.starts] using locallyValid.1
  | succ index inductionHypothesis =>
      rw [execution.follows index]
      exact (locallyValid.2 (execution.state index) inductionHypothesis).2

/-- Every selected controlled edge is accepted by the local authored step
authority at its exact occurrence index. -/
theorem audited_step_at
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    (auditedRevisionTheory stepAuthority accepting).Step
      (claim.controller.action (execution.state index))
      (execution.state index) (execution.state (index + 1)) := by
  have selected :=
    (locallyValid.2 (execution.state index)
      (execution_active stepAuthority accepting claim locallyValid execution index)).1
  rw [execution.follows index]
  exact selected

/-- The local checker soundness projects the same indexed edge to a genuine
step of the admitted GSLT. -/
theorem semantic_step_at
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    theory.Step (execution.state index) (execution.state (index + 1)) :=
  auditedLabeledSystem_step_sound stepAuthority accepting
    (audited_step_at stepAuthority accepting claim locallyValid execution index)

/-- Every demanded prefix has a checked chronological history. -/
theorem revisionPrefix_history
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root) :
    forall depth,
      (auditedRevisionTheory stepAuthority accepting).HistoryStep
        (revisionPrefix stepAuthority claim execution depth)
        claim.root (execution.state depth) := by
  intro depth
  induction depth with
  | zero =>
      change
        (auditedRevisionTheory stepAuthority accepting).HistoryStep []
          claim.root (execution.state 0)
      rw [execution.starts]
      exact @Theory.HistoryStep.nil
        (auditedRevisionTheory stepAuthority accepting) claim.root
  | succ depth inductionHypothesis =>
      simp only [revisionPrefix]
      exact inductionHypothesis.append
        (.single
          (audited_step_at stepAuthority accepting claim locallyValid execution depth))

/-- An audited revision history is also a genuine multi-step reduction in the
underlying GSLT after its occurrence evidence is forgotten. -/
theorem history_to_multistep
    : forall {revisions : List (TraceLink theory stepAuthority.Certificate)}
        {source target : theory.Term},
      (auditedRevisionTheory stepAuthority accepting).HistoryStep
          revisions source target ->
        theory.MultiStep source target
  | [], _, _, .nil world => .refl world
  | _ :: _, _, _, .cons checked rest =>
      .step (auditedLabeledSystem_step_sound stepAuthority accepting checked)
        (history_to_multistep rest)

/-- The canonical exact finite prefix obtained from local checker validity. -/
def finitePrefix
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate) claim.root where
  occurrences := occurrencePrefix stepAuthority claim execution depth
  revisions := revisionPrefix stepAuthority claim execution depth
  target := execution.state depth
  aligned := occurrencePrefix_length stepAuthority claim execution depth
  execution := revisionPrefix_history
    stepAuthority accepting claim locallyValid execution depth

/-- The one checked occurrence which extends a finite prefix by one step. -/
def atomicStep
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (index : Nat) :
    FiniteRoute (auditedRevisionTheory stepAuthority accepting)
      (ControlledOccurrence theory stepAuthority.Certificate)
      (execution.state index) :=
  FiniteRoute.single
    (occurrenceAt stepAuthority claim execution index)
    (claim.controller.action (execution.state index))
    (execution.state (index + 1))
    (audited_step_at stepAuthority accepting claim locallyValid execution index)

/-- Demanding one more element extends the same route by exactly one checked
occurrence.  Prefixes are therefore coherent views of one run, not unrelated
finite witnesses. -/
theorem finitePrefix_succ
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    finitePrefix stepAuthority accepting claim locallyValid execution
        (depth + 1) =
      (finitePrefix stepAuthority accepting claim locallyValid execution depth).append
        (atomicStep stepAuthority accepting claim locallyValid execution depth) := by
  apply FiniteRoute.ext <;> rfl

@[simp] theorem finitePrefix_occurrences
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).occurrences =
      occurrencePrefix stepAuthority claim execution depth :=
  rfl

@[simp] theorem finitePrefix_revisions
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).revisions =
      revisionPrefix stepAuthority claim execution depth :=
  rfl

@[simp] theorem finitePrefix_target
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).target =
      execution.state depth :=
  rfl

/-- Each finite prefix reaches its endpoint by genuine GSLT reduction. -/
theorem finitePrefix_semantic
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) :
    theory.MultiStep claim.root (execution.state depth) :=
  history_to_multistep stepAuthority accepting
    (finitePrefix stepAuthority accepting claim locallyValid execution depth).execution

/-- A prefix witness fixes all observable route data, rather than asserting
mere existence of some route from the root. -/
structure ExactPrefix
    (execution : ControlledExecution claim.controller claim.root)
    (depth : Nat) where
  route : FiniteRoute (auditedRevisionTheory stepAuthority accepting)
    (ControlledOccurrence theory stepAuthority.Certificate) claim.root
  occurrences_exact : route.occurrences =
    occurrencePrefix stepAuthority claim execution depth
  revisions_exact : route.revisions =
    revisionPrefix stepAuthority claim execution depth
  target_exact : route.target = execution.state depth

/-- Exact prefix productivity: every controlled execution can answer every
finite demand with the occurrence list, semantic revisions, and endpoint fixed
by that execution. -/
def AuditedPrefixProductive : Prop :=
  forall execution : ControlledExecution claim.controller claim.root,
    forall depth,
      Nonempty (ExactPrefix stepAuthority accepting claim execution depth)

/-- Local validity is sufficient for finite-prefix productivity.  Recurrence
is not used. -/
theorem prefixProductive_of_local
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root) :
    AuditedPrefixProductive stepAuthority accepting claim := by
  intro execution depth
  exact ⟨{
    route := finitePrefix stepAuthority accepting claim locallyValid execution depth
    occurrences_exact := rfl
    revisions_exact := rfl
    target_exact := rfl }⟩

/-- Acceptance by the ordinary recurrent checker constructs every exact
finite occurrence prefix. -/
theorem recurrentChecker_acceptance_implies_prefixProductive
    [Fintype theory.Term]
    (authorityId : AuthorityId)
    (measure : ProgressMeasure theory.Term)
    (accepted :
      (recurrentChecker authorityId stepAuthority accepting).check
        claim measure = true) :
    AuditedPrefixProductive stepAuthority accepting claim := by
  have valid : measure.Valid
      (auditedLabeledSystem stepAuthority accepting)
      claim.controller claim.root :=
    (ProgressMeasure.check_eq_true_iff
      (auditedLabeledSystem stepAuthority accepting)
      claim.controller measure claim.root).mp accepted
  exact prefixProductive_of_local stepAuthority accepting claim valid.1

/-- One accepted recurrent certificate supplies both finite-prefix
productivity and genuine recurrent GSLT meaning.  The conjunction keeps the
two obligations visible. -/
theorem recurrentChecker_acceptance_consequences
    [Fintype theory.Term]
    (authorityId : AuthorityId)
    (measure : ProgressMeasure theory.Term)
    (accepted :
      (recurrentChecker authorityId stepAuthority accepting).check
        claim measure = true) :
    AuditedPrefixProductive stepAuthority accepting claim /\
      claim.Meaning accepting := by
  exact ⟨recurrentChecker_acceptance_implies_prefixProductive
      stepAuthority accepting claim authorityId measure accepted,
    recurrentChecker_sound authorityId stepAuthority accepting
      claim measure accepted⟩

end Prefix

/-! ## Positive and negative recurrence controls -/

namespace Canary

/-- One state with one always-enabled rewrite is enough to distinguish finite
prefix productivity from recurrent acceptance. -/
@[reducible] def loopTheory : GSLT where
  Term := Unit
  equations :=
    ⟨fun _ _ => True,
      ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := fun _ _ => ⟨(), trivial, trivial⟩
  rewrites_resp_right := fun _ _ => trivial

def loopStepAuthority : StepAuthority Unit loopTheory where
  id := ()
  Certificate := Unit
  check := fun _ _ => true
  sound := fun _ => trivial

def loopController :
    MemorylessController loopTheory.Term
      (TraceLink loopTheory loopStepAuthority.Certificate) where
  active := fun _ => true
  action := fun _ => ⟨(), ()⟩
  next := fun _ => ()

def loopClaim :
    RecurrentTraceClaim loopTheory loopStepAuthority.Certificate where
  root := ()
  controller := loopController

def alwaysAccepting (_ : loopTheory.Term) : Bool := true
def neverAccepting (_ : loopTheory.Term) : Bool := false

def zeroMeasure : ProgressMeasure loopTheory.Term where
  rank := fun _ => 0

theorem loop_locally_valid (accepting : loopTheory.Term -> Bool) :
    loopController.LocallyValid
      (auditedLabeledSystem loopStepAuthority accepting) loopClaim.root := by
  constructor
  · rfl
  · intro state _
    cases state
    exact ⟨rfl, rfl⟩

/-- Positive control: the accepting loop passes the real recurrent checker. -/
theorem accepting_loop_checker_accepts :
    (recurrentChecker () loopStepAuthority alwaysAccepting).check
      loopClaim zeroMeasure = true := by
  decide

/-- The accepted loop consequently exposes every finite occurrence prefix and
genuine recurrent meaning. -/
theorem accepting_loop_has_both_consequences :
    AuditedPrefixProductive loopStepAuthority alwaysAccepting loopClaim /\
      loopClaim.Meaning alwaysAccepting :=
  recurrentChecker_acceptance_consequences loopStepAuthority alwaysAccepting
    loopClaim () zeroMeasure accepting_loop_checker_accepts

/-- Negative control: a nonaccepting loop still has every checked finite
prefix. -/
theorem nonaccepting_loop_prefixProductive :
    AuditedPrefixProductive loopStepAuthority neverAccepting loopClaim :=
  prefixProductive_of_local loopStepAuthority neverAccepting loopClaim
    (loop_locally_valid neverAccepting)

/-- But finite-prefix productivity does not imply Buechi recurrence. -/
theorem nonaccepting_loop_not_recurrent :
    ¬ loopController.BuchiWinning
      (auditedLabeledSystem loopStepAuthority neverAccepting) loopClaim.root := by
  intro recurrent
  obtain ⟨visit, _lower, accepted⟩ :=
    recurrent (loopController.canonicalExecution loopClaim.root) 0
  simp [auditedLabeledSystem, neverAccepting] at accepted

theorem prefixProductivity_does_not_imply_recurrence :
    AuditedPrefixProductive loopStepAuthority neverAccepting loopClaim /\
      ¬ loopController.BuchiWinning
        (auditedLabeledSystem loopStepAuthority neverAccepting)
        loopClaim.root :=
  ⟨nonaccepting_loop_prefixProductive,
    nonaccepting_loop_not_recurrent⟩

/-- Soundness forbids any progress measure from making the nonaccepting loop
pass the recurrent checker. -/
theorem nonaccepting_loop_rejects_every_measure
    (measure : ProgressMeasure loopTheory.Term) :
    (recurrentChecker () loopStepAuthority neverAccepting).check
      loopClaim measure = false := by
  cases checked :
      (recurrentChecker () loopStepAuthority neverAccepting).check
        loopClaim measure with
  | false => rfl
  | true =>
      have meaning := recurrentChecker_sound () loopStepAuthority
        neverAccepting loopClaim measure checked
      have recurrent : loopController.BuchiWinning
          (auditedLabeledSystem loopStepAuthority neverAccepting)
          loopClaim.root := by
        intro execution lowerBound
        exact (meaning execution).2 lowerBound
      exact False.elim (nonaccepting_loop_not_recurrent recurrent)

end Canary

#print axioms occurrencePrefix_actions
#print axioms occurrenceAt_index_injective
#print axioms revisionPrefix_history
#print axioms history_to_multistep
#print axioms finitePrefix_succ
#print axioms finitePrefix_semantic
#print axioms recurrentChecker_acceptance_consequences
#print axioms Canary.accepting_loop_has_both_consequences
#print axioms Canary.prefixProductivity_does_not_imply_recurrence
#print axioms Canary.nonaccepting_loop_rejects_every_measure

end Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
