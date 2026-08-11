import Mettapedia.GSLT.LanguageDef.ProofGSLTFiniteTraceAuthority
import Mettapedia.GSLT.LanguageDef.ProofGSLTUltrainfinite

/-!
# Infinitary recurrence from checked GSLT edges

Finite traces certify finite prefixes, even when the transition graph has
cycles.  A claim about a daemon or other infinite execution needs more: local
edge legality and a global progress argument.

This module composes those two existing ProofGSLT mechanisms.  Controller
actions carry the same local evidence accepted by a `StepAuthority`; a finite
Büchi progress measure proves that accepting states recur indefinitely.  An
accepted certificate therefore denotes an actual infinite execution of the
admitted GSLT, not merely recurrence in an unrelated Boolean transition
table.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.GSLT

universe uAuthority uCertificate

/-- Turn a checked GSLT edge authority into the executable labeled system
consumed by the finite Büchi checker.  An action names both its target and the
local evidence for reaching it. -/
def auditedLabeledSystem {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool) :
    LabeledSystem theory.Term
      (TraceLink theory stepAuthority.Certificate) where
  step := fun source action target =>
    decide (action.target = target) &&
      stepAuthority.check ⟨source, action.target⟩ action.evidence
  accepting := accepting

/-- Every transition accepted by the generated Boolean system is a genuine
edge of the admitted GSLT. -/
theorem auditedLabeledSystem_step_sound
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool)
    {source target : theory.Term}
    {action : TraceLink theory stepAuthority.Certificate}
    (accepted :
      (auditedLabeledSystem stepAuthority accepting).step
        source action target = true) :
    theory.Step source target := by
  have acceptedParts :
      decide (action.target = target) = true ∧
        stepAuthority.check ⟨source, action.target⟩ action.evidence = true := by
    simpa only [auditedLabeledSystem, Bool.and_eq_true] using accepted
  have targetEq : action.target = target := of_decide_eq_true acceptedParts.1
  exact targetEq ▸ stepAuthority.sound acceptedParts.2

/-- A controller whose actions are locally checkable GSLT edge witnesses. -/
structure RecurrentTraceClaim (theory : GSLT)
    (StepCertificate : Type uCertificate) where
  root : theory.Term
  controller :
    MemorylessController theory.Term (TraceLink theory StepCertificate)

/-- Semantic meaning of recurrent execution: every execution following the
controller consists of genuine GSLT steps and visits the declared accepting
states beyond every finite prefix. -/
def RecurrentTraceClaim.Meaning {theory : GSLT}
    {StepCertificate : Type uCertificate}
    (accepting : theory.Term → Bool)
    (claim : RecurrentTraceClaim theory StepCertificate) : Prop :=
  ∀ execution : ControlledExecution claim.controller claim.root,
    (∀ index,
      theory.Step (execution.state index) (execution.state (index + 1))) ∧
    (∀ lowerBound, ∃ visit, lowerBound ≤ visit ∧
      accepting (execution.state visit) = true)

/-- The Büchi checker generated from a local GSLT edge authority.  Its finite
certificate proves both genuine infinite GSLT execution and recurrence of the
chosen observable. -/
def recurrentTraceAuthority
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (authorityId : AuthorityId)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool) :
    SemanticAuthority AuthorityId
      (RecurrentTraceClaim theory stepAuthority.Certificate) where
  id := authorityId
  Certificate := ProgressMeasure theory.Term
  check := fun claim measure =>
    measure.check (auditedLabeledSystem stepAuthority accepting)
      claim.controller claim.root
  Meaning := RecurrentTraceClaim.Meaning accepting
  sound := by
    intro claim measure accepted execution
    have valid : measure.Valid
        (auditedLabeledSystem stepAuthority accepting)
        claim.controller claim.root :=
      (ProgressMeasure.check_eq_true_iff
        (auditedLabeledSystem stepAuthority accepting)
        claim.controller measure claim.root).mp accepted
    have activeAt : ∀ index,
        claim.controller.active (execution.state index) = true := by
      intro index
      induction index with
      | zero =>
          rw [execution.starts]
          exact valid.1.1
      | succ index inductionHypothesis =>
          have nextActive :=
            (valid.1.2 (execution.state index) inductionHypothesis).2
          rw [execution.follows index]
          exact nextActive
    constructor
    · intro index
      have selected :=
        (valid.1.2 (execution.state index) (activeAt index)).1
      have genuine := auditedLabeledSystem_step_sound
        stepAuthority accepting selected
      rw [execution.follows index]
      exact genuine
    · exact ProgressMeasure.buchi_sound valid execution

end Mettapedia.GSLT.LanguageDef.ProofGSLT
