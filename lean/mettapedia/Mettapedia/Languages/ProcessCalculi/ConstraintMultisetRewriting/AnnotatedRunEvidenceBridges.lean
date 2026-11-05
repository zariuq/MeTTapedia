import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplateExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEvents

/-!
# Contextual firing bridges into evidence-rich histories

The contextual execution records already contain much of the evidence that a
history needs.  A solver-backed conditional firing contains its rule,
selection, residual update and the proof that the worklist computed it.  A
template firing additionally contains its authored `sourceRule` and a proof
that the executed rule is its lowering.  This module projects those records
to the thin firing alphabet used by `AnnotatedRuns`; it does not copy or alter
the contextual execution structures.

Predicate-census observations are not invented by these bridges.  Their thin
projection therefore has an empty `queries` field.  A source compiler that has
actual census observations must attach them in its own evidence adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidenceBridges

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily

universe uActor uWorld uRound uAnswers uFreshening uTask

variable {S : Signature} {Local Shared Inner O : Type} {Γ : Ctx S} {sort : S.Srt}

section ContextualFirings

variable [DecidableEq Local] [DecidableEq Inner] [DecidableEq O]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- The existing solver-backed firing, viewed as R22's thin firing.  Its
residual update and computation proof remain in the rich event. -/
def conditionalBase (locals : Local → MetaArity S)
    {before : ContextualConditionalExecution.State locals O Γ sort}
    (firing : ContextualConditionalExecution.Firing locals before) :
    AnnotatedRuns.Firing
      (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)
      Unit O :=
  ⟨firing.rule, [], firing.selection⟩

@[simp] theorem conditionalBase_rule (locals : Local → MetaArity S)
    {before : ContextualConditionalExecution.State locals O Γ sort}
    (firing : ContextualConditionalExecution.Firing locals before) :
    (conditionalBase locals firing).rule = firing.rule := rfl

@[simp] theorem conditionalBase_queries (locals : Local → MetaArity S)
    {before : ContextualConditionalExecution.State locals O Γ sort}
    (firing : ContextualConditionalExecution.Firing locals before) :
    (conditionalBase locals firing).queries = [] := rfl

@[simp] theorem conditionalBase_selection (locals : Local → MetaArity S)
    {before : ContextualConditionalExecution.State locals O Γ sort}
    (firing : ContextualConditionalExecution.Firing locals before) :
    (conditionalBase locals firing).selection = firing.selection := rfl

/-- Metadata not already stored by `ContextualConditionalExecution.Firing`.
The firing itself remains the solver witness: it retains `update` and
`computed`. -/
structure ConditionalEvent (locals : Local → MetaArity S)
    (before : ContextualConditionalExecution.State locals O Γ sort)
    (Actor : Type uActor) (World : Type uWorld) (Round : Type uRound)
    (Answers : Type uAnswers) where
  firing : ContextualConditionalExecution.Firing locals before
  actor : Option Actor
  world : World
  round : Round
  queryEvidence : Answers

def ConditionalEvent.forget (locals : Local → MetaArity S)
    {before : ContextualConditionalExecution.State locals O Γ sort}
    {Actor : Type uActor} {World : Type uWorld} {Round : Type uRound}
    {Answers : Type uAnswers} :
    ConditionalEvent locals before Actor World Round Answers →
      AnnotatedRuns.Firing
        (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)
        Unit O :=
  fun event => conditionalBase locals event.firing

/-- The actual residual solver update already stored in the contextual
firing. -/
def ConditionalEvent.witness (locals : Local → MetaArity S)
    {before : ContextualConditionalExecution.State locals O Γ sort}
    {Actor : Type uActor} {World : Type uWorld} {Round : Type uRound}
    {Answers : Type uAnswers}
    (event : ConditionalEvent locals before Actor World Round Answers) :=
  event.firing.update

/-- The retained witness was computed by the actual worklist; it is not an
unrelated proof object supplied alongside the firing. -/
theorem ConditionalEvent.witness_computed (locals : Local → MetaArity S)
    {before : ContextualConditionalExecution.State locals O Γ sort}
    {Actor : Type uActor} {World : Type uWorld} {Round : Type uRound}
    {Answers : Type uAnswers}
    (event : ConditionalEvent locals before Actor World Round Answers) :
    letI := before.equality
    ContextualFrameWorklist.run event.firing.fuel
      (ContextualActivatedStep.target locals before.declarations)
      (ContextualConditionalExecution.information locals before.declarations before.occupied
        event.firing.selection event.firing.rule before.rows before.equations) =
      .residual (event.witness locals) :=
  event.firing.computed

/-- The authored template firing, viewed as the same thin event. -/
def templateBase (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    {before : ContextualExecution.Endpoint (ContextualTemplateSource.Expanded locals inners) O Γ sort}
    (firing : ContextualTemplatePublication.Firing locals inners before) :
    AnnotatedRuns.Firing
      (Term (signature S
        (ContextualActivatedStep.source (ContextualTemplateSource.Expanded locals inners)
          before.declarations)) Γ sort)
      Unit O :=
  ⟨firing.execution.rule, [], firing.selection⟩

@[simp] theorem templateBase_selection (locals : Local → MetaArity S)
    (inners : Inner → MetaArity S)
    {before : ContextualExecution.Endpoint (ContextualTemplateSource.Expanded locals inners) O Γ sort}
    (firing : ContextualTemplatePublication.Firing locals inners before) :
    (templateBase locals inners firing).selection = firing.selection := rfl

/-- The thin rule is exactly the lowering of the authored schema retained by
the rich firing. -/
theorem templateBase_rule_is_source_lowering (locals : Local → MetaArity S)
    (inners : Inner → MetaArity S)
    {before : ContextualExecution.Endpoint (ContextualTemplateSource.Expanded locals inners) O Γ sort}
    (firing : ContextualTemplatePublication.Firing locals inners before) :
    (templateBase locals inners firing).rule =
      firing.sourceRule.lower locals inners before.declarations :=
  firing.compiled

/-- Additional runtime provenance around an authored template firing.  The
schema is not duplicated: it is `firing.sourceRule`. -/
structure TemplateEvent (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    (before : ContextualExecution.Endpoint (ContextualTemplateSource.Expanded locals inners) O Γ sort)
    (Freshening : Type uFreshening) (Actor : Type uActor) (World : Type uWorld)
    (Round : Type uRound) (Answers : Type uAnswers) where
  firing : ContextualTemplatePublication.Firing locals inners before
  freshening : Freshening
  actor : Option Actor
  world : World
  round : Round
  queryEvidence : Answers

def TemplateEvent.forget (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    {before : ContextualExecution.Endpoint (ContextualTemplateSource.Expanded locals inners) O Γ sort}
    {Freshening : Type uFreshening} {Actor : Type uActor} {World : Type uWorld}
    {Round : Type uRound} {Answers : Type uAnswers} :
    TemplateEvent locals inners before Freshening Actor World Round Answers →
      AnnotatedRuns.Firing
        (Term (signature S
          (ContextualActivatedStep.source (ContextualTemplateSource.Expanded locals inners)
            before.declarations)) Γ sort)
        Unit O :=
  fun event => templateBase locals inners event.firing

/-- Schema provenance is already part of the authored template firing. -/
def TemplateEvent.schema (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    {before : ContextualExecution.Endpoint (ContextualTemplateSource.Expanded locals inners) O Γ sort}
    {Freshening : Type uFreshening} {Actor : Type uActor} {World : Type uWorld}
    {Round : Type uRound} {Answers : Type uAnswers}
    (event : TemplateEvent locals inners before Freshening Actor World Round Answers) :=
  event.firing.sourceRule

theorem TemplateEvent.schema_lowers_to_thin_rule
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    {before : ContextualExecution.Endpoint (ContextualTemplateSource.Expanded locals inners) O Γ sort}
    {Freshening : Type uFreshening} {Actor : Type uActor} {World : Type uWorld}
    {Round : Type uRound} {Answers : Type uAnswers}
    (event : TemplateEvent locals inners before Freshening Actor World Round Answers) :
    (event.forget locals inners).rule =
      (event.schema locals inners).lower locals inners before.declarations :=
  templateBase_rule_is_source_lowering locals inners event.firing

end ContextualFirings

section Attempts

variable [DecidableEq Local] [DecidableEq Shared] [DecidableEq O]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- Turn an actual non-firing contextual attempt into an attempt-history
record.  The answer table is the actual finite census table, and the theorem
below connects its zero-state-change interpretation to the source attempt. -/
def attemptRecord {Query : Type} (queries : Query → MetaArity S)
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {search : ContextualAttemptOutcomes.Search queries locals captures (O := O) (Γ := Γ) (sort := sort)}
    {mode : ContextualAttemptOutcomes.Mode} {T EffectSubst EffectO : Type}
    [DecidableEq Query] [DecidableEq EffectO]
    {action : SubstitutionAction T EffectSubst} {label : EffectO → T}
    {code : List (StagedSourceEffects.Instruction T EffectSubst EffectO)}
    {before after : Configuration T EffectO} {outcome : ContextualAttemptOutcomes.Outcome}
    {Task : Type uTask} {World : Type uWorld} {Round : Type uRound}
    (_actual : ContextualAttemptOutcomes.Attempt search mode action label code before outcome after)
    (nonfiring : outcome ≠ .fired) (task : Task) (world : World) (round : Round)
    (charge : Nat) :
    AnnotatedRunEvidence.AttemptRecord
      (Finset (Fin search.patterns.length → O)) Task World Round where
  outcome := outcome
  nonfiring := nonfiring
  answers := search.entries
  task := task
  world := world
  round := round
  charge := charge

theorem attemptRecord_unchanged {Query : Type} (queries : Query → MetaArity S)
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {search : ContextualAttemptOutcomes.Search queries locals captures (O := O) (Γ := Γ) (sort := sort)}
    {mode : ContextualAttemptOutcomes.Mode} {T EffectSubst EffectO : Type}
    [DecidableEq Query] [DecidableEq EffectO]
    {action : SubstitutionAction T EffectSubst} {label : EffectO → T}
    {code : List (StagedSourceEffects.Instruction T EffectSubst EffectO)}
    {before after : Configuration T EffectO} {outcome : ContextualAttemptOutcomes.Outcome}
    (actual : ContextualAttemptOutcomes.Attempt search mode action label code before outcome after)
    (nonfiring : outcome ≠ .fired) : after = before :=
  actual.nonfiring_unchanged nonfiring

end Attempts

section Standing

variable [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- Standing-rule provenance is the installation occurrence already carried
by the invocation. -/
def standingActor {atom : S.Srt} {before : ContextualStandingEvents.World S atom O Γ}
    (invocation : ContextualStandingEvents.Invocation before) : O :=
  invocation.installation

theorem standingActor_survives {atom : S.Srt}
    {before : ContextualStandingEvents.World S atom O Γ}
    (invocation : ContextualStandingEvents.Invocation before) :
    standingActor invocation ∈ invocation.target.current.present :=
  invocation.installation_kept

end Standing

#print axioms ConditionalEvent.witness_computed
#print axioms TemplateEvent.schema_lowers_to_thin_rule
#print axioms attemptRecord_unchanged
#print axioms standingActor_survives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidenceBridges
