import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAskTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame

/-!
# Principal solutions reflect asks for the same equation problem

Every model of a problem factors through its principal answer. An ask about
that problem can therefore be checked after the answer, with the rows and
check transported together. This is distinct from applying an answer to a
later, stronger problem: its principality does not supply the factorization
required here for the earlier problem.

The equation problem, physical world and schema-local interfaces are retained.
Completed solver updates supply the principal-answer hypothesis directly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

universe u
variable {S : Signature} {Local Shared Next : Type} {O : Type u}
  (locals : Local → MetaArity S) {captures : Shared → MetaArity S}
  {next : Next → MetaArity S}

namespace ContextualGuardSemantics

theorem Ask.principal_transport_iff {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (answer : Assignment captures next) (principal : ContextualFrameUnifier.Principal problem answer)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Ask locals (ContextualFrameUnifier.mapProblem answer problem)
        (fun occurrence => (rows occurrence).map locals answer) world (check.map (instantiate answer)) ↔
      Ask locals problem rows world check := by
  constructor
  · intro admitted Future future candidate solved
    obtain ⟨residual, components⟩ := principal.factors future candidate solved
    have same : candidate = Assignment.compose residual answer := by
      funext identity
      exact components identity
    have residualModel : ContextualFrameUnifier.Models residual
        (ContextualFrameUnifier.mapProblem answer problem) := by
      apply (ContextualFrameUnifier.models_mapProblem answer residual problem).mpr
      rw [← same]
      exact solved
    have holds := (holds_after_capture_transport locals answer residual rows world check).mp
      (admitted Future future residual residualModel)
    rw [← same] at holds
    exact holds
  · intro admitted
    exact Ask.transport locals admitted answer

theorem Ask.completed_update_iff {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem problem))
    (finished : update.remaining = [])
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Ask locals (ContextualFrameUnifier.mapProblem update.answer problem)
        (fun occurrence => (rows occurrence).map locals update.answer) world
        (check.map (instantiate update.answer)) ↔ Ask locals problem rows world check :=
  Ask.principal_transport_iff locals problem update.answer
    (ContextualComputedFreshFrame.completed_is_principal problem update finished) rows world check

end ContextualGuardSemantics

namespace ContextualConjunctiveAbsence

variable {Query : Type} (queries : Query → MetaArity S)

theorem Ask.principal_transport_iff {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (answer : Assignment captures next) (principal : ContextualFrameUnifier.Principal problem answer)
    (patterns : List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Ask queries locals next (ContextualFrameUnifier.mapProblem answer problem)
        (ContextualConjunctiveQueries.mapPatterns queries answer patterns)
        (fun occurrence => (rows occurrence).map locals answer) world ↔
      Ask queries locals captures problem patterns rows world := by
  constructor
  · intro admitted Future future candidate solved
    obtain ⟨residual, components⟩ := principal.factors future candidate solved
    have same : candidate = Assignment.compose residual answer := by
      funext identity
      exact components identity
    have residualModel : ContextualFrameUnifier.Models residual
        (ContextualFrameUnifier.mapProblem answer problem) := by
      apply (ContextualFrameUnifier.models_mapProblem answer residual problem).mpr
      rw [← same]
      exact solved
    have holds := (holds_after_capture_transport queries locals captures answer residual patterns rows world).mp
      (admitted Future future residual residualModel)
    rw [← same] at holds
    exact holds
  · intro admitted
    exact Ask.transport queries locals captures problem patterns rows world answer admitted

theorem Ask.completed_update_iff {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem problem))
    (finished : update.remaining = [])
    (patterns : List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Ask queries locals update.declaration (ContextualFrameUnifier.mapProblem update.answer problem)
        (ContextualConjunctiveQueries.mapPatterns queries update.answer patterns)
        (fun occurrence => (rows occurrence).map locals update.answer) world ↔
      Ask queries locals captures problem patterns rows world :=
  Ask.principal_transport_iff locals queries problem update.answer
    (ContextualComputedFreshFrame.completed_is_principal problem update finished) patterns rows world

end ContextualConjunctiveAbsence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
