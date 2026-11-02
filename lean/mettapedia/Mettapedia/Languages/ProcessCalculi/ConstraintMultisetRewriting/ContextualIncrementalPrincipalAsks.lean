import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalAsks

/-!
# Principal prefix answers preserve asks with residual equations

A principal answer for an earlier equation prefix reparametrizes every model
of a larger current problem. The additional equations remain in the problem,
transported with the rows and checks. The prefix answer need not itself solve
the additional equations. This does not move a later guard into an earlier
prefix or move future equations into that prefix's guard.
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

theorem Ask.prefix_principal_transport_iff {Γ : Ctx S} {sort : S.Srt}
    (prefixProblem extra : EquationStore (Term (signature S captures) Γ sort))
    (answer : Assignment captures next)
    (principal : ContextualFrameUnifier.Principal prefixProblem answer)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Ask locals (ContextualFrameUnifier.mapProblem answer (prefixProblem ++ extra))
        (fun occurrence => (rows occurrence).map locals answer) world
        (check.map (instantiate answer)) ↔ Ask locals (prefixProblem ++ extra) rows world check := by
  constructor
  · intro admitted Future future candidate solved
    have prefixModel := (ContextualFrameUnifier.models_append candidate prefixProblem extra).mp solved |>.1
    obtain ⟨residual, components⟩ := principal.factors future candidate prefixModel
    have same : candidate = Assignment.compose residual answer := funext components
    have residualModel : ContextualFrameUnifier.Models residual
        (ContextualFrameUnifier.mapProblem answer (prefixProblem ++ extra)) := by
      apply (ContextualFrameUnifier.models_mapProblem answer residual (prefixProblem ++ extra)).mpr
      rw [← same]
      exact solved
    have holds := (holds_after_capture_transport locals answer residual rows world check).mp
      (admitted Future future residual residualModel)
    rw [← same] at holds
    exact holds
  · intro admitted
    exact Ask.transport locals admitted answer

theorem Ask.completed_prefix_update_iff {Γ : Ctx S} {sort : S.Srt}
    (prefixProblem extra : EquationStore (Term (signature S captures) Γ sort))
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem prefixProblem))
    (finished : update.remaining = [])
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Ask locals (ContextualFrameUnifier.mapProblem update.answer (prefixProblem ++ extra))
        (fun occurrence => (rows occurrence).map locals update.answer) world
        (check.map (instantiate update.answer)) ↔ Ask locals (prefixProblem ++ extra) rows world check :=
  Ask.prefix_principal_transport_iff locals prefixProblem extra update.answer
    (ContextualComputedFreshFrame.completed_is_principal prefixProblem update finished) rows world check

end ContextualGuardSemantics

namespace ContextualConjunctiveAbsence

variable {Query : Type} (queries : Query → MetaArity S)

theorem Ask.prefix_principal_transport_iff {Γ : Ctx S} {sort : S.Srt}
    (prefixProblem extra : EquationStore (Term (signature S captures) Γ sort))
    (answer : Assignment captures next)
    (principal : ContextualFrameUnifier.Principal prefixProblem answer)
    (patterns : List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Ask queries locals next (ContextualFrameUnifier.mapProblem answer (prefixProblem ++ extra))
        (ContextualConjunctiveQueries.mapPatterns queries answer patterns)
        (fun occurrence => (rows occurrence).map locals answer) world ↔
      Ask queries locals captures (prefixProblem ++ extra) patterns rows world := by
  constructor
  · intro admitted Future future candidate solved
    have prefixModel := (ContextualFrameUnifier.models_append candidate prefixProblem extra).mp solved |>.1
    obtain ⟨residual, components⟩ := principal.factors future candidate prefixModel
    have same : candidate = Assignment.compose residual answer := funext components
    have residualModel : ContextualFrameUnifier.Models residual
        (ContextualFrameUnifier.mapProblem answer (prefixProblem ++ extra)) := by
      apply (ContextualFrameUnifier.models_mapProblem answer residual (prefixProblem ++ extra)).mpr
      rw [← same]
      exact solved
    have holds := (holds_after_capture_transport queries locals captures answer residual patterns rows world).mp
      (admitted Future future residual residualModel)
    rw [← same] at holds
    exact holds
  · intro admitted
    exact Ask.transport queries locals captures (prefixProblem ++ extra) patterns rows world answer admitted

theorem Ask.completed_prefix_update_iff {Γ : Ctx S} {sort : S.Srt}
    (prefixProblem extra : EquationStore (Term (signature S captures) Γ sort))
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem prefixProblem))
    (finished : update.remaining = [])
    (patterns : List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Ask queries locals update.declaration (ContextualFrameUnifier.mapProblem update.answer (prefixProblem ++ extra))
        (ContextualConjunctiveQueries.mapPatterns queries update.answer patterns)
        (fun occurrence => (rows occurrence).map locals update.answer) world ↔
      Ask queries locals captures (prefixProblem ++ extra) patterns rows world :=
  Ask.prefix_principal_transport_iff locals queries prefixProblem extra update.answer
    (ContextualComputedFreshFrame.completed_is_principal prefixProblem update finished) patterns rows world

end ContextualConjunctiveAbsence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
