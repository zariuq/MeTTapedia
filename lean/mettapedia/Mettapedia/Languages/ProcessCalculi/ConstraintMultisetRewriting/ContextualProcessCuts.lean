import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInformation

/-!
# Common-frame event deltas and original guarded prefixes

The delta of an event contains its actual per-use port equations and tells.
The earlier common-frame problem plus this delta reconstructs its original
guard problem. These data are suitable for cut-indexed conjunctions without
silently importing the final equation store into an earlier guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualGuardMatching

variable {S : Signature} {Local O V W : Type} {locals : Local → MetaArity S}
  {declarations : V → MetaArity S} {later : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

def Event.added (event : Event locals (O := O) declarations Γ sort) :
    EquationStore (Term (signature S declarations) Γ sort) :=
  ContextualActivatedStep.useEquations event.rule.take event.takenViews ++
    ContextualActivatedStep.useEquations event.rule.read event.readViews ++ event.rule.tell

theorem Event.map_added (event : Event locals (O := O) declarations Γ sort)
    (change : Assignment declarations later) :
    (event.map change).added = ContextualFrameUnifier.mapProblem change event.added := by
  simp only [Event.added, Event.map, RuleInstance.map,
    ContextualTransportedActivation.map_append, ContextualTransportedActivation.map_useEquations]
  rfl

def addedAll (catalogue : List (Event locals (O := O) declarations Γ sort)) :
    EquationStore (Term (signature S declarations) Γ sort) := catalogue.flatMap Event.added

theorem addedAll_map (catalogue : List (Event locals (O := O) declarations Γ sort))
    (change : Assignment declarations later) :
    addedAll (catalogue.map (Event.map change)) = ContextualFrameUnifier.mapProblem change (addedAll catalogue) := by
  induction catalogue with
  | nil => rfl
  | cons event rest earlier =>
      simp only [addedAll, List.map_cons, List.flatMap_cons,
        ContextualTransportedActivation.map_append] at earlier ⊢
      rw [Event.map_added, earlier]

variable [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

set_option backward.isDefEq.respectTransparency false in
theorem prepared_problem_is_prefix_and_delta {before : Endpoint locals O Γ sort}
    (prepared : Prepared locals before) :
    (preparedEvent prepared).problem =
      ContextualFrameUnifier.mapProblem (show Assignment before.declarations prepared.target.declarations from
        (ContextualProcessTransport.captureExtension prepared).assignment)
        before.inventory.configuration.equations ++ (preparedEvent prepared).added := by
  dsimp only [Prepared.target]
  have transported := ContextualTransportedActivation.transported_problem locals before.declarations
    (ContextualComputedFreshFrame.includeSource prepared.update) before.occupied prepared.selection
    prepared.rule before.inventory.rows before.inventory.configuration
  have unfolded : (preparedEvent prepared).problem =
      ContextualFrameUnifier.mapProblem (show Assignment _ prepared.target.declarations from
        ContextualComputedFreshFrame.includeSource prepared.update)
        (ContextualActivatedStep.frame locals before.declarations before.inventory.configuration).equations ++
          (preparedEvent prepared).added := by
    dsimp only [Prepared.target]
    with_unfolding_all simpa only [preparedEvent, originalEvent, Event.map, Event.added,
      ContextualTransportedActivation.configurationMap,
      ContextualTransportedActivation.preparedRule, RuleInstance.map, List.append_assoc] using transported
  apply unfolded.trans
  apply congrArg (fun problem => problem ++ (preparedEvent prepared).added)
  dsimp only [ContextualProcessTransport.captureExtension]
  rw [ContextualComputedFreshFrame.capturedDeclarationExtension_assignment]
  exact ContextualComputedFreshFrame.map_compose
    (ContextualSelectionViews.capturedTarget locals before.declarations)
    (ContextualComputedFreshFrame.includeSource prepared.update) _

/-- The catalogue's common-frame deltas reconstruct the whole terminal
equation list, with its original order before any model-level quotient. -/
theorem final_equations_from_deltas {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    target.inventory.configuration.equations = incomingProblem certificate ++ addedAll (events certificate) := by
  induction certificate with
  | nil =>
      change source.inventory.configuration.equations =
        ContextualFrameUnifier.mapProblem (generator source.declarations) source.inventory.configuration.equations ++ []
      simp [ContextualFrameUnifier.mapProblem, instantiate_identity]
  | snoc past next earlier =>
      have initial : incomingProblem (.snoc past next) =
          ContextualFrameUnifier.mapProblem (show Assignment _ next.target.declarations from
            (ContextualProcessTransport.captureExtension next).assignment)
            (incomingProblem past) := by
        unfold incomingProblem
        have composed := ContextualProcessTransport.assignment_append past (.snoc (.nil _) next)
        have single : ContextualProcessTransport.assignment (.snoc (.nil _) next) =
            (ContextualProcessTransport.captureExtension next).assignment := by rfl
        rw [single] at composed
        simpa only [Certificate.append, ContextualComputedFreshFrame.map_compose] using
          (congrArg (fun change => ContextualFrameUnifier.mapProblem change
            source.inventory.configuration.equations) composed)
      change (preparedEvent next).problem = _
      rw [prepared_problem_is_prefix_and_delta, earlier, ContextualTransportedActivation.map_append, initial,
        events]
      simp only [addedAll, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      with_unfolding_all rw [show List.flatMap Event.added
          (List.map (Event.map (later := next.target.declarations)
            (ContextualProcessTransport.captureExtension next).assignment) (events past)) =
          ContextualFrameUnifier.mapProblem (ContextualProcessTransport.captureExtension next).assignment
            (addedAll (events past)) from addedAll_map _ _]
      simp only [List.append_assoc]
      rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
