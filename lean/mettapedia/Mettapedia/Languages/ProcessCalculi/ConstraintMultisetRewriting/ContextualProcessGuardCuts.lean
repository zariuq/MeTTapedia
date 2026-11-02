import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCuts

/-!
# Exact guard cuts in the common-frame contextual catalogue

Each guard retains precisely the incoming problem and the deltas through its
own event. It does not receive the deltas of later events. The construction
is separate from the joint final consistency problem, whose conjunction may
be enumerated in any order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualGuardMatching

variable {S : Signature} {Local O V W : Type} {locals : Local → MetaArity S}
  {declarations : V → MetaArity S} {later : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

/-- The equation cut of a guard includes its event's own port equations and
tells, matching the source semantics, but never a later event's delta. -/
def OriginalCuts (incoming : EquationStore (Term (signature S declarations) Γ sort)) :
    List (Event locals (O := O) declarations Γ sort) → Prop
  | [] => True
  | event :: rest => event.problem = incoming ++ event.added ∧ OriginalCuts event.problem rest

theorem OriginalCuts.append
    {incoming : EquationStore (Term (signature S declarations) Γ sort)}
    {first second : List (Event locals (O := O) declarations Γ sort)}
    (firstCuts : OriginalCuts incoming first)
    (secondCuts : OriginalCuts (incoming ++ addedAll first) second) :
    OriginalCuts incoming (first ++ second) := by
  induction first generalizing incoming with
  | nil => simpa only [addedAll, List.flatMap_nil, List.append_nil, List.nil_append] using secondCuts
  | cons event rest earlier =>
      refine ⟨firstCuts.1, earlier firstCuts.2 ?_⟩
      rw [firstCuts.1]
      simpa only [addedAll, List.flatMap_cons, List.append_assoc] using secondCuts

theorem OriginalCuts.map
    {incoming : EquationStore (Term (signature S declarations) Γ sort)}
    {catalogue : List (Event locals (O := O) declarations Γ sort)}
    (cuts : OriginalCuts incoming catalogue) (change : Assignment declarations later) :
    OriginalCuts (ContextualFrameUnifier.mapProblem change incoming)
      (catalogue.map (Event.map change)) := by
  induction catalogue generalizing incoming with
  | nil => trivial
  | cons event rest earlier =>
      refine ⟨?_, earlier cuts.2⟩
      change ContextualFrameUnifier.mapProblem change event.problem = _
      rw [cuts.1, ContextualTransportedActivation.map_append, Event.map_added]

theorem OriginalCuts.at_cut
    {incoming : EquationStore (Term (signature S declarations) Γ sort)}
    {earlierEvents suffix : List (Event locals (O := O) declarations Γ sort)}
    {event : Event locals (O := O) declarations Γ sort}
    (cuts : OriginalCuts incoming (earlierEvents ++ event :: suffix)) :
    event.problem = incoming ++ addedAll earlierEvents ++ event.added := by
  induction earlierEvents generalizing incoming with
  | nil => simpa [addedAll] using cuts.1
  | cons earlier rest ih =>
      have found := ih cuts.2
      rw [cuts.1] at found
      simpa only [addedAll, List.flatMap_cons, List.append_assoc] using found

variable [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem incomingProblem_snoc {source middle : Endpoint locals O Γ sort}
    (past : Certificate locals source middle) (next : Prepared locals middle) :
    incomingProblem (.snoc past next) =
      ContextualFrameUnifier.mapProblem (show Assignment _ next.target.declarations from
        (ContextualProcessTransport.captureExtension next).assignment) (incomingProblem past) := by
  unfold incomingProblem
  have composed := ContextualProcessTransport.assignment_append past (.snoc (.nil _) next)
  have single : ContextualProcessTransport.assignment (.snoc (.nil _) next) =
      (ContextualProcessTransport.captureExtension next).assignment := by rfl
  rw [single] at composed
  simpa only [Certificate.append, ContextualComputedFreshFrame.map_compose] using
    (congrArg (fun change => ContextualFrameUnifier.mapProblem change source.inventory.configuration.equations) composed)

theorem original_cuts_preserved {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    OriginalCuts (incomingProblem certificate) (events certificate) := by
  induction certificate with
  | nil => trivial
  | snoc past next earlier =>
      rw [events, incomingProblem_snoc]
      apply OriginalCuts.append (OriginalCuts.map earlier _)
      refine ⟨?_, trivial⟩
      rw [prepared_problem_is_prefix_and_delta, final_equations_from_deltas past,
        ContextualTransportedActivation.map_append, addedAll_map]

/-- A selected event's guard problem is recovered from its original cut,
while its rule and watched row views remain those stored in the catalogue. -/
theorem guard_cut_recovers_original_problem {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target)
    (earlierEvents suffix : List (Event locals (O := O) target.declarations Γ sort))
    (event : Event locals (O := O) target.declarations Γ sort)
    (split : events certificate = earlierEvents ++ event :: suffix) :
    event.problem = incomingProblem certificate ++ addedAll earlierEvents ++ event.added := by
  have cuts := original_cuts_preserved certificate
  rw [split] at cuts
  exact cuts.at_cut

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
