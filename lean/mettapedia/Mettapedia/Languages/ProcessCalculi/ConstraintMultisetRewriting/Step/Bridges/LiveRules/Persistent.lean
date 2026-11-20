import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Correspondences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derivations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Transitions

/-!
# Actual runs of the persistent rule-store profile

The code system is `ofRules`: its rules have no closure arguments, rule
queries or rule-store updates. A finite held part and an arbitrary ambient
part therefore give the old program's transitions. The actual run adapters
retain endpoints and event counts. Event multiplicities require an additional
condition or the origin fibres developed separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules

open RuleSyntax RuleSyntax.RuleOccurrences
open LogicOverTheStep.StepSpan
open FragmentsOfTheStep.TransitionMaps
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) {P Q : Program Tm}
  {ids : Finset R} {code : R → Rule Tm} (offers : Offers Q ids code) (zone : R → Z)

include offers

theorem persistentBisimulation :
    FunctionalBisimulation (Succ (step X O E (P ∪ Q)).toStep)
      (Succ (rstep X O R E (ofRules Z) P).toStep)
      (fun state => holding state ids code zone) where
  zig moved := (program_eq R X E offers zone _ _).mpr moved
  zag moved := by
    obtain ⟨after, same, projected⟩ := holding_closed R X E offers zone moved
    exact ⟨after, projected, same.symm⟩

def persistentTranslation :
    OperationalTranslation (Execution.theory (step X O E (P ∪ Q)).toStep)
      (Execution.theory (rstep X O R E (ofRules Z) P).toStep) :=
  Transitions.translation (persistentBisimulation X E offers zone)

def persistentRunPath {state : State Tm O} (run : (step X O E (P ∪ Q)).toStep.Run state) :
    ExecutionPath (Execution.theory (rstep X O R E (ofRules Z) P).toStep)
      (holding state ids code zone) (holding run.last ids code zone) :=
  (persistentTranslation X E offers zone).mapRoute (Execution.toPath _ run)

theorem persistentRunPath_length {state : State Tm O} (run : (step X O E (P ∪ Q)).toStep.Run state) :
    (persistentRunPath X E offers zone run).length = run.word.length := by
  rw [persistentRunPath, OperationalTranslation.mapRoute_length, Execution.toPath_length]

theorem persistentRun_lifts {state : State Tm O} (run : (step X O E (P ∪ Q)).toStep.Run state) :
    ∃ lifted : (rstep X O R E (ofRules Z) P).toStep.Run (holding state ids code zone),
      lifted.last = holding run.last ids code zone ∧ lifted.word.length = run.word.length := by
  obtain ⟨lifted, endpoint, count⟩ := Execution.path_has_run _ (persistentRunPath X E offers zone run)
  exact ⟨lifted, endpoint, count.trans (persistentRunPath_length X E offers zone run)⟩

theorem persistentPath_projects :
    ∀ {first last : RState Tm O R (Rule Tm) Z}
      (path : ExecutionPath (Execution.theory (rstep X O R E (ofRules Z) P).toStep) first last)
      (state : State Tm O), holding state ids code zone = first →
        ∃ run : (step X O E (P ∪ Q)).toStep.Run state,
          holding run.last ids code zone = last ∧ run.word.length = path.length
  | _, _, .refl _, state, same => ⟨.nil state, same, rfl⟩
  | _, _, .cons edge rest, state, same => by
      have moved := edge.down
      rw [← same] at moved
      obtain ⟨next, ⟨firing, admitted, endpoint⟩, represented⟩ :=
        (persistentBisimulation X E offers zone).zag moved
      subst endpoint
      obtain ⟨run, final, count⟩ := persistentPath_projects rest _ represented
      exact ⟨.cons firing admitted run, final, congrArg (· + 1) count⟩

theorem persistentRun_projects {state : State Tm O}
    (run : (rstep X O R E (ofRules Z) P).toStep.Run (holding state ids code zone)) :
    ∃ projected : (step X O E (P ∪ Q)).toStep.Run state,
      holding projected.last ids code zone = run.last ∧ projected.word.length = run.word.length := by
  obtain ⟨projected, endpoint, count⟩ := persistentPath_projects X E offers zone (Execution.toPath _ run) state rfl
  exact ⟨projected, endpoint, count.trans (Execution.toPath_length _ run)⟩

theorem persistent_readout_iff (state : State Tm O) (observe : State Tm O → Prop) :
    (∃ run : (step X O E (P ∪ Q)).toStep.Run state, observe run.last) ↔
      ∃ run : (rstep X O R E (ofRules Z) P).toStep.Run (holding state ids code zone),
        observe run.last.toState := by
  constructor
  · rintro ⟨run, observed⟩
    obtain ⟨lifted, endpoint, _⟩ := persistentRun_lifts X E offers zone run
    exact ⟨lifted, by simpa only [endpoint, holding] using observed⟩
  · rintro ⟨run, observed⟩
    obtain ⟨projected, endpoint, _⟩ := persistentRun_projects X E offers zone run
    exact ⟨projected, by simpa only [← endpoint, holding] using observed⟩

theorem persistent_normalization_iff (state : State Tm O) :
    Acc (fun after before => Succ (step X O E (P ∪ Q)).toStep before after) state ↔
      Acc (fun after before => Succ (rstep X O R E (ofRules Z) P).toStep before after)
        (holding state ids code zone) :=
  Transitions.normalization_iff (graph_isBisimulation_iff.mpr (persistentBisimulation X E offers zone)) rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules
