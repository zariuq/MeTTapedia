import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedAnswerReadings

/-!
# Finished source alternatives under actual native dead-name agreement

Having a value-shaped instance is an existential row observation, with arbitrary open values and
target frames. It is invariant under dead-name extensions. It is not a definition of finishedness.
For a state that actually represents a source branch, source encoding inversion recovers syntactic
finishedness and a real store model from that instance. The existing `Hosting.finished_iff` then
recovers the full universal `StateFinished` observation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedFinishedReadings

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting
open RuleSyntax.StepWeb.HostedNative
open NativeClosedReadings HostedAnswerReadings

variable {S : Signature} {O : Type} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}

/-- An actual present conditional row has one value-shaped instance at a model of its knowledge.
The value may mention the model's declarations. -/
def HasValueInstance (N : Nodes S Γ star) (native : NativeState S O Γ star) (occurrence : O) : Prop :=
  occurrence ∈ native.state.present ∧
    ∃ (target : Frames.Frame S) (candidate : Assignment native.state.declarations target.arity)
      (value : Term (signature S target.arity) Γ star),
      ContextualResidual.Models candidate native.state.equations ∧
        ContextualConditionalRows.Matches native.locals native.state.declarations candidate
          (altN N (valueN N value) (emptyN N)) (native.state.rows occurrence)

theorem deadExtension_valueInstance_iff (N : Nodes S Γ star)
    {before after : NativeState S O Γ star} (extension : NativeDead.DeadExtension before after)
    (occurrence : O) : HasValueInstance N after occurrence ↔ HasValueInstance N before occurrence := by
  constructor
  · rintro ⟨present, target, candidate, value, model, matched⟩
    refine ⟨?_, target, Assignment.compose candidate extension.frame, value, ?_, ?_⟩
    · rwa [extension.present] at present
    · apply (ContextualResidual.models_mapProblem extension.frame candidate
        before.state.equations).mp
      intro equation member
      exact model equation (extension.equations.mem_iff.mpr member)
    · rw [extension.rows occurrence] at matched
      exact (matches_carried_iff extension.toInclusion candidate _ _).mp matched
  · rintro ⟨present, target, candidate, value, model, matched⟩
    let frame := frameExtension extension.toInclusion
    let grown : Frames.Frame S :=
      ⟨frame.Complement ⊕ target.Names,
        ContextualPrefixModels.extended frame.complementDeclarations target.arity⟩
    let inclusion := ContextualPrefixModels.inclusion frame.complementDeclarations target.arity
    let lifted : Assignment after.state.declarations grown.arity := frame.liftModel candidate
    have mapped : ContextualResidual.Models lifted
        (ContextualResidual.mapProblem extension.frame before.state.equations) :=
      (ContextualConditionalNaturality.models_liftModel_iff frame candidate
        before.state.equations).mpr model
    refine ⟨?_, grown, lifted, instantiate inclusion value, ?_, ?_⟩
    · rwa [extension.present]
    · intro equation member
      exact mapped equation (extension.equations.mem_iff.mp member)
    · rw [extension.rows occurrence]
      apply (matches_carried_iff extension.toInclusion lifted _ _).mpr
      have carried := (ContextualConditionalNaturality.matches_inclusion_iff before.locals
        frame.complementDeclarations candidate (altN N (valueN N value) (emptyN N))
        (before.state.rows occurrence)).mpr matched
      have shape : instantiate inclusion (altN N (valueN N value) (emptyN N)) =
          altN N (valueN N (instantiate inclusion value)) (emptyN N) := by
        rw [instantiate_altN, instantiate_valueN, empty_node_natural]
      rw [shape, ← frame.liftModel_square candidate] at carried
      exact carried

theorem deadEquiv_valueInstance_iff (N : Nodes S Γ star)
    {first second : NativeState S O Γ star} (same : NativeDead.DeadEquiv first second)
    (occurrence : O) : HasValueInstance N first occurrence ↔ HasValueInstance N second occurrence := by
  obtain ⟨common, ⟨left⟩, ⟨right⟩⟩ := same
  exact (deadExtension_valueInstance_iff N left occurrence).symm.trans
    (deadExtension_valueInstance_iff N right occurrence)

/-- The existential observation uses the real shared rows of the actual hosted adapter. -/
theorem hosted_valueInstance_iff (N : Nodes S Γ star) (hosted : HostState S)
    (presented : Presented Γ star hosted) (occupied : Finset Nat) (occurrence : Nat) :
    HasValueInstance N (state κ hosted presented occupied) occurrence ↔
      occurrence ∈ hosted.present ∧
        ∃ (target : Frames.Frame S) (value : Term (signature S target.arity) Γ star),
          rowReads hosted occurrence target (observe (altN N (valueN N value) (emptyN N))) := by
  constructor
  · rintro ⟨present, target, candidate, value, model, matched⟩
    change ContextualConditionalRows.Matches (ruleLocals Γ star κ) hosted.frame.arity candidate
      (altN N (valueN N value) (emptyN N))
      (ContextualConditionalRows.ofStored (ruleLocals Γ star κ) hosted.frame.arity
        (.shared (presented.term occurrence))) at matched
    have shared := (ContextualConditionalRows.ofStored_matches_iff (ruleLocals Γ star κ)
      hosted.frame.arity candidate _ (.shared (presented.term occurrence))).mp matched
    have same := (ContextualGuardMatching.shared_matches_iff (ruleLocals Γ star κ)
      candidate _ (presented.term occurrence)).mp shared
    refine ⟨present, target, value, candidate, model, ?_⟩
    rw [presented.label_eq occurrence]
    exact congrArg observe same.symm
  · rintro ⟨present, target, value, candidate, model, same⟩
    refine ⟨present, target, candidate, value, model, ?_⟩
    change ContextualConditionalRows.Matches (ruleLocals Γ star κ) hosted.frame.arity candidate
      (altN N (valueN N value) (emptyN N))
      (ContextualConditionalRows.ofStored (ruleLocals Γ star κ) hosted.frame.arity
        (.shared (presented.term occurrence)))
    apply (ContextualConditionalRows.ofStored_matches_iff (ruleLocals Γ star κ)
      hosted.frame.arity candidate _ (.shared (presented.term occurrence))).mpr
    apply (ContextualGuardMatching.shared_matches_iff (ruleLocals Γ star κ)
      candidate _ (presented.term occurrence)).mpr
    rw [presented.label_eq occurrence] at same
    exact (observe_injective same).symm

section Represented

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}

/-- A source representation supplies the control-shape inversion that an arbitrary shared row
does not. One value-shaped reading then recovers the existing universal finished observation. -/
theorem represented_value_reading_iff_finished (N : Nodes S Γ star) {scope : Nat}
    {branch : Branch κ Γ star D.Ty} {hosted : HostState S} {occurrence : Nat}
    (represented : Represents N P scope branch hosted occurrence) :
    (∃ (target : Frames.Frame S) (value : Term (signature S target.arity) Γ star),
      rowReads hosted occurrence target (observe (altN N (valueN N value) (emptyN N)))) ↔
        StateFinished N hosted occurrence := by
  constructor
  · rintro ⟨target, value, reads⟩
    obtain ⟨candidate, solved, same⟩ := (branchReads_observe N).mp
      ((represented.reads target _).mp reads)
    obtain ⟨onFocus, onStack⟩ := alt_eq_encAlt N (instantiate candidate) same.symm
    obtain ⟨datum, focus, _⟩ := value_eq_encFocus N (instantiate candidate) onFocus
    apply (Hosting.finished_iff N (D := D) represented).mp
    exact ⟨⟨empty_eq_encStack N (instantiate candidate) onStack, datum, focus⟩,
      target.Names, target.arity, candidate, solved⟩
  · intro finished
    obtain ⟨target, reading, reads⟩ := finished.1
    obtain ⟨value, rfl⟩ := finished.2 target reading reads
    exact ⟨target, value, reads⟩

theorem represented_finished_iff_valueInstance (N : Nodes S Γ star) {scope : Nat}
    {branch : Branch κ Γ star D.Ty} {hosted : HostState S} {occurrence : Nat}
    (represented : Represents N P scope branch hosted occurrence)
    (presented : Presented Γ star hosted) (occupied : Finset Nat) :
    StateFinished N hosted occurrence ↔
      HasValueInstance N (state κ hosted presented occupied) occurrence := by
  rw [hosted_valueInstance_iff]
  constructor
  · intro finished
    refine ⟨?_, (represented_value_reading_iff_finished N (D := D) represented).mpr finished⟩
    rw [represented.present]
    exact Finset.mem_insert_self _ _
  · rintro ⟨_, reading⟩
    exact (represented_value_reading_iff_finished N (D := D) represented).mp reading

end Represented

/-- Both representations are actual source licences; neither includes the desired finished
conclusion. The full `Hosting.StateFinished` observation is preserved. -/
theorem stateFinished_deadEquiv (N : Nodes S Γ star) {D : Discipline S Γ star}
    {leftProgram rightProgram : SourceLanguage.Program κ Γ star D.Ty}
    {leftScope rightScope : Nat} {leftBranch rightBranch : Branch κ Γ star D.Ty}
    {first second : HostState S} {left : Presented Γ star first} {right : Presented Γ star second}
    {firstOccupied secondOccupied : Finset Nat}
    (same : NativeDead.DeadEquiv (state κ first left firstOccupied)
      (state κ second right secondOccupied))
    {occurrence : Nat} (firstRep : Represents N leftProgram leftScope leftBranch first occurrence)
    (secondRep : Represents N rightProgram rightScope rightBranch second occurrence) :
    StateFinished N first occurrence ↔ StateFinished N second occurrence :=
  (represented_finished_iff_valueInstance N (D := D) firstRep left firstOccupied).trans
    ((deadEquiv_valueInstance_iff N same occurrence).trans
      (represented_finished_iff_valueInstance N (D := D) secondRep right secondOccupied).symm)

theorem answers_and_finished_deadEquiv (N : Nodes S Γ star) {D : Discipline S Γ star}
    {leftProgram rightProgram : SourceLanguage.Program κ Γ star D.Ty}
    {leftScope rightScope : Nat} {leftBranch rightBranch : Branch κ Γ star D.Ty}
    {first second : HostState S} {left : Presented Γ star first} {right : Presented Γ star second}
    {firstOccupied secondOccupied : Finset Nat}
    (same : NativeDead.DeadEquiv (state κ first left firstOccupied)
      (state κ second right secondOccupied))
    {occurrence : Nat} (firstRep : Represents N leftProgram leftScope leftBranch first occurrence)
    (secondRep : Represents N rightProgram rightScope rightBranch second occurrence) :
    stateAnswer N first occurrence = stateAnswer N second occurrence ∧
      (StateFinished N first occurrence ↔ StateFinished N second occurrence) :=
  ⟨stateAnswer_deadEquiv_of_rep N same firstRep,
    stateFinished_deadEquiv N (D := D) same firstRep secondRep⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedFinishedReadings
