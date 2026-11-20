import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Operational

/-!
# The reduction graph after finite administration

A reaction is finitely many actual administrative firings followed by exactly
one communication. It is not an arbitrary nonempty run: a run made only of
administration must not count as a source reduction. The source and target
equation quotients have isomorphic reduction graphs with this convention.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-- One real communication, preceded by finite administrative work. -/
def Reaction (before after : Point) : Prop :=
  ∃ middle : RawState, Relation.ReflTransGen ByInstantiation.Administers before.val middle ∧
    ByInstantiation.Communicates middle after.val

theorem administration_represents {first last : RawState} {process : RhoProcess}
    (represented : ByInstantiation.Represents first process)
    (run : Relation.ReflTransGen ByInstantiation.Administers first last) :
    ByInstantiation.Represents last process := by
  induction run with
  | refl => exact represented
  | tail previous step ih =>
      exact ByInstantiation.reflective_calculus_by_instantiation.2.2.1 ih step

theorem reaction_reads {before after : Point} (reaction : Reaction before after) :
    rhoLanguageDefGSLT.Step (readback before) (readback after) := by
  obtain ⟨middle, administration, communication⟩ := reaction
  have represented := administration_represents (readback_represents before) administration
  obtain ⟨process, step, represented⟩ :=
    ByInstantiation.reflective_calculus_by_instantiation.2.2.2.1 represented communication
  exact (source_step_congr (rhoProcessEquations.iseqv.refl _)
    (rhoProcessEquations.iseqv.symm (readback_equations after represented))).mp step

theorem reaction_runs {before after : Point} (reaction : Reaction before after) : Runs before after := by
  obtain ⟨middle, administration, communication⟩ := reaction
  obtain ⟨last, same, run⟩ := raw_runs_lift before
    ((Encodings.runs_of_administrative administration).tail (Encodings.communicates_moves communication))
  have equal : last = after := Subtype.ext same
  exact equal ▸ run

/-- Completeness from every clean state, with an actual communication witness. -/
theorem reaction_lifts (before : Point) {process : RhoProcess}
    (step : rhoLanguageDefGSLT.Step (readback before) process) :
    ∃ after : Point, Reaction before after ∧ rhoProcessEquations.r (readback after) process := by
  obtain ⟨middle, last, value, administration, communication, represented⟩ :=
    ByInstantiation.communication_complete (certificate before).represents step
  let after : Point := ⟨last, clean_of_represents ⟨value, represented⟩⟩
  exact ⟨after, ⟨middle, administration, communication⟩,
    readback_equations after ⟨value, represented⟩⟩

theorem source_step_iff_reaction (before : Point) (process : RhoProcess) :
    rhoLanguageDefGSLT.Step (readback before) process ↔
      ∃ after : Point, Reaction before after ∧ rhoProcessEquations.r (readback after) process := by
  constructor
  · exact reaction_lifts before
  · rintro ⟨after, reaction, same⟩
    exact (source_step_congr (rhoProcessEquations.iseqv.refl _) same).mp (reaction_reads reaction)

/-- The endpoint is specified up to the declared equational meaning. -/
def ReactionBetween (before after : Point) : Prop := ∃ last : Point, Reaction before last ∧ Same last after

theorem reaction_between_iff (before after : Point) :
    ReactionBetween before after ↔ rhoLanguageDefGSLT.Step (readback before) (readback after) :=
  (source_step_iff_reaction before (readback after)).symm

theorem reaction_between_respects {first first' last last' : Point}
    (before : Same first first') (after : Same last last') :
    ReactionBetween first last ↔ ReactionBetween first' last' := by
  rw [reaction_between_iff, reaction_between_iff]
  exact source_step_congr before after

def sourceReduction (before after : SourceQuotient) : Prop :=
  Quotient.liftOn₂ before after rhoLanguageDefGSLT.Step
    (fun _ _ _ _ first last => propext (source_step_congr first last))

def targetReduction (before after : TargetQuotient) : Prop :=
  Quotient.liftOn₂ before after ReactionBetween
    (fun _ _ _ _ first last => propext (reaction_between_respects first last))

/-- The onto equivalence also preserves and reflects reduction. Silent
administration is omitted, while each retained edge contains a communication. -/
theorem quotient_reduction_iff (before after : SourceQuotient) :
    targetReduction (quotientEquiv before) (quotientEquiv after) ↔ sourceReduction before after := by
  refine Quotient.inductionOn₂ before after ?_
  intro first last
  change ReactionBetween (compile first) (compile last) ↔ rhoLanguageDefGSLT.Step first last
  exact (reaction_between_iff _ _).trans (source_step_congr (source_roundtrip first) (source_roundtrip last))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
