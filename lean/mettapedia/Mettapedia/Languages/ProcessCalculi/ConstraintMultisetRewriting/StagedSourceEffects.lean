import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalSchedule

/-!
# Computed-source effects retain their cuts until one public commit

A finite computed-source block consists of prepared ordinary firings, with
their complete observations. The existing conditional compiler constructs
the resource conditions, equations, static shapes and original check cuts.
Complete observations are transported alongside them as inspectable prefix
equations and store effects. No call to a whole evaluator is a premise.

The source contract is atomic: a successful block publishes its final
configuration, and a nonadmitted block leaves the caller configuration intact.
The compiler is compared in both directions with that contract. This is not
an assertion that an eager host evaluator already stages its effects, nor a
replacement of arbitrary public sequential histories by one event.

The negative branch below observes the unchanged configuration only. It does
not classify the reason as completed refusal, unresolved information or an
unfinished search. An executable driver must retain those distinctions;
failure to obtain a ready certificate is not a proof of nonadmission.

The block is over a common prepared declaration interface. Source freshening,
family-changing episodes and returned-value bindings keep their own source
compilation obligations. Pure `Source.letBind` remains the existing read-only
computed-value constructor; this module supplies the separate staged path.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

structure Instruction (T : Type uT) (S : Type uS) (O : Type uO) where
  rule : RuleInstance T
  selection : Selection O
  observations : List (PredicateQueryAdmission.Query T S O)

def Instruction.raw (instruction : Instruction T S O) : ConditionalSchedule.Firing T O :=
  (instruction.rule, instruction.selection)

structure Observation (T : Type uT) (S : Type uS) (O : Type uO) where
  equations : EquationStore T
  effect : Commit O T
  query : PredicateQueryAdmission.Query T S O

def Observation.Holds (observation : Observation T S O) (action : SubstitutionAction T S)
    (label : O → T) (before : Configuration T O) : Prop :=
  observation.query.Ask action (before.equations ++ observation.equations) label
    (fire before.present observation.effect)

def Observation.transport (earlier : ConditionalComposite T O) (observation : Observation T S O) :
    Observation T S O :=
  ⟨earlier.equations ++ observation.equations,
    ConditionalComposite.transportEffect earlier.effect observation.effect, observation.query⟩

theorem Observation.transport_holds (earlier : ConditionalComposite T O)
    (observation : Observation T S O) (action : SubstitutionAction T S)
    (label : O → T) (before : Configuration T O) :
    (observation.transport earlier).Holds action label before ↔
      observation.Holds action label (earlier.result before) := by
  simp only [Observation.transport, Observation.Holds, ConditionalComposite.result,
    List.append_assoc, ConditionalComposite.fire_transportEffect]

def compileObservations (label : O → T) : List (Instruction T S O) → List (Observation T S O)
  | [] => []
  | instruction :: rest =>
      instruction.observations.map (fun query =>
        ⟨ConditionalComposite.addedEquations label instruction.rule instruction.selection,
          ConditionalComposite.emptyEffect, query⟩) ++
      (compileObservations label rest).map
        (Observation.transport (ConditionalSchedule.single label instruction.raw))

structure Plan (T : Type uT) (S : Type uS) (O : Type uO) where
  raw : ConditionalComposite T O
  observations : List (Observation T S O)

def compile (label : O → T) (code : List (Instruction T S O)) : Plan T S O :=
  ⟨ConditionalSchedule.compile label (code.map Instruction.raw), compileObservations label code⟩

def Plan.Holds (plan : Plan T S O) (action : SubstitutionAction T S)
    (label : O → T) (before : Configuration T O) : Prop :=
  plan.raw.Holds action label before ∧ ∀ observation ∈ plan.observations, observation.Holds action label before

def Executable (action : SubstitutionAction T S) (label : O → T) :
    Configuration T O → List (Instruction T S O) → Prop
  | before, [] => action.Consistent before.equations
  | before, instruction :: rest =>
      PredicateQueryAdmission.Valid action label instruction.rule instruction.observations before instruction.selection ∧
        Executable action label (instruction.selection.result label instruction.rule before) rest

theorem Executable.raw {action : SubstitutionAction T S} {label : O → T} :
    ∀ {before : Configuration T O} {code : List (Instruction T S O)}, Executable action label before code →
      ConditionalSchedule.Executable action label before (code.map Instruction.raw)
  | _, [], ready => ready
  | _, _ :: _, ready => ⟨ready.1.firing, ready.2.raw⟩

theorem observation_cons_iff (action : SubstitutionAction T S) (label : O → T)
    (instruction : Instruction T S O) (rest : List (Instruction T S O)) (before : Configuration T O) :
    (∀ observation ∈ compileObservations label (instruction :: rest), observation.Holds action label before) ↔
      (∀ query ∈ instruction.observations, query.Ask action
        (instruction.selection.problem label instruction.rule before) label before.present) ∧
      ∀ observation ∈ compileObservations label rest, observation.Holds action label
        (instruction.selection.result label instruction.rule before) := by
  rw [compileObservations, List.forall_mem_append]
  apply and_congr
  · simp only [List.forall_mem_map, Observation.Holds, ConditionalComposite.fire_emptyEffect,
      ConditionalComposite.problem_eq]
  · constructor
    · intro holds observation member
      have ready := holds _ (List.mem_map.mpr ⟨observation, member, rfl⟩)
      have law := Observation.transport_holds (ConditionalSchedule.single label instruction.raw)
        observation action label before
      rw [ConditionalSchedule.single_result] at law
      exact law.mp ready
    · intro holds observation member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      have law := Observation.transport_holds (ConditionalSchedule.single label instruction.raw)
        original action label before
      rw [ConditionalSchedule.single_result] at law
      exact law.mpr (holds original present)

/-- The compiler retains the exact readiness of every private source step,
including a census made before later equations or effects exist. -/
theorem compile_exact (action : SubstitutionAction T S) (label : O → T) :
    ∀ (code : List (Instruction T S O)) (before : Configuration T O),
      (compile label code).Holds action label before ↔ Executable action label before code
  | [], before => by
      constructor
      · intro ready
        exact (ConditionalSchedule.empty_holds_iff action label before).mp ready.1
      · intro consistent
        refine ⟨(ConditionalSchedule.empty_holds_iff action label before).mpr consistent, ?_⟩
        intro observation member
        cases member
  | instruction :: rest, before => by
      constructor
      · rintro ⟨raw, censuses⟩
        have source := (ConditionalSchedule.compile_holds_iff action label before _).mp raw
        obtain ⟨current, later⟩ := (observation_cons_iff action label instruction rest before).mp censuses
        refine ⟨⟨source.1, current⟩, ?_⟩
        apply (compile_exact action label rest _).mp
        exact ⟨(ConditionalSchedule.compile_holds_iff action label _ _).mpr source.2, later⟩
      · rintro ⟨current, later⟩
        have compiled := (compile_exact action label rest _).mpr later
        refine ⟨(ConditionalSchedule.compile_holds_iff action label before _).mpr ⟨current.firing, later.raw⟩, ?_⟩
        exact (observation_cons_iff action label instruction rest before).mpr ⟨current.observations, compiled.2⟩

def SourceResult (action : SubstitutionAction T S) (label : O → T) (code : List (Instruction T S O))
    (before after : Configuration T O) : Prop :=
  (Executable action label before code ∧ after = ConditionalSchedule.follow label before (code.map Instruction.raw)) ∨
    (¬ Executable action label before code ∧ after = before)

def CompiledResult (action : SubstitutionAction T S) (label : O → T) (plan : Plan T S O)
    (before after : Configuration T O) : Prop :=
  (plan.Holds action label before ∧ after = plan.raw.result before) ∨
    (¬ plan.Holds action label before ∧ after = before)

/-- Two-way source comparison for the explicitly staged boundary. The final
resource effect is published only after the complete source admission holds. -/
theorem compiled_result_iff_source (action : SubstitutionAction T S) (label : O → T)
    (code : List (Instruction T S O)) (before after : Configuration T O) :
    CompiledResult action label (compile label code) before after ↔ SourceResult action label code before after := by
  have same := compile_exact action label code before
  constructor
  · rintro (⟨ready, result⟩ | ⟨refused, result⟩)
    · have runs := same.mp ready
      exact .inl ⟨runs, result.trans (ConditionalSchedule.compile_result action label before _ runs.raw)⟩
    · exact .inr ⟨fun ready => refused (same.mpr ready), result⟩
  · rintro (⟨ready, result⟩ | ⟨refused, result⟩)
    · exact .inl ⟨same.mpr ready,
        result.trans (ConditionalSchedule.compile_result action label before _ ready.raw).symm⟩
    · exact .inr ⟨fun ready => refused (same.mp ready), result⟩

theorem refused_has_no_residue {action : SubstitutionAction T S} {label : O → T}
    {code : List (Instruction T S O)} {before after : Configuration T O}
    (refused : ¬ Executable action label before code)
    (result : CompiledResult action label (compile label code) before after) : after = before := by
  rcases (compiled_result_iff_source action label code before after).mp result with ⟨ready, _⟩ | ⟨_, same⟩
  · exact False.elim (refused ready)
  · exact same

/-- Under the retained source admission, the compiled net effect has one
actual occurrence firing with the same final models and resources. The
prefix conditions remain part of the compiled entry: enabling its bare net
update does not justify discarding them. -/
theorem realize_net_under_retained_admission (action : SubstitutionAction T S) (label : O → T)
    (code : List (Instruction T S O)) (before : Configuration T O)
    (ready : (compile label code).Holds action label before) :
    let plan := (compile label code).raw
    let selected := CensusSourceCompilation.selection plan.effect
    let rule := CensusSourceCompilation.rule label plan.effect plan.equations
    PredicateQueryAdmission.Valid action label rule (plan.effect.queries.map PredicateQueryAdmission.Query.fixed) before selected ∧
      action.Equivalent (selected.result label rule before).equations
        (ConditionalSchedule.follow label before (code.map Instruction.raw)).equations ∧
      (selected.result label rule before).present =
        (ConditionalSchedule.follow label before (code.map Instruction.raw)).present := by
  have enabled := ConditionalSchedule.compile_resourceSound label (code.map Instruction.raw)
    before.present ready.1.2.1
  have same := ConditionalSchedule.compile_result action label before _
    ((compile_exact action label code before).mp ready).raw
  refine ⟨CensusSourceCompilation.realize_commit action label (compile label code).raw.effect
    (compile label code).raw.equations before enabled ready.1.2.2.1, ?_, ?_⟩
  · intro candidate
    rw [← same]
    exact CensusSourceCompilation.models_problem_iff action candidate label (compile label code).raw.effect
      (compile label code).raw.equations before
  · rw [← same]
    exact CensusSourceCompilation.physical_result label (compile label code).raw.effect
      (compile label code).raw.equations before

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects
