import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramBackend

/-!
# Generated OSLF meaning of complete repeated-service runs

The run view retains the existing scope-indexed backend terms and literal
equations. Its edges are finite paths of that backend ending at a complete
result list. This is a derived semantic view, not another execution machine.
No source evaluator is a premise of a run edge.

`IRRunView` implements this idea for Pattern-valued `IRLanguage`s. The present
backend instead retains dependent request/reply objects; no Pattern codec or
IRLanguage is asserted here. The existing generic GSLT synthesis supplies the
predicate frame and diamond/box adjunction directly on this typed run view.

Complete-list predicates may distinguish order, counts, states, intents and
full reply histories. An existential output predicate observes only that a
matching output occurs. Finite positions remain available separately. These
behavioral native types are not dependent native term-inhabitation judgments;
the latter follow only under independent source admission and qualification.

This is not an unrestricted OSLF decision procedure, an external proof-search
termination theorem, a raw HOL proof-byte checker, or a full native model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramOSLF

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation SharedJudgmentFragment SharedJudgmentServices SharedJudgmentServicePrograms
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

open SharedJudgmentServiceProgramBackend

variable {n m k : Nat}

/-- A complete run uses an actual finite backend path and only a designated
completed endpoint. Reflexive paths at an already completed state are allowed,
as in an identity-entry run protocol; initial authored starts are running. -/
def CompleteRun (assembly : Assembly) (source target : Term m) : Prop :=
  ∃ outputs, Reaches assembly source (.completed outputs) ∧ target = .completed outputs

/-- The same authored carrier and equality equations, with one complete
backend run as a semantic edge. This is not a Pattern IRLanguage. -/
def runView (assembly : Assembly) (m : Nat) : Mettapedia.GSLT.GSLT :=
  equalityGSLT (Term m) (CompleteRun assembly)

theorem runView_equiv_iff (assembly : Assembly) (left right : Term m) :
    (runView assembly m).Equiv left right ↔ left = right := Iff.rfl

theorem runView_completed_iff (assembly : Assembly) (source : Term m)
    (outputs : List (Output m)) :
    (runView assembly m).Step source (.completed outputs) ↔
      Reaches assembly source (.completed outputs) := by
  constructor
  · rintro ⟨actual, path, same⟩
    cases Term.completed.inj same
    exact path
  · intro path
    exact ⟨outputs, path, rfl⟩

theorem runView_worlds_iff (assembly : Assembly) (execution : ExecutionQualified assembly)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace)
    (outputs : List (Output m)) :
    (runView assembly m).Step (start environment code state branch) (.completed outputs) ↔
      outputs = Code.worlds assembly environment code state branch := by
  rw [runView_completed_iff, completion_worlds_iff assembly execution]

/-- The generated right adjoint is predecessor-universal, not a claim that
all future runs satisfy a predicate. -/
theorem runView_galois (assembly : Assembly) (m : Nat) :
    GaloisConnection (semanticDiamond (runView assembly m)) (semanticBox (runView assembly m)) :=
  semanticGalois (runView assembly m)

def completedObservation (observation : List (Output m) → Prop) : Term m → Prop
  | .completed outputs => observation outputs
  | .running _ _ => False

/-- An actual native type from generic GSLT/OSLF synthesis. The atom observes
the complete list, and the generated diamond observes a complete backend run. -/
def completeNativeType (assembly : Assembly) (observation : List (Output m) → Prop) :
    GSLTNativeType (runView assembly m) where
  sort := ()
  pred := semanticDiamond (runView assembly m)
    (saturatePredicate (runView assembly m) (completedObservation observation))

theorem completeNativeType_iff (assembly : Assembly)
    (observation : List (Output m) → Prop) (source : Term m) :
    (gsltOSLF (runView assembly m)).satisfies (S := ()) source
      (completeNativeType assembly observation).pred ↔
      ∃ outputs, Reaches assembly source (.completed outputs) ∧ observation outputs := by
  have base : (saturatePredicate (runView assembly m) (completedObservation observation)).1 =
      completedObservation observation := by
    funext term
    exact propext (saturatePredicate_apply_iff_of_equiv_iff_eq
      (runView assembly m) (runView_equiv_iff assembly) _ term)
  change gsltDiamond (runView assembly m)
    (saturatePredicate (runView assembly m) (completedObservation observation)).1 source ↔ _
  rw [base]
  refine (gsltDiamond_spec (runView assembly m) (completedObservation observation) source).trans ?_
  constructor
  · rintro ⟨target, ⟨outputs, path, rfl⟩, observed⟩
    exact ⟨outputs, path, observed⟩
  · rintro ⟨outputs, path, observed⟩
    exact ⟨.completed outputs, ⟨outputs, path, rfl⟩, observed⟩

/-- This law needs no semantic realization assumption: it observes the
actual supplied handler and services used by the independently authored backend. -/
theorem completeNativeType_iff_run (assembly : Assembly)
    (observation : List (Output m) → Prop)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView assembly m)).satisfies (S := ())
      (start environment code state branch) (completeNativeType assembly observation).pred ↔
      observation (Code.run assembly environment code state branch) := by
  rw [completeNativeType_iff]
  constructor
  · rintro ⟨outputs, path, observed⟩
    rw [completion_sound assembly environment code state branch path] at observed
    exact observed
  · intro observed
    exact ⟨_, (completion_run_iff assembly environment code state branch _).mpr rfl, observed⟩

/-- Exact meaning for arbitrary complete-list observations of independently
recursive source worlds, under the explicit native execution qualification. -/
theorem completeNativeType_iff_worlds (assembly : Assembly) (execution : ExecutionQualified assembly)
    (observation : List (Output m) → Prop)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView assembly m)).satisfies (S := ())
      (start environment code state branch) (completeNativeType assembly observation).pred ↔
      observation (Code.worlds assembly environment code state branch) := by
  rw [completeNativeType_iff_run, Code.interpret_worlds assembly execution]

theorem exactCompletionNativeType_iff_worlds (assembly : Assembly) (execution : ExecutionQualified assembly)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace)
    (outputs : List (Output m)) :
    (gsltOSLF (runView assembly m)).satisfies (S := ())
      (start environment code state branch)
      (exactTargetNativeType (runView assembly m) (.completed outputs)).pred ↔
      outputs = Code.worlds assembly environment code state branch := by
  exact (satisfies_exactTargetNativeType_iff_step (runView assembly m)
    (start environment code state branch) (.completed outputs)).trans
      (runView_worlds_iff assembly execution environment code state branch outputs)

/-- Position-aware observation retains a finite occurrence index. Existential
quantification over positions is still not a count of matching occurrences. -/
def occurrenceNativeType (assembly : Assembly) (observation : Nat → Output m → Prop) :
    GSLTNativeType (runView assembly m) :=
  completeNativeType assembly fun outputs =>
    ∃ occurrence : Fin outputs.length, observation occurrence.val (outputs.get occurrence)

theorem occurrenceNativeType_iff_worlds (assembly : Assembly) (execution : ExecutionQualified assembly)
    (observation : Nat → Output m → Prop)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView assembly m)).satisfies (S := ())
      (start environment code state branch) (occurrenceNativeType assembly observation).pred ↔
      ∃ occurrence : Fin (Code.worlds assembly environment code state branch).length,
        observation occurrence.val ((Code.worlds assembly environment code state branch).get occurrence) :=
  completeNativeType_iff_worlds assembly execution _ environment code state branch

/-- Existential output observation deliberately forgets its position. Each
observed output still includes its full outcome, world and reply history. -/
def outputNativeType (assembly : Assembly) (observation : Output m → Prop) :
    GSLTNativeType (runView assembly m) :=
  completeNativeType assembly fun outputs => ∃ output ∈ outputs, observation output

theorem outputNativeType_iff_worlds (assembly : Assembly) (execution : ExecutionQualified assembly)
    (observation : Output m → Prop)
    (environment : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView assembly m)).satisfies (S := ())
      (start environment code state branch) (outputNativeType assembly observation).pred ↔
      ∃ output ∈ Code.worlds assembly environment code state branch, observation output :=
  completeNativeType_iff_worlds assembly execution _ environment code state branch

/-- The run-view meaning transports the backend's actual substitution law;
both sides use the handler at the final target scope. -/
theorem completeNativeType_substitute_iff (assembly : Assembly)
    (observation : List (Output k) → Prop) (later : Sub Tower.Head m k)
    (earlier : Sub Tower.Head n m) (code : Code n) (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView assembly k)).satisfies (S := ())
      (start later (code.substitute earlier) state branch)
      (completeNativeType assembly observation).pred ↔
    (gsltOSLF (runView assembly k)).satisfies (S := ())
      (start (subComp later earlier) code state branch)
      (completeNativeType assembly observation).pred := by
  simp only [completeNativeType_iff, completion_substitute_iff]

/-- A behavioral observation of a value yields native term admission only
with the independent source judgment, formed environment and service/execution
qualification. Stopped responses are not admitted native values. -/
theorem observed_value_admitted {assembly : Assembly} (qualified : specification.Satisfies assembly)
    {context : Tower.Ctx n} {targetContext : Tower.Ctx m} {code : Code n} {type : Tower.Tm n}
    (admitted : Admission assembly context code type) {environment : Sub Tower.Head n m}
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    (typed : FormationSensitive.CtxMor assembly.rules context targetContext environment)
    (state : Bool) (branch : BranchTrace) (value : Tower.Tm m)
    (observed : (gsltOSLF (runView assembly m)).satisfies (S := ())
      (start environment code state branch)
      (outputNativeType assembly (fun output => output.world.answer = .value value)).pred) :
    FormationSensitive.Judgment assembly.rules targetContext value (subst environment type) := by
  obtain ⟨outputs, completed, output, member, isValue⟩ :=
    (completeNativeType_iff assembly _ _).mp observed
  exact completion_value_admitted qualified admitted target typed completed member isValue

namespace Controls

open SharedJudgmentServicePrograms.Examples SharedJudgmentServicePrograms.AdmissionExamples

theorem nested_complete_meaning (state : Bool) (branch : BranchTrace)
    (observation : List (Output 2) → Prop) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids matchingThenHOLIdentity state branch) (completeNativeType common observation).pred ↔
      observation [SharedJudgmentServiceProgramBackend.Controls.nestedOutput state branch] := by
  rw [completeNativeType_iff_run, nested_worlds]
  rfl

theorem nested_exact_native_type (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids matchingThenHOLIdentity state branch)
      (exactTargetNativeType (runView common 2)
        (.completed [SharedJudgmentServiceProgramBackend.Controls.nestedOutput state branch])).pred := by
  apply (satisfies_exactTargetNativeType_iff_step (runView common 2)
    (start ids matchingThenHOLIdentity state branch) _).mpr
  exact (runView_completed_iff common _ _).mpr
    ((SharedJudgmentServiceProgramBackend.Controls.nested_completion_iff state branch _).mpr rfl)

theorem nested_occurrence_native_type (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids matchingThenHOLIdentity state branch)
      (occurrenceNativeType common (fun position output =>
        position = 0 ∧ output = SharedJudgmentServiceProgramBackend.Controls.nestedOutput state branch)).pred := by
  apply (nested_complete_meaning state branch _).mpr
  exact ⟨⟨0, by change 0 < 1; decide⟩, rfl, rfl⟩

/-- A stopped result remains visible to the generated run-view type with
its actual changed request, declined reply and preceding matching history. -/
theorem stopped_exact_native_type (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids matchingThenChangedHOL state branch)
      (exactTargetNativeType (runView common 2)
        (.completed [SharedJudgmentServiceProgramBackend.Controls.stoppedOutput state branch])).pred := by
  apply (satisfies_exactTargetNativeType_iff_step (runView common 2)
    (start ids matchingThenChangedHOL state branch) _).mpr
  exact (runView_completed_iff common _ _).mpr
    ((SharedJudgmentServiceProgramBackend.Controls.stopped_completion_iff state branch _).mpr rfl)

theorem stopped_value_unobservable (state : Bool) (branch : BranchTrace) :
    ¬ (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids matchingThenChangedHOL state branch)
      (outputNativeType common (fun output => ∃ value, output.world.answer = .value value)).pred := by
  intro observed
  obtain ⟨outputs, completed, output, member, value, isValue⟩ :=
    (completeNativeType_iff common _ _).mp observed
  exact SharedJudgmentServiceProgramBackend.Controls.stopped_completion_no_value state branch completed member value isValue

/-- Exact generated types reject changed complete observations, including
the mutation of only the chronological reply history. -/
theorem reversed_history_native_type_rejected (state : Bool) (branch : BranchTrace) :
    ¬ (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids matchingThenHOLIdentity state branch)
      (exactTargetNativeType (runView common 2)
        (.completed [{ SharedJudgmentServiceProgramBackend.Controls.nestedOutput state branch with
          replies := (SharedJudgmentServiceProgramBackend.Controls.nestedOutput state branch).replies.reverse }])).pred := by
  intro observed
  have step := (satisfies_exactTargetNativeType_iff_step (runView common 2)
    (start ids matchingThenHOLIdentity state branch) _).mp observed
  exact SharedJudgmentServiceProgramBackend.Controls.reversed_nested_history_rejected state branch
    ((runView_completed_iff common _ _).mp step)

/-- Both branches perform the actual matching and HOL calls before returning
the same dependent native value. Their branch occurrences remain distinct. -/
def forkedNested : Code 2 := .choose matchingThenHOLIdentity matchingThenHOLIdentity

theorem forked_nested_run (state : Bool) (branch : BranchTrace) :
    Code.run common ids forkedNested state branch =
      [SharedJudgmentServiceProgramBackend.Controls.nestedOutput state (false :: branch),
       SharedJudgmentServiceProgramBackend.Controls.nestedOutput state (true :: branch)] := by
  change runWorldsAt (invoke common)
    (.choose (Code.interpret common ids matchingThenHOLIdentity)
      (Code.interpret common ids matchingThenHOLIdentity)) state branch = _
  rw [runWorldsAt_choose]
  change Code.run common ids matchingThenHOLIdentity state (false :: branch) ++
    Code.run common ids matchingThenHOLIdentity state (true :: branch) = _
  rw [nested_worlds, nested_worlds]
  rfl

theorem forked_nested_complete_meaning (state : Bool) (branch : BranchTrace)
    (observation : List (Output 2) → Prop) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
      (start ids forkedNested state branch) (completeNativeType common observation).pred ↔
      observation
        [SharedJudgmentServiceProgramBackend.Controls.nestedOutput state (false :: branch),
         SharedJudgmentServiceProgramBackend.Controls.nestedOutput state (true :: branch)] := by
  rw [completeNativeType_iff_run, forked_nested_run]

/-- Count positions returning this actual nested value, without identifying
distinct worlds or quotienting their request/reply histories. -/
def nestedValueCount (outputs : List (Output 2)) : Nat :=
  outputs.countP fun output =>
    match output.world.answer with
    | .value value => decide (value = nestedValue)
    | .stopped _ => false

/-- Existential observation cannot determine occurrence count: these real
one-branch and two-branch service programs both expose the same value, while
complete-list predicates distinguish one occurrence from two. -/
theorem existential_value_observation_does_not_count (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
        (start ids matchingThenHOLIdentity state branch)
        (outputNativeType common (fun output => output.world.answer = .value nestedValue)).pred ∧
      (gsltOSLF (runView common 2)).satisfies (S := ())
        (start ids forkedNested state branch)
        (outputNativeType common (fun output => output.world.answer = .value nestedValue)).pred ∧
      (gsltOSLF (runView common 2)).satisfies (S := ())
        (start ids matchingThenHOLIdentity state branch)
        (completeNativeType common (fun outputs => nestedValueCount outputs = 1)).pred ∧
      ¬ (gsltOSLF (runView common 2)).satisfies (S := ())
        (start ids forkedNested state branch)
        (completeNativeType common (fun outputs => nestedValueCount outputs = 1)).pred ∧
      (gsltOSLF (runView common 2)).satisfies (S := ())
        (start ids forkedNested state branch)
        (completeNativeType common (fun outputs => nestedValueCount outputs = 2)).pred := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (nested_complete_meaning state branch _).mpr
    exact ⟨_, List.mem_cons_self, rfl⟩
  · apply (forked_nested_complete_meaning state branch _).mpr
    exact ⟨_, List.mem_cons_self, rfl⟩
  · apply (nested_complete_meaning state branch _).mpr
    simp [nestedValueCount, SharedJudgmentServiceProgramBackend.Controls.nestedOutput]
  · intro observed
    have count := (forked_nested_complete_meaning state branch _).mp observed
    simp [nestedValueCount, SharedJudgmentServiceProgramBackend.Controls.nestedOutput] at count
  · apply (forked_nested_complete_meaning state branch _).mpr
    simp [nestedValueCount, SharedJudgmentServiceProgramBackend.Controls.nestedOutput]

/-- Unlike the position-forgetting existential predicate, a query for the
second position distinguishes the actual one- and two-world completions. -/
theorem second_occurrence_distinguishes (state : Bool) (branch : BranchTrace) :
    (gsltOSLF (runView common 2)).satisfies (S := ())
        (start ids forkedNested state branch)
        (occurrenceNativeType common (fun position output =>
          position = 1 ∧ output.world.answer = .value nestedValue)).pred ∧
      ¬ (gsltOSLF (runView common 2)).satisfies (S := ())
        (start ids matchingThenHOLIdentity state branch)
        (occurrenceNativeType common (fun position output =>
          position = 1 ∧ output.world.answer = .value nestedValue)).pred := by
  constructor
  · apply (forked_nested_complete_meaning state branch _).mpr
    exact ⟨⟨1, by change 1 < 2; decide⟩, rfl, rfl⟩
  · intro observed
    obtain ⟨occurrence, position, _⟩ := (nested_complete_meaning state branch _).mp observed
    have bound := occurrence.isLt
    change occurrence.val < 1 at bound
    omega

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramOSLF
