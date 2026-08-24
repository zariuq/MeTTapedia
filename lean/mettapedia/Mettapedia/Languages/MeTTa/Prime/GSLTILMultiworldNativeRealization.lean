import Mettapedia.GSLT.LanguageDef.GSLTILMultiworldObservation
import Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds

/-!
# GSLT-IL elaboration worlds composed with native execution worlds

Elaboration ambiguity and runtime nondeterminism are independent axes.  An
authored command may have several evidence-bearing elaboration worlds, and
each elaboration world may relate to several rho execution worlds.  Native
realization acts only on the latter axis.

The construction uses the existing loose-relation equipment.  Postcomposing
an elaboration-to-execution relation with the companion of worldwise native
realization retains the elaboration world, the original execution world, and
both relation witnesses.  It neither selects a meaning nor identifies raw rho
alternatives whose realized observations happen to coincide.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldNativeRealization

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

variable {program : Program} {profile : Profile program}
  {command : profile.Command}
  {Ground : Type} {source : CostConfig Ground}

/-- A language-specific interpretation may relate one elaboration world to
several proof-relevant execution worlds. -/
abbrev ExecutionInterpretation :=
  Loose (profile.World command) (ExecutionWorld Ground source)

/-- Native realization is relational postcomposition with the companion of
the already-established worldwise realization map. -/
abbrev NativeInterpretation
    (interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)) :
    Loose (profile.World command) (RealizedWorld Ground source) :=
  comp interpretation (companion realize)

/-- One complete interpreted execution retains its elaboration world, runtime
world, and the evidence connecting them. -/
abbrev InterpretedExecution
    (interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)) :=
  Σ elaboration : profile.World command,
    Σ execution : ExecutionWorld Ground source,
      interpretation elaboration execution

/-- One realized interpretation retains its elaboration world and the full
loose-composite witness, including the original execution world. -/
abbrev InterpretedRealization
    (interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)) :=
  Σ elaboration : profile.World command,
    Σ realized : RealizedWorld Ground source,
      NativeInterpretation interpretation elaboration realized

/-- Inject one interpretation witness into the relational composite with
native realization. -/
def realizeEvidence
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    {elaboration : profile.World command}
    {execution : ExecutionWorld Ground source}
    (evidence : interpretation elaboration execution) :
    NativeInterpretation interpretation elaboration (realize execution) :=
  ⟨execution, evidence, ⟨⟨rfl⟩⟩⟩

/-- Realize one interpreted execution without changing or selecting its
elaboration world. -/
def realizeInterpreted
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)} :
    InterpretedExecution interpretation → InterpretedRealization interpretation
  | ⟨elaboration, execution, evidence⟩ =>
      ⟨elaboration, realize execution, realizeEvidence evidence⟩

/-- Recover the elaboration world from a realized composite witness. -/
def originalElaboration
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)} :
    InterpretedRealization interpretation → profile.World command
  | ⟨elaboration, _, _⟩ => elaboration

/-- Recover the original execution world retained as the intermediate object
of loose relational composition. -/
def originalExecution
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)} :
    InterpretedRealization interpretation → ExecutionWorld Ground source
  | ⟨_, _, execution, _, _⟩ => execution

@[simp] theorem realizeInterpreted_originalElaboration
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (world : InterpretedExecution interpretation) :
    originalElaboration (realizeInterpreted world) = world.1 := by
  rcases world with ⟨elaboration, execution, evidence⟩
  rfl

@[simp] theorem realizeInterpreted_originalExecution
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (world : InterpretedExecution interpretation) :
    originalExecution (realizeInterpreted world) = world.2.1 := by
  rcases world with ⟨elaboration, execution, evidence⟩
  rfl

/-- Distinct runtime branches remain distinct realized composite witnesses,
even if a later value readout identifies their visible targets. -/
theorem realizeInterpreted_distinct_of_execution_ne
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (first second : InterpretedExecution interpretation)
    (different : first.2.1 ≠ second.2.1) :
    realizeInterpreted first ≠ realizeInterpreted second := by
  intro same
  apply different
  exact congrArg originalExecution same

/-- Mapping a finite family realizes every occurrence independently and
preserves its cardinality. -/
@[simp] theorem realizeInterpreted_length
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (worlds : List (InterpretedExecution interpretation)) :
    (worlds.map realizeInterpreted).length = worlds.length := by
  simp

/-- Mapping a finite family preserves the complete ordered elaboration-world
projection. -/
@[simp] theorem realizeInterpreted_elaborations
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (worlds : List (InterpretedExecution interpretation)) :
    (worlds.map realizeInterpreted).map originalElaboration =
      worlds.map Sigma.fst := by
  induction worlds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

/-- Postcomposition cannot manufacture a realized meaning when the original
elaboration world has no related execution world. -/
theorem no_realization_without_interpreted_execution
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (elaboration : profile.World command)
    (absent : ¬ Nonempty
      (Σ execution : ExecutionWorld Ground source,
        interpretation elaboration execution)) :
    ¬ Nonempty
      (Σ realized : RealizedWorld Ground source,
        NativeInterpretation interpretation elaboration realized) := by
  rintro ⟨⟨realized, execution, evidence, realizationEvidence⟩⟩
  exact absent ⟨⟨execution, evidence⟩⟩

/-! ## Contested rho communication under one authored meaning -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds.Examples

/-- One elaboration world may genuinely interpret as either contested rho
communication branch. -/
inductive ContestedInterpretation
  (selected : profile.World command) :
    ExecutionInterpretation (profile := profile) (command := command)
      (Ground := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples.ExampleGround)
      (source := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples.contestedSource)
  | chooseAlice : ContestedInterpretation selected selected Contested.alice
  | chooseCompetitor :
      ContestedInterpretation selected selected Contested.competitor

def aliceExecution (selected : profile.World command) :
    InterpretedExecution (ContestedInterpretation selected) :=
  ⟨selected, Contested.alice, .chooseAlice⟩

def competitorExecution (selected : profile.World command) :
    InterpretedExecution (ContestedInterpretation selected) :=
  ⟨selected, Contested.competitor, .chooseCompetitor⟩

/-- Native realization preserves both runtime alternatives beneath the same
authored meaning.  Their elaboration projection is equal, but their retained
intermediate execution worlds keep the composite witnesses distinct. -/
theorem contested_branches_remain_distinct_beneath_one_meaning
    (selected : profile.World command) :
    originalElaboration (realizeInterpreted (aliceExecution selected)) =
        originalElaboration
          (realizeInterpreted (competitorExecution selected)) ∧
      realizeInterpreted (aliceExecution selected) ≠
        realizeInterpreted (competitorExecution selected) := by
  constructor
  · rfl
  · apply realizeInterpreted_distinct_of_execution_ne
    intro equal
    have realizedTargetEqual :=
      congrArg (fun world => (realize world).target) equal
    exact Contested.realization_preserves_both_contested_worlds.2
      realizedTargetEqual

/-- An empty interpretation stays empty after native postcomposition. -/
def emptyInterpretation :
    ExecutionInterpretation (profile := profile) (command := command)
      (Ground := Ground) (source := source) :=
  fun _ _ => Empty

theorem empty_interpretation_has_no_realized_world
    (elaboration : profile.World command) :
    ¬ Nonempty
      (Σ realized : RealizedWorld Ground source,
        NativeInterpretation (emptyInterpretation
          (profile := profile) (command := command)
          (Ground := Ground) (source := source)) elaboration realized) :=
  no_realization_without_interpreted_execution elaboration
    (by rintro ⟨⟨execution, evidence⟩⟩; exact evidence.elim)

end Canary

#print axioms realizeEvidence
#print axioms realizeInterpreted_originalElaboration
#print axioms realizeInterpreted_originalExecution
#print axioms realizeInterpreted_distinct_of_execution_ne
#print axioms realizeInterpreted_length
#print axioms realizeInterpreted_elaborations
#print axioms no_realization_without_interpreted_execution
#print axioms Canary.contested_branches_remain_distinct_beneath_one_meaning
#print axioms Canary.empty_interpretation_has_no_realized_world

end Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldNativeRealization
