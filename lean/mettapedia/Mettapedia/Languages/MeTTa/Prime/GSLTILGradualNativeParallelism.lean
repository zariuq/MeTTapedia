import Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldNativeRealization
import Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee

/-!
# Gradual native parallelism beneath relational GSLT-IL meanings

GSLT-IL elaboration worlds and rho execution worlds are independent axes.
A language-specific interpretation relates the former to the latter.  Native
parallel evidence may refine an execution world, while deoptimization must
leave the authored elaboration world untouched.

The required language capability is explicit: an interpretation is
deoptimization-closed when every interpreted native world also admits its
exact raw rho projection.  Any relational semantics stated over raw rho
branches lifts canonically to such an interpretation.  Thus gradual fallback
is derived from relational meaning rather than installed as a global choice
of elaboration or communication branch.

Two controls separate the axes.  Distinct authored worlds remain distinct
even when they share one runtime branch.  Conversely, the contested rho race
retains two runtime branches beneath one authored world.  Native realization
and deoptimization select neither axis.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILGradualNativeParallelism

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldNativeRealization
open Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

variable {program : Program} {profile : Profile program}
  {command : profile.Command}
  {Ground : Type} {source : CostConfig Ground}

/-! ## Raw interpretations and their canonical gradual lifting -/

/-- A language interpretation stated only over proof-relevant raw rho
branches. -/
abbrev RawExecutionInterpretation :=
  Loose (profile.World command) (RawBranchWorld source)

/-- Lift raw relational meaning across native annotations by interpreting a
world through its exact raw projection.  No authored or runtime world is
selected. -/
def liftRawInterpretation
    (raw : RawExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)) :
    ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) :=
  fun elaboration execution => raw elaboration (rawProjection execution)

/-- The semantic condition required for gradual fallback: every interpreted
native execution has an interpreted raw projection at the same elaboration
world. -/
structure DeoptimizationClosed
    (interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)) : Type where
  preserve : ∀ {elaboration execution}, interpretation elaboration execution →
    interpretation elaboration (deopt execution)

/-- Every semantics factored through raw rho branches is automatically
deoptimization-closed. -/
def liftRawInterpretation_deoptimizationClosed
    (raw : RawExecutionInterpretation
      (profile := profile) (command := command)
    (Ground := Ground) (source := source)) :
    DeoptimizationClosed (liftRawInterpretation raw) := by
  constructor
  intro elaboration execution evidence
  change raw elaboration (rawProjection execution) at evidence
  change raw elaboration (rawProjection (deopt execution))
  rw [rawProjection_deopt]
  exact evidence

/-! ## Interpreted gradual precision -/

/-- Deoptimize one interpreted world, using the language's closure evidence
to retain its relational meaning. -/
def deoptInterpreted
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation) :
    InterpretedExecution interpretation → InterpretedExecution interpretation
  | ⟨elaboration, execution, evidence⟩ =>
      ⟨elaboration, deopt execution, closed.preserve evidence⟩

/-- Precision between interpreted executions preserves the elaboration world
and carries the proof-relevant execution-world precision step. -/
structure InterpretedRefines
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (coarse refined : InterpretedExecution interpretation) : Type where
  elaboration_eq : coarse.1 = refined.1
  execution : WorldRefines coarse.2.1 refined.2.1

def deoptInterpreted_refines
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (world : InterpretedExecution interpretation) :
    InterpretedRefines (deoptInterpreted closed world) world := by
  rcases world with ⟨elaboration, execution, evidence⟩
  exact ⟨rfl, deopt_refines execution⟩

@[simp] theorem deoptInterpreted_elaboration
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (world : InterpretedExecution interpretation) :
    (deoptInterpreted closed world).1 = world.1 := by
  rcases world with ⟨elaboration, execution, evidence⟩
  rfl

def interpretedTarget
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (world : InterpretedExecution interpretation) : CostConfig Ground :=
  world.2.1.target

@[simp] theorem deoptInterpreted_target
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (world : InterpretedExecution interpretation) :
    interpretedTarget (deoptInterpreted closed world) =
      interpretedTarget world := by
  rcases world with ⟨elaboration, execution, evidence⟩
  exact deopt_target execution

/-- Distinct authored meanings or derivation histories cannot be collapsed by
execution deoptimization. -/
theorem distinct_elaborations_survive_deoptimization
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (first second : InterpretedExecution interpretation)
    (different : first.1 ≠ second.1) :
    deoptInterpreted closed first ≠ deoptInterpreted closed second := by
  intro same
  apply different
  have elaborations := congrArg
    (fun world : InterpretedExecution interpretation => world.1) same
  simpa only [deoptInterpreted_elaboration] using elaborations

/-- Distinct runtime results likewise survive deoptimization. -/
theorem distinct_targets_survive_deoptimization
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (first second : InterpretedExecution interpretation)
    (different : interpretedTarget first ≠ interpretedTarget second) :
    deoptInterpreted closed first ≠ deoptInterpreted closed second := by
  intro same
  apply different
  have deoptimizedTargets := congrArg interpretedTarget same
  simpa only [deoptInterpreted_target] using deoptimizedTargets

/-! ## Finite multiworld collections -/

def deoptInterpretedWorlds
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (worlds : List (InterpretedExecution interpretation)) :
    List (InterpretedExecution interpretation) :=
  worlds.map (deoptInterpreted closed)

@[simp] theorem deoptInterpretedWorlds_length
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (worlds : List (InterpretedExecution interpretation)) :
    (deoptInterpretedWorlds closed worlds).length = worlds.length := by
  simp [deoptInterpretedWorlds]

@[simp] theorem deoptInterpretedWorlds_elaborations
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (worlds : List (InterpretedExecution interpretation)) :
    (deoptInterpretedWorlds closed worlds).map Sigma.fst =
      worlds.map Sigma.fst := by
  induction worlds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [deoptInterpretedWorlds]

theorem deoptInterpretedWorlds_targets
    {interpretation : ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source)}
    (closed : DeoptimizationClosed interpretation)
    (worlds : List (InterpretedExecution interpretation)) :
    (deoptInterpretedWorlds closed worlds).map interpretedTarget =
      worlds.map interpretedTarget := by
  induction worlds with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [deoptInterpretedWorlds]

/-! ## Authored ambiguity can share one execution without collapsing -/

/-- A raw relation assigning one exact branch to every authored world.  This
is a canary for independence of elaboration multiplicity from runtime
multiplicity, not a proposed universal interpretation policy. -/
def constantRawInterpretation (world : RawBranchWorld source) :
    RawExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) :=
  fun _ candidate => ULift (PLift (candidate = world))

def constantInterpretation (world : RawBranchWorld source) :
    ExecutionInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) :=
  liftRawInterpretation
    (profile := profile) (command := command)
    (Ground := Ground) (source := source)
    (constantRawInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) world)

def constantInterpretedExecution (world : RawBranchWorld source)
    (elaboration : profile.World command) :
    InterpretedExecution
      (constantInterpretation
        (profile := profile) (command := command)
        (Ground := Ground) (source := source) world) :=
  ⟨elaboration, .raw world, ⟨⟨rfl⟩⟩⟩

/-- Two distinct authored worlds may share exactly one runtime branch.  The
canonical gradual semantics retains their distinction before and after
deoptimization. -/
theorem authored_ambiguity_independent_of_execution
    (world : RawBranchWorld source)
    (first second : profile.World command)
    (different : first ≠ second) :
    let interpretation := constantInterpretation
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) world
    let closed : DeoptimizationClosed interpretation :=
      liftRawInterpretation_deoptimizationClosed
        (constantRawInterpretation
          (profile := profile) (command := command)
          (Ground := Ground) (source := source) world)
    let firstExecution := constantInterpretedExecution
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) world first
    let secondExecution := constantInterpretedExecution
      (profile := profile) (command := command)
      (Ground := Ground) (source := source) world second
    deoptInterpreted closed firstExecution ≠
        deoptInterpreted closed secondExecution ∧
      interpretedTarget firstExecution = interpretedTarget secondExecution := by
  dsimp
  constructor
  · apply distinct_elaborations_survive_deoptimization
    exact different
  · rfl

/-! ## One authored meaning can retain contested runtime alternatives -/

namespace Contested

open Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldNativeRealization.Canary
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds.Examples.Contested

def interpretationClosed (selected : profile.World command) :
    DeoptimizationClosed (ContestedInterpretation selected) := by
  constructor
  intro elaboration execution evidence
  cases evidence with
  | chooseAlice => exact .chooseAlice
  | chooseCompetitor => exact .chooseCompetitor

/-- One authored elaboration world still has both contested rho executions
after deoptimization.  The elaboration projections agree and the complete
interpreted worlds remain distinct. -/
theorem runtime_nondeterminism_independent_of_elaboration
    (selected : profile.World command) :
    (deoptInterpreted (interpretationClosed selected)
        (aliceExecution selected)).1 =
      (deoptInterpreted (interpretationClosed selected)
        (competitorExecution selected)).1 ∧
    deoptInterpreted (interpretationClosed selected)
        (aliceExecution selected) ≠
      deoptInterpreted (interpretationClosed selected)
        (competitorExecution selected) := by
  constructor
  · rfl
  · apply distinct_targets_survive_deoptimization
    change alice.target ≠ competitor.target
    simpa only [realize_target] using
      realization_preserves_both_contested_worlds.2

end Contested

#print axioms liftRawInterpretation_deoptimizationClosed
#print axioms deoptInterpreted_refines
#print axioms distinct_elaborations_survive_deoptimization
#print axioms distinct_targets_survive_deoptimization
#print axioms deoptInterpretedWorlds_elaborations
#print axioms deoptInterpretedWorlds_targets
#print axioms authored_ambiguity_independent_of_execution
#print axioms Contested.runtime_nondeterminism_independent_of_elaboration

end Mettapedia.Languages.MeTTa.Prime.GSLTILGradualNativeParallelism
