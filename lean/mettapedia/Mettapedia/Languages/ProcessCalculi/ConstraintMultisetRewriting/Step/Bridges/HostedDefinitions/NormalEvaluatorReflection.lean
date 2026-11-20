import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorCallMoves
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorScanMoves
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorPhaseMoves

/-!
# Actual public answers are exactly directed native normal results

Every live source alternative keeps its own certificate. Freshness and
arrow frames are earned from the actual public query and its reached
prefix. The resulting reflection composes with the existing execution
construction and frontier transport, rather than using conversion as an
execution oracle. Termination and result typing are separate guarantees.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorReflection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalEvaluatorCertificates (Certificate Reaches)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

theorem move {initial : Tower.Tm 0}
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (known : Certificate built D initial before) (arrow : ArrowBranch before)
    (fresh : NormalScannerReflection.FreshCalls built D world.scope before)
    (moved : Move D (NormalProgram.program built D) supply world before nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  cases known with
  | initial => exact NormalEvaluatorPhaseMoves.initial_move built D supply initial moved
  | evaluating current call reached input =>
      obtain ⟨storeBelow, callBelow⟩ := fresh _ rfl
      exact NormalEvaluatorCallMoves.evaluating_move built D supply _ current call reached input
        storeBelow callBelow moved
  | choosing current scope reached input =>
      exact NormalEvaluatorPhaseMoves.choosing_move built D supply current scope reached input moved
  | startingScan current scope reached input =>
      exact NormalEvaluatorPhaseMoves.startingScan_move built D supply current scope reached input moved
  | machine before call code reached episode input =>
      exact NormalEvaluatorCallMoves.machine_move built D supply _ before call code reached episode input moved
  | machineValue call code head input =>
      exact NormalEvaluatorPhaseMoves.machineValue_move built D supply call code head input moved
  | scanning current scope inside reached input scanner =>
      exact NormalEvaluatorScanMoves.scanning_move built D supply current scope inside reached input scanner
        arrow fresh moved
  | returningDone current datum reached normal input =>
      exact NormalEvaluatorPhaseMoves.returningDone_move built D supply current datum reached normal input moved
  | repliedDone current datum reached normal input =>
      exact NormalEvaluatorPhaseMoves.repliedDone_move built D supply current datum reached normal input moved
  | returning datum correct =>
      exact NormalEvaluatorPhaseMoves.returning_move built D supply datum correct moved
  | finished datum _ =>
      exact NormalEvaluatorPhaseMoves.finished_move built D supply datum moved

def Invariant (initial : Tower.Tm 0) (configuration : Config (BinderCore.keys built.rules) [] () D.Ty) : Prop :=
  ∀ branch ∈ configuration.branches, Solvable branch.store → Certificate built D initial branch

theorem initial_arrows (initial : Tower.Tm 0) :
    NormalFrameTransport.ArrowConfiguration D
      (Config.initial (fun _ => 0) (NormalProgram.query built initial)) := by
  intro branch member
  rw [Multiset.mem_singleton.mp member]
  exact ⟨trivial, .inl ⟨_, rfl, NormalProgramFormation.query_arrows built initial⟩⟩

theorem step {initial : Tower.Tm 0}
    {before after : Config (BinderCore.keys built.rules) [] () D.Ty}
    (reached : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built initial)) before)
    (known : Invariant built D initial before)
    (edge : SourceLanguage.Step D (NormalProgram.program built D) supply before after) :
    Invariant built D initial after := by
  have arrows := NormalFrameTransport.runs_arrows D (NormalProgram.program built D) supply
    (NormalProgramFormation.program_arrows built D) (initial_arrows built D initial) reached
  cases edge with
  | move world nextWorld current rest children live moved =>
      intro child member alive
      rcases Multiset.mem_add.mp member with made | kept
      · have runtimeScope := scoping_reachable (fun _ => 0) (NormalProgram.query built initial)
          (NormalProgramFormation.equations_formed built D)
          (NormalProgramFormation.query_scoped built initial)
          (NormalProgramFormation.query_distinct built initial)
          (NormalProgramFormation.query_arrows built initial)
          _ reached current (Multiset.mem_cons_self _ _)
        exact move built D supply (known current (Multiset.mem_cons_self _ _) live)
          (arrows current (Multiset.mem_cons_self _ _))
          (NormalScannerReflection.fresh_of_scoping built D runtimeScope) moved child made alive
      · exact known child (Multiset.mem_cons_of_mem kept) alive

theorem runs (initial : Tower.Tm 0)
    {after : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built initial)) after) :
    Invariant built D initial after := by
  induction executed with
  | refl =>
      intro branch member _
      rw [Multiset.mem_singleton.mp member]
      exact .initial
  | tail earlier edge ih => exact step built D supply earlier ih edge

theorem finished_reflects {initial : Tower.Tm 0}
    {after : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built initial)) after)
    {branch : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (member : branch ∈ after.branches) (finished : branch.Finished (D := D))
    {value : MClosed} (read : value ∈ branch.answer (D := D)) :
    ∃ normal : Tower.Tm 0,
      value = encodeTm normal ∧ Reaches built initial normal ∧ NormalStructure.Normal built normal := by
  have live : Solvable branch.store := by
    obtain ⟨_, _, X, family, assignment, solved, _⟩ := read
    exact ⟨X, family, assignment, solved⟩
  exact NormalEvaluatorCertificates.finished_read built D
    (runs built D supply initial executed branch member live) finished read

theorem public_source_iff (initial : Tower.Tm 0) (value : MClosed) :
    (∃ after, Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built initial)) after ∧
      NativePublic.Contains (after.answers (D := D)) value) ↔
    ∃ normal : Tower.Tm 0,
      value = encodeTm normal ∧ Reaches built initial normal ∧ NormalStructure.Normal built normal := by
  constructor
  · rintro ⟨after, executed, read⟩
    obtain ⟨branch, member, finished, answer⟩ :=
      (NativePublic.has_answer_iff built.rules after value).mpr read
    exact finished_reflects built D supply executed member finished answer
  · rintro ⟨normal, rfl, reached, normalForm⟩
    obtain ⟨after, branch, executed, member, finished, _, read⟩ :=
      NormalEvaluatorPublic.public_source_executes built D supply reached normalForm
    exact ⟨after, executed, (NativePublic.has_answer_iff built.rules after (encodeTm normal)).mp
      ⟨branch, member, finished, read⟩⟩

include supply in
theorem public_native_iff (N : Hosting.Nodes MSig [] ()) (initial : Tower.Tm 0) (value : MClosed) :
    (∃ next, (FrontierArrow.target (D := D) N (NormalProgram.program built D)).MultiStep
      (FrontierArrow.initialState (D := D) N (NormalProgram.program built D)
        (NormalProgram.query built initial)) next ∧
      NativePublic.Contains (FrontierArrow.answers N next) value) ↔
    ∃ normal : Tower.Tm 0,
      value = encodeTm normal ∧ Reaches built initial normal ∧ NormalStructure.Normal built normal := by
  exact (NormalPublicTransport.prefixes_iff built D supply N initial
    (fun answers => NativePublic.Contains answers value)).symm.trans
      (public_source_iff built D supply initial value)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorReflection

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorReflection.public_source_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorReflection.public_native_iff
