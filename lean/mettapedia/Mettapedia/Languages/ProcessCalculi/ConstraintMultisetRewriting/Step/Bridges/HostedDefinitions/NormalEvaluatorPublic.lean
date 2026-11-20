import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalPublicTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NativePublic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerExecutionControls

/-!
# Directed native normal forms reach the actual public result

The real source query binds its held done reply and returns the payload.
Freshness for that bind follows from the actual reached source configuration.
The final transport observes membership in the native frontier's bag of
reading sets, without counting native reduction strategies as multiplicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPublic

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable {dev : Definitions.Development} (built : Compiled dev)

theorem opened_result_copy (scope : Nat) :
    instantiate (openAt (BinderCore.keys built.rules)
      (PublicQuery.site RuntimeSubstitution.rules built.authored) scope)
      (PublicQuery.result RuntimeSubstitution.rules built.authored) =
    instantiate (copyAt (BinderCore.keys built.rules) scope)
      (PublicQuery.result RuntimeSubstitution.rules built.authored) :=
  (PublicQuery.opened_result RuntimeSubstitution.rules built.authored scope).trans
    (BinderCore.copy_embed built.rules scope (PublicQuery.site RuntimeSubstitution.rules built.authored)
      (RuleBuilder.slot (ProgramLayout.resultHole RuntimeSubstitution.rules built.authored))).symm

theorem bind_has_result_below {scope : Nat}
    {store : List (Constraint (BinderCore.keys built.rules) [] ())}
    {reply : Data (BinderCore.keys built.rules) [] ()} {value : MClosed}
    (storeBelow : Hosting.StoreBelow scope store) (replyBelow : Hosting.DependsBelow scope reply)
    (read : Reads store reply (doneC value)) :
    Reads (store ++ [(instantiate (openAt (BinderCore.keys built.rules)
      (PublicQuery.site RuntimeSubstitution.rules built.authored) scope)
      (PublicReadout.pattern (PublicQuery.result RuntimeSubstitution.rules built.authored)), reply)])
      (instantiate (openAt (BinderCore.keys built.rules)
        (PublicQuery.site RuntimeSubstitution.rules built.authored) scope)
        (PublicQuery.result RuntimeSubstitution.rules built.authored)) value := by
  obtain ⟨X, target, assignment, solved, replyRead⟩ := read
  let site : (BinderCore.keys built.rules).Site := PublicQuery.site RuntimeSubstitution.rules built.authored
  let result : Data (BinderCore.keys built.rules) [] () := PublicQuery.result RuntimeSubstitution.rules built.authored
  let environment := PublicQuery.groundResult RuntimeSubstitution.rules built.authored value
  let atResult := NormalProbeFreshness.equationAssignment built target site environment
  let extension := Hosting.graft scope assignment atResult
  have resultRead : instantiate atResult result = Rigid.includeTerm target value := by
    change instantiate atResult (generator (fam (BinderCore.keys built.rules))
      ⟨[], ProgramLayout.resultKey RuntimeSubstitution.rules built.authored⟩) = _
    rw [instantiate_generator]
    change Rigid.includeTerm target (ProgramBinders.extendGround built.rules.get site environment
      ⟨site, ProgramLayout.resultHole RuntimeSubstitution.rules built.authored⟩) = _
    rw [congrFun (ProgramBinders.extendGround_at built.rules.get site environment)
      (ProgramLayout.resultHole RuntimeSubstitution.rules built.authored)]
    rfl
  have outputRead : instantiate extension
      (instantiate (openAt (BinderCore.keys built.rules) site scope) result) = Rigid.includeTerm target value := by
    exact (congrArg (instantiate extension) (opened_result_copy built scope)).trans
      ((Hosting.graft_copy scope assignment atResult result).trans resultRead)
  have originalRead : instantiate extension reply = Rigid.includeTerm target (doneC value) :=
    (Hosting.instantiate_graft_below assignment atResult replyBelow).trans replyRead
  refine ⟨X, target, extension, (models_append extension _ _).mpr ⟨?_, ?_⟩, outputRead⟩
  · exact (Hosting.models_graft assignment atResult storeBelow).mpr solved
  · apply (models_singleton extension _).mpr
    dsimp only
    rw [PublicReadout.instantiate_pattern, PublicReadout.instantiate_pattern, outputRead, originalRead]
    exact PublicReadout.include_done target value

private theorem value_below {scope : Nat} {D : Discipline MSig [] ()}
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {reply : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (runtimeScope : Hosting.Scoping scope (⟨K, .value reply, frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty)) :
    Hosting.StoreBelow scope K ∧ Hosting.DependsBelow scope reply := by
  obtain ⟨visible, level, levels, invariant⟩ := runtimeScope
  constructor
  · intro equation member
    constructor
    all_goals
      intro X target first second agree
      apply instantiate_congr
      intro name used
      apply agree name
    · exact invariant.visibleBelow name ((invariant.store equation member).1 name used)
    · exact invariant.visibleBelow name ((invariant.store equation member).2 name used)
  · intro X target first second agree
    apply instantiate_congr
    intro name used
    exact agree name (invariant.visibleBelow name (invariant.focus name used))

variable (D : Discipline MSig [] ()) (supply : Nat → MClosed)

theorem reply_finishes (input : Tower.Tm 0) (value : MClosed)
    (current : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built input)) current)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (payload : Data (BinderCore.keys built.rules) [] ())
    (member : (⟨K, .value (NormalProgram.doneAt payload),
      [PublicQuery.frame RuntimeSubstitution.rules built.authored], []⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches)
    (determined : Determines K payload value) :
    ∃ next branch, Runs D (NormalProgram.program built D) supply current next ∧
      branch ∈ next.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      value ∈ branch.answer (D := D) := by
  let reply := NormalProgram.doneAt payload
  let result := PublicQuery.result RuntimeSubstitution.rules built.authored
  let site := PublicQuery.site RuntimeSubstitution.rules built.authored
  let pattern := PublicReadout.pattern result
  let opened := openAt (BinderCore.keys built.rules) site current.world.scope
  let output := instantiate opened result
  let finalStore := K ++ [(instantiate opened pattern, reply)]
  obtain ⟨storeBelow, replyBelow⟩ := value_below built
    (Hosting.scoping_reachable (fun _ => 0) (NormalProgram.query built input)
      (NormalProgramFormation.equations_formed built D) (NormalProgramFormation.query_scoped built input)
      (NormalProgramFormation.query_distinct built input) (NormalProgramFormation.query_arrows built input)
      current reached _ member)
  have replyDetermined : Determines K reply (doneC value) := by
    refine ⟨determined.1, ?_⟩
    intro X target assignment solved
    simp only [reply, NormalProgram.doneAt, NormalScanner.instantiate_nodeAt, List.map_cons, List.map_nil]
    rw [determined.2 target assignment solved]
    exact (NormalScanner.include_nodeAt target doneTag [value]).symm
  have outputRead : Reads finalStore output value :=
    bind_has_result_below built storeBelow replyBelow ((replyDetermined.reads_iff _).mpr rfl)
  have live : Solvable finalStore := by
    obtain ⟨X, target, assignment, solved, _⟩ := outputRead
    exact ⟨X, target, assignment, solved⟩
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  let returning : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨current.world.fresh, (⟨finalStore, .eval (.ret output), [], []⟩ ::ₘ rest)⟩
  have bind : SourceLanguage.Step D (NormalProgram.program built D) supply current returning :=
    SourceLanguage.Step.of_eq split rfl determined.1
      (.letBind current.world K reply site pattern (.ret result) [] [])
  let branch : Branch (BinderCore.keys built.rules) [] () D.Ty := ⟨finalStore, .value output, [], []⟩
  let next : Config (BinderCore.keys built.rules) [] () D.Ty := ⟨current.world.fresh, branch ::ₘ rest⟩
  have finish : SourceLanguage.Step D (NormalProgram.program built D) supply returning next :=
    SourceLanguage.Step.of_eq rfl rfl live (.ret current.world.fresh finalStore output [] [])
  exact ⟨next, branch, (Relation.ReflTransGen.single bind).tail finish, Multiset.mem_cons_self _ _,
    ⟨rfl, output, rfl⟩, live, output, rfl, outputRead⟩

theorem public_source_executes {before normalForm : Tower.Tm 0}
    (reductions : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) before normalForm)
    (normal : NormalStructure.Normal built normalForm) :
    ∃ next branch, Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built before)) next ∧
      branch ∈ next.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      encodeTm normalForm ∈ branch.answer (D := D) := by
  let frame : Frame (BinderCore.keys built.rules) [] () D.Ty :=
    PublicQuery.frame RuntimeSubstitution.rules built.authored
  let current := ContinuationLift.configuration frame (BinderCore.start built.rules (Ty := D.Ty) (NormalProgram.code before))
  let datum := Rigid.includeTerm (fam (BinderCore.keys built.rules)) (encodeTm before)
  have start : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query built before)) current :=
    Relation.ReflTransGen.single (NormalPublicTransport.initial_step built D supply before)
  have member : (⟨[], .eval (.apply (NormalProgram.evaluateAt datum)), [frame], []⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches := by
    have callEq : NormalProgram.evaluateAt datum =
        Rigid.includeTerm (fam (BinderCore.keys built.rules)) (NormalProgram.code before) :=
      (NormalEvaluatorGrounding.include_callAt (fam (BinderCore.keys built.rules)) .evaluate (encodeTm before)).symm
    rw [callEq]
    exact Multiset.mem_singleton_self _
  have live : Solvable ([] : List (Constraint (BinderCore.keys built.rules) [] ())) :=
    ⟨Empty, ProgramBinders.ground MSig, ProgramBinders.close (fam (BinderCore.keys built.rules)),
      fun _ inside => False.elim (List.not_mem_nil inside)⟩
  have determined := NormalProbeFreshness.determines_include built [] live (encodeTm before)
  obtain ⟨replied, extra, payload, run, included, available⟩ :=
    NormalEvaluatorExecution.completes_branch built D supply (fun _ => 0) (NormalProgram.query built before)
      (NormalProgramFormation.query_scoped built before) (NormalProgramFormation.query_distinct built before)
      (NormalProgramFormation.query_arrows built before) reductions normal current start [] datum [frame] [] member determined
  obtain ⟨next, branch, finished, present, done, alive, read⟩ :=
    reply_finishes built D supply before (encodeTm normalForm) replied (start.trans run) extra payload included available
  exact ⟨next, branch, (start.trans run).trans finished, present, done, alive, read⟩

include supply in
theorem public_native_executes (N : Hosting.Nodes MSig [] ()) {before normalForm : Tower.Tm 0}
    (reductions : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) before normalForm)
    (normal : NormalStructure.Normal built normalForm) :
    ∃ next, (FrontierArrow.target (D := D) N (NormalProgram.program built D)).MultiStep
      (FrontierArrow.initialState (D := D) N (NormalProgram.program built D) (NormalProgram.query built before)) next ∧
      NativePublic.Contains (FrontierArrow.answers N next) (encodeTm normalForm) := by
  obtain ⟨after, branch, run, member, finished, _, read⟩ := public_source_executes built D supply reductions normal
  apply (NormalPublicTransport.prefixes_iff built D supply N before
    (fun answers => NativePublic.Contains answers (encodeTm normalForm))).mp
  exact ⟨after, run, (NativePublic.has_answer_iff built.rules after (encodeTm normalForm)).mp
    ⟨branch, member, finished, read⟩⟩

theorem named_normal_public (term : Tower.Tm 0)
    (selected : term ∈ [NormalScanner.lambdaExample, NormalScanner.piExample, NormalScanner.idExample]) :
    ∃ next branch, Runs D (NormalProgram.program ExecutionControls.built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query ExecutionControls.built term)) next ∧
      branch ∈ next.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      encodeTm term ∈ branch.answer (D := D) :=
  public_source_executes ExecutionControls.built D supply .refl
    (NormalScannerExecutionControls.named_normal term selected)

theorem beta_below_binder_public :
    ∃ next branch, Runs D (NormalProgram.program ExecutionControls.built D) supply
      (Config.initial (fun _ => 0) (NormalProgram.query ExecutionControls.built
        NormalScannerExecutionControls.betaBelowBinder)) next ∧
      branch ∈ next.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      encodeTm NormalScanner.lambdaExample ∈ branch.answer (D := D) :=
  public_source_executes ExecutionControls.built D supply
    (.single NormalScannerExecutionControls.beta_below_binder_reduces) NormalScannerExecutionControls.lambda_normal

theorem beta_below_binder_mettaNodes (sourceSupply : Nat → MClosed) :
    ∃ next, (FrontierArrow.target (D := untyped.discipline) Hosting.mettaNodes
      (NormalProgram.program ExecutionControls.built untyped.discipline)).MultiStep
      (FrontierArrow.initialState (D := untyped.discipline) Hosting.mettaNodes
        (NormalProgram.program ExecutionControls.built untyped.discipline)
        (NormalProgram.query ExecutionControls.built NormalScannerExecutionControls.betaBelowBinder)) next ∧
      NativePublic.Contains (FrontierArrow.answers Hosting.mettaNodes next) (encodeTm NormalScanner.lambdaExample) :=
  public_native_executes ExecutionControls.built untyped.discipline sourceSupply Hosting.mettaNodes
    (.single NormalScannerExecutionControls.beta_below_binder_reduces) NormalScannerExecutionControls.lambda_normal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPublic

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPublic.public_source_executes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorPublic.public_native_executes
