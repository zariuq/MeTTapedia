import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorCertificates

/-!
# Every live evaluator call follows its actual source clause

Normal-evaluation entries use the real driver. Original machine clauses
preserve the fixed-before episode; its successful normal-next return earns
one native reduction before restarting evaluation. Unmatched machine calls
remain held residuals under the public done bind.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorCallMoves

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalEvaluatorCertificates (Certificate Reaches publicFrame payload)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

theorem evaluating_move {initial : Tower.Tm 0}
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (current : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ())
    (reached : Reaches built initial current)
    (input : Determines K call (NormalEvaluatorGrounding.callCode .evaluate (encodeTm current)))
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (storeBelow : StoreBelow world.scope K) (callBelow : DependsBelow world.scope call)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.apply call), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  intro child member live
  cases moved with
  | apply =>
      obtain ⟨equation, included, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      have same := NormalEvaluatorDriverReadback.evaluate_clause built D world.scope K call (encodeTm current)
        input included live
      subst equation
      have field := NormalEvaluatorGrounding.copied_field_determines built .evaluate world.scope K call
        (encodeTm current) input live
      rw [NormalEvaluatorGrounding.callBranch_shape]
      exact .choosing current world.scope reached field
  | unmatched =>
      have noMatch : ∀ equation ∈ (NormalProgram.program built D).equations,
          ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) world.scope) equation.lhs, call)]) :=
        by assumption
      have matched := NormalEvaluatorGrounding.match_live built .evaluate world.scope K call (encodeTm current)
        storeBelow callBelow input
      exact False.elim (noMatch _ (NormalEvaluatorGrounding.clause_mem built D .evaluate) matched)

theorem machine_move {initial : Tower.Tm 0}
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (before : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (reached : Reaches built initial before) (episode : NormalEvaluatorMachineView.Episode built before code)
    (input : Determines K call code)
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.apply call), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D initial child := by
  intro child member live
  cases moved with
  | apply =>
      obtain ⟨equation, included, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      rcases NormalEvaluatorDriverReadback.active_clause built D world.scope K call code input
        (NormalEvaluatorMachineView.head built episode) included live with original | driver
      · obtain ⟨index, _, rfl⟩ := List.mem_map.mp original
        obtain ⟨after, datum, focus, answered, output⟩ := GroundCall.live_callBranch_determines built.rules D
          index world.scope K call code [publicFrame built D] [] input
          (NormalGroundingCompiled.grounded built _ (List.get_mem built.rules index)) live
        have nextEpisode := NormalEvaluatorMachineView.step built episode ⟨index, answered⟩
        change Certificate built D initial ⟨_,
          (callBranch D world.scope K call [publicFrame built D] [] (BinderCore.embedEquation built.rules index)).focus,
          [publicFrame built D], []⟩
        rw [focus]
        exact .machine before datum after reached nextEpisode output
      · subst equation
        obtain ⟨encoded, shape⟩ := NormalEvaluatorDriverReadback.matching_driver_payload built .resume
          world.scope K call code input live
        obtain ⟨after, reduced, native⟩ := NormalEvaluatorMachineView.resume_view built episode shape.symm
        have resumeInput : Determines K call (NormalEvaluatorGrounding.callCode .resume (encodeTm after)) := by
          rw [← shape, native] at input
          exact input
        have field := NormalEvaluatorGrounding.copied_field_determines built .resume world.scope K call
          (encodeTm after) resumeInput live
        rw [NormalEvaluatorGrounding.callBranch_shape]
        exact .evaluating after (NormalProgram.evaluateAt (payload built world.scope)) (reached.tail reduced)
          (NormalEvaluatorGrounding.determines_callAt built .evaluate field)
  | unmatched =>
      rw [Multiset.mem_singleton.mp member]
      exact .machineValue call code (NormalEvaluatorMachineView.head built episode) input

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorCallMoves

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorCallMoves.evaluating_move
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorCallMoves.machine_move
