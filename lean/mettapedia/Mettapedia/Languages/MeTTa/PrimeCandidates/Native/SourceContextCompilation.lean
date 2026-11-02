import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceContextCompilation
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceCompositionalAdequacy

/-!
# Compiled source contexts in the actual shared-return machine

The source context and its target context are built independently of their
hole expressions. Their proved plugging equation connects the existing source
observation to actual shared-return execution, preserving and reflecting
completed ordered observations with branch effects. Quotation is admitted
because this is compilation of the same supplied syntax, not replacement of
arbitrary computations having equal completed observations.

Named lexical crossings, live revisions and external transactional effects
remain outside this fixed-program source profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceContextCompilation

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
open ContextCompilation

theorem preservation (profile : Profile) (program : SProgram)
    (context : Source) (expression : Expr) {results : List Result}
    (source : SourceObserves profile program (context.plug expression) results) :
    ∃ steps observations,
      SharedFinished (program.toCore profile)
        ((context.compile profile id).plug
          (expression.toCore profile (context.holeRenaming id))) steps true ∧
      sharedObservations (program.toCore profile) steps
        ((context.compile profile id).plug
          (expression.toCore profile (context.holeRenaming id))) = some observations ∧
      List.Forall₂ ObservationRel results observations := by
  rw [← Source.compile_plug]
  exact SourceCompositionalAdequacy.preservation source

theorem no_invention (profile : Profile) (program : SProgram)
    (context : Source) (expression : Expr) {steps : Nat}
    (finished : SharedFinished (program.toCore profile)
      ((context.compile profile id).plug
        (expression.toCore profile (context.holeRenaming id))) steps true) :
    ∃ results observations, SourceObserves profile program (context.plug expression) results ∧
      sharedObservations (program.toCore profile) steps
        ((context.compile profile id).plug
          (expression.toCore profile (context.holeRenaming id))) = some observations ∧
      List.Forall₂ ObservationRel results observations := by
  rw [← Source.compile_plug] at finished ⊢
  exact SourceCompositionalAdequacy.no_invention finished

theorem completion_iff (profile : Profile) (program : SProgram)
    (context : Source) (expression : Expr) (keepReceipts : Bool) :
    (∃ results, SourceObserves profile program (context.plug expression) results) ↔
      ∃ steps, SharedFinished (program.toCore profile)
        ((context.compile profile id).plug
          (expression.toCore profile (context.holeRenaming id))) steps keepReceipts := by
  rw [← Source.compile_plug]
  exact SourceCompositionalAdequacy.completion_iff profile program _ keepReceipts

/-- The same construction applies at an equation body's source root; the
reserved-head shift and arity remain the source compiler's own operations. -/
theorem equation_body (profile : Profile) (head arity : Nat)
    (context : Source) (expression : Expr) :
    (SRule.toCore profile ⟨head, arity, context.plug expression⟩) =
      ⟨head + 1, arity,
        (context.compile profile id).plug
          (expression.toCore profile (context.holeRenaming id))⟩ := by
  simp only [SRule.toCore, Source.compile_plug]

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceContextCompilation
