import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceTransition

/-!
# Chronological writer observation of funded executions

The existing `FundedExecution` parameterized monad retains its full pre/post
resource states and certified transition.  Its ordered raw emissions also
admit an observation in the concrete free-action writer monad.  This observation
preserves pure return, result mapping, and funded bind.

Each emitted letter retains the event identifier, causes, located funding, and
raw spend.  This account is a chronological word rather than a signature total.
The observation does not reconstruct a funded transition from an arbitrary
word, and is not the authored Cost language transformer.
-/

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.Cost.FundedWriter

open Mettapedia.CategoryTheory.WriterActionAdjunction
open Mettapedia.Effects
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

set_option autoImplicit false

/-- The account monoid retains chronological runtime event records. -/
abbrev ReceiptAccount := FreeMonoid RawEmittedEvent

/-- Observe an already certified funded execution.  Resource indices and
the transition evidence remain in the input, before this readout is taken.
This is the chronological emission account of the run, read with the result. -/
def interpret {Result : Type} {source target : FundedState}
    (execution : FundedExecution source target Result) :
    (writerMonad ReceiptAccount).obj Result :=
  ResourceTransition.emissionAccount.read execution

/-- Parameterized pure return is observed by the ordinary writer unit. -/
theorem interpret_pure {Result : Type} (state : FundedState) (result : Result) :
    interpret (Execution.pure state result) =
      (writerMonad ReceiptAccount).η.app Result result :=
  ResourceTransition.emissionAccount.read_pure state result

/-- Returning a mapped result retains the entire chronological account. -/
theorem interpret_map {Result NextResult : Type}
    {source target : FundedState} (function : Result → NextResult)
    (execution : FundedExecution source target Result) :
    interpret (execution.map function) =
      (writerMonad ReceiptAccount).map (TypeCat.ofHom function) (interpret execution) :=
  ResourceTransition.emissionAccount.read_map function execution

/-- Certified bind concatenates emissions in execution order before the
writer multiplication returns the continuation's result. -/
theorem interpret_bind {Result NextResult : Type}
    {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    interpret (first.bind next) =
      (writerMonad ReceiptAccount).μ.app NextResult
        ((writerMonad ReceiptAccount).map
          (TypeCat.ofHom fun result => interpret (next result)) (interpret first)) :=
  ResourceTransition.emissionAccount.read_bind first next

/-- A computation with the same complete resource state at both ends has
the pure account: genuine firing would advance the retained event counter. -/
theorem interpret_endomorphism {Result : Type} (state : FundedState)
    (execution : FundedExecution state state Result) :
    interpret execution =
      (writerMonad ReceiptAccount).η.app Result execution.result := by
  change (FreeMonoid.ofList (CostPath.rawEmission execution.transition),
      execution.result) = (1, execution.result)
  rw [FundedExecution.endomorphism_transition_eq_identity]
  rfl

end Mettapedia.GSLT.LanguageDef.Cost.FundedWriter
