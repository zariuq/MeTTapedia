import Mettapedia.Machines.CMemory.EffectStatements
import Mettapedia.Machines.CMemory.DependencyCollectionOperands
import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.OrderedDependencyCPreparationAdmission

/-!
# Failed dependency preparation releases its actual pending allocation

The selected branch is extracted from the complete, recognized preparation
source. Its actual condition, deallocation operand and returned value are
retained. The physical contract frees the entire private allocation, including
uninitialized spare cells, while preserving module storage, input storage and
unrelated resources. It uses the shared framed-call proof service.

This is the failed-cleanup branch, not a refinement of the whole preparation
function or of concurrent publication. Capacities are cell counts here;
byte layout and ABI realization are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.DependencyCleanup

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open OrderedDependencyCPreparationSource
open ReadExpressions DependencyCollectionOperands DependencyValidationOperands
open DependencyExpressionReads Lift CellPermission

def site : Option CStatement := preparationFunction.body[13]?

def parsedSite : Option CStatement := do
  let actual ← declaratorFunctionText? typeNames preparationSource.toList
  actual.body[13]?

theorem parsed_site_retains_actual_branch : parsedSite = site := by
  unfold parsedSite
  rw [complete_preparation_source_admitted]
  rfl

theorem site_has_authored_cleanup : site = some (.branch
    (.unary .not (.identifier "ok".toList))
    [.effect (.call "free".toList [.identifier "pending".toList]),
      .return (some (.bool false))] []) := rfl

def execute (layout : ReadExpressions.Layout) (bodyFuel : Nat)
    (environment : ReadExpressions.Environment) : CProg CVal ReadBlock.Result :=
  match site with
  | some actual => EffectStatements.selected (EffectStatements.deallocate "free".toList)
      PostIndexWrites.assign layout 0 bodyFuel environment actual
  | none => CProg.undefined

theorem failure_deallocates_before_return (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (pending : Ptr)
    (failed : environment "ok".toList = some (.bool false))
    (pendingRead : environment "pending".toList = some (.ptr (some pending))) :
    execute layout 1 environment = (CProg.free (some pending) >>= fun _ =>
      pure (.finished (.returned environment (some (.bool false))))) := by
  simp only [execute, site_has_authored_cleanup, EffectStatements.selected,
    EffectStatements.beforeBlock, expression, expressionWith_equation, failed, resolved, truth,
    EffectStatements.bound_pointer_operand_is_not_replaced _ _ _ _ _ pendingRead,
    StatementBlock.execute, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
    Bool.not_false, ↓reduceIte]
  rw [StatementBlock.executeWith_equation]
  rfl

theorem success_does_not_read_pending (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment)
    (succeeded : environment "ok".toList = some (.bool true)) (bodyFuel : Nat) :
    execute layout bodyFuel environment = pure (.finished (.next environment)) := by
  simp only [execute, site_has_authored_cleanup, EffectStatements.selected,
    EffectStatements.beforeBlock, expression, expressionWith_equation, succeeded, resolved, truth,
    StatementBlock.execute, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [StatementBlock.executeWith_equation]
  rfl

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} (addr : Id → Ptr)

theorem failed_cleanup_preserves_store_and_input (layout : SpaceLayout)
    (D : List Id) (H : SplitHeap Id) (array : Ptr) (inputCapacity : Nat)
    (inputs : List (Option Id)) (pending : Ptr) (capacity : Nat) (values : List Id)
    (environment : ReadExpressions.Environment)
    (failed : environment "ok".toList = some (.bool false))
    (pendingRead : environment "pending".toList = some (.ptr (some pending)))
    (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (execute (fields layout) 1 environment)
      (fun result σ => result = .finished (.returned environment (some (.bool false))) ∧
        InputState addr layout D H array inputCapacity inputs
          (DeadStorage (some pending) capacity ∗ F) σ) := by
  rw [failure_deallocates_before_return _ _ _ failed pendingRead]
  cmem_start σ h
  unfold PendingState at h
  unfold InputState StoreState at h ⊢
  obtain ⟨wf, h⟩ := h
  cmem_norm
  cmem_call EffectStatements.deallocate_dynamic_array pending capacity
    (values.map (spacePtr ∘ addr))
  rintro _ σ' held wellFormed
  refine ⟨wellFormed, ?_⟩
  cmem_exact

namespace Controls

theorem insufficient_return_fuel_is_not_a_false_result (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (pending : Ptr)
    (failed : environment "ok".toList = some (.bool false))
    (pendingRead : environment "pending".toList = some (.ptr (some pending))) :
    execute layout 0 environment =
      (CProg.free (some pending) >>= fun _ => pure .exhausted) := by
  simp only [execute, site_has_authored_cleanup, EffectStatements.selected,
    EffectStatements.beforeBlock, expression, expressionWith_equation, failed, resolved, truth,
    EffectStatements.bound_pointer_operand_is_not_replaced _ _ _ _ _ pendingRead,
    StatementBlock.execute, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
    Bool.not_false, ↓reduceIte]
  rw [StatementBlock.executeWith_equation]
  rfl

theorem failed_cleanup_without_pending_is_undefined (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment)
    (failed : environment "ok".toList = some (.bool false))
    (absent : environment "pending".toList = none) :
    execute layout 1 environment = CProg.undefined := by
  simp only [execute, site_has_authored_cleanup, EffectStatements.selected,
    EffectStatements.beforeBlock, expression, expressionWith_equation, failed, resolved, truth,
    EffectStatements.deallocation_keeps_actual_operand, absent,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
    Bool.not_false, ↓reduceIte]
  change ((CProg.undefined >>= _) >>= _) = _
  rw [undefined_bind, undefined_bind]

end Controls

end Mettapedia.Machines.CMemory.DependencyCleanup
