import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalCorrespondence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeDrain
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolSimulation

/-!
# Implementing a lambda step from every retained tuple-protocol phase

Outstanding private communications are completed against their actual
occurrence registry. The independently checked lambda compiler and unary
protocol then implement the supplied source step, with its literal compiled
endpoint. The resulting state has a freshly initialized, zero-debt witness.
This forward result does not restrict which target prefix preceded it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryForward

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingEnvironmentEquationsNative
open MonadicProtocol MonadicProtocol.RuntimeWitness

/-- Every source reference lies after the independently reserved result name. -/
def references (Γ : Ctx sig) : Ren sig Γ (.nm :: Γ) := fun _ name => .succ name

def polyadic {Γ : Ctx sig} (source : Expr Γ) : Proc (.nm :: Γ) :=
  compile source (references Γ) .zero

def unary {Γ : Ctx sig} (source : Expr Γ) : Proc (.nm :: Γ) := lower (polyadic source)

theorem references_faithful (Γ : Ctx sig) : Function.Injective (references Γ .nm) :=
  fun _ _ equal => Var.succ.inj equal

theorem references_fresh (Γ : Ctx sig) (name : Var Γ .nm) :
    references Γ .nm name ≠ (Var.zero : Var (.nm :: Γ) .nm) := by
  intro equal
  cases equal

theorem initial {Γ : Ctx sig} (source : Expr Γ) :
    ∃ witness : Witness (polyadic source) (unary source), witness.debt = 0 :=
  initialized_debt_zero (MonadicProtocol.guarded_compiler_image source (references Γ) .zero)
    (NamePassingChannelRoles.canonicalRoles Γ)
    (NamePassingChannelRoles.fresh_result_compile_typed source)

/-- The supplied lambda step is implemented after exactly the pending debt,
followed by one unary communication or the four-communication tuple protocol.
No equation is inserted as an execution event, and the final term is literal. -/
theorem forward {Γ : Ctx sig} {source after : Expr Γ} {current : Proc (.nm :: Γ)}
    (before : Witness (polyadic source) current) (step : (sourceTheory Γ).Step source after) :
    ∃ path : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ)) current (unary after),
      ∃ witness : Witness (polyadic after) (unary after),
        witness.debt = 0 ∧
        (path.length = before.debt + 1 ∨ path.length = before.debt + 4) := by
  let completed := RuntimeDrain.drain before
  have emitted : StepModulo (polyadic source) (polyadic after) :=
    (compiler (references Γ) .zero).mapStep step
  obtain ⟨block, counted⟩ := stepModulo_lower_path emitted
  have positive : 0 < block.length := by
    rcases counted with one | four <;> omega
  let fromActual := pathSourceEquation completed.equal block positive
  let execution := completed.path.append (rewritePathToExecutionPath fromActual)
  obtain ⟨witness, stable⟩ := initial after
  refine ⟨execution, witness, stable, ?_⟩
  have converted := rewritePathToExecutionPath_length fromActual
  have shifted := pathSourceEquation_length completed.equal block positive
  have whole : execution.length = before.debt + block.length := by
    change (completed.path.append (rewritePathToExecutionPath fromActual)).length = _
    exact (Route.length_append completed.path (rewritePathToExecutionPath fromActual)).trans
      (congrArg₂ Nat.add completed.counted (converted.trans shifted))
  rcases counted with one | four
  · exact .inl (whole.trans (congrArg (fun count => before.debt + count) one))
  · exact .inr (whole.trans (congrArg (fun count => before.debt + count) four))

theorem forward_positive {Γ : Ctx sig} {source after : Expr Γ} {current : Proc (.nm :: Γ)}
    (before : Witness (polyadic source) current) (step : (sourceTheory Γ).Step source after) :
    ∃ path : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ)) current (unary after),
      0 < path.length ∧ Nonempty (Witness (polyadic after) (unary after)) := by
  obtain ⟨path, witness, _, counted⟩ := forward before step
  refine ⟨path, ?_, ⟨witness⟩⟩
  rcases counted with one | four <;> omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryForward
