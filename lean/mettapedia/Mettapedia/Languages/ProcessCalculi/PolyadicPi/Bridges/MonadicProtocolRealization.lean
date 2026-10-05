import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolUnaryInvariant
import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.GSLT.Core.OperationalRealizationAccounts

/-!
# The unary protocol as an accounted operational realization

The independently proved protocol supplies an actual unary execution for
every scoped source firing, including equations at both supplied endpoints.
Choosing one such execution gives a realization in the existing free path
category. Each selected source firing expands into one or four communications;
complete paths retain all administrative states and obey the corresponding
cost bounds. The image is the proved unary subset of the shared syntax.

This is a forward realization. Its reachability-scale native logic is distinct
from primitive one-step logic; no arbitrary-schedule reflection or protocol
discipline is inferred merely from these path bounds. RuntimeTransition
independently proves arbitrary-prefix reflection using actual arity roles
and occurrence registries; NamePassingUnaryOperational applies it to the
source-derived roles of the lambda compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

/-- Choice selects a path only from the protocol's proved actual executions. -/
noncomputable def selectedBlock {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) :
    (operationalTheory Γ).RewritePath (lower source) (lower target) :=
  Classical.choose (stepModulo_lower_path step)

theorem selectedBlock_length {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) :
    (selectedBlock step).length = 1 ∨ (selectedBlock step).length = 4 :=
  Classical.choose_spec (stepModulo_lower_path step)

/-- The nontrivial syntax lowering and its actual retained protocol paths. -/
noncomputable def realization (Γ : Ctx sig) :
    OperationalRealization (operationalTheory Γ) (operationalTheory Γ) where
  mapTerm := lower
  mapEquiv := lower_structural
  mapStep step := rewritePathToExecutionPath (selectedBlock step)

theorem realization_unary (Γ : Ctx sig) (process : Proc Γ) :
    Unary ((realization Γ).mapTerm process) := lower_unary process

theorem realization_step_length {Γ : Ctx sig} {source target : Proc Γ}
    (step : (operationalTheory Γ).Step source target) :
    ((realization Γ).mapStep step).length = 1 ∨
      ((realization Γ).mapStep step).length = 4 := by
  have converted := rewritePathToExecutionPath_length (selectedBlock step)
  rcases selectedBlock_length step with one | four
  · exact Or.inl (converted.trans one)
  · exact Or.inr (converted.trans four)

theorem realization_step_bounds {Γ : Ctx sig} {source target : Proc Γ}
    (step : (operationalTheory Γ).Step source target) :
    1 ≤ ((realization Γ).mapStep step).length ∧
      ((realization Γ).mapStep step).length ≤ 4 := by
  rcases realization_step_length step with one | four <;> omega

/-- Every primitive communication, including protocol administration, is
charged; static changes of representative introduce no extra firing. -/
theorem realization_path_bounds {Γ : Ctx sig} {source target : Proc Γ}
    (path : ExecutionPath (operationalTheory Γ) source target) :
    path.length ≤ ((realization Γ).mapRoute path).length ∧
      ((realization Γ).mapRoute path).length ≤ 4 * path.length := by
  simpa only [Nat.one_mul] using
    (realization Γ).mapRoute_length_bounds 1 4 (fun step => realization_step_bounds step) path

/-- Every actual intermediate representative in the selected expansion is
unary, including equation administration around each communication. -/
theorem realization_path_unary {Γ : Ctx sig} {source target : Proc Γ}
    (path : ExecutionPath (operationalTheory Γ) source target) :
    executionPathUnary ((realization Γ).mapRoute path) :=
  lowered_executionPath_unary source _

theorem realization_account {Γ : Ctx sig} {source target : Proc Γ}
    (path : ExecutionPath (operationalTheory Γ) source target) :
    ((realization Γ).blockAccount).of path =
      Multiplicative.ofAdd ((realization Γ).mapRoute path).length := rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
