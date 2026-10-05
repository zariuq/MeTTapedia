import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRho
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentProtocol
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInitialRuntime

/-!
# The whole environment compiler enters the real core-rho runtime

The supplied result of the lambda/polyadic/unary compiler initializes the
same actual allocator and cursor used by the core-rho execution proofs.
Source names have an explicit injective seed interpretation. The result
retains the literal emitted code and its finite active inventory; static
lambda laws continue to be interpreted by the existing source protocol.

Runtime initialization is distinct from arbitrary-schedule reflection and
from the observation contract of a compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoRuntime

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryInventory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- This uses a supplied successful result of the actual three-stage
compiler, including all definitions and environment carriers. -/
theorem supplied_runtime {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (world : SeedWorld Δ)
    (code : Code 0) (supplied : NamePassingRho.compile term environment result world.world = some code) :
    ∃ activities : List (Activity Δ),
      Inventory world activities ∧
      StructuralEq (MonadicProtocol.lower (NamePassingLambda.compile term environment result))
        (source activities) ∧
      StructuralCongruence (RhoUnaryExecution.runtime code world.available)
        (actual world.world activities) :=
  RhoUnaryInitialRuntime.initial_runtime
    (NamePassingRho.guarded_compiler_image term environment result) world code supplied

/-- Every source context has a genuinely fresh result channel and a
nonempty actual runtime entry, independently of its eventual computation. -/
theorem fresh_runtime {Γ : Ctx sig} (term : NamePassingLambda.Expr Γ) :
    ∃ (code : Code 0) (activities : List (Activity (.nm :: Γ))),
      NamePassingRho.compile term (fun _ name => Var.succ name) .zero
        (RhoUnaryWorld.initial (.nm :: Γ)).world = some code ∧
      Inventory (RhoUnaryWorld.initial (.nm :: Γ)) activities ∧
      StructuralEq (MonadicProtocol.lower
        (NamePassingLambda.compile term (fun _ name => Var.succ name) .zero))
        (source activities) ∧
      StructuralCongruence (RhoUnaryExecution.runtime code (Γ.length + 1))
        (actual (RhoUnaryWorld.initial (.nm :: Γ)).world activities) := by
  let world := RhoUnaryWorld.initial (.nm :: Γ)
  obtain ⟨code, supplied⟩ := NamePassingRho.compile_total term (fun _ name => Var.succ name) .zero world.world
  obtain ⟨activities, inventory, sourceEq, actualEq⟩ :=
    supplied_runtime term (fun _ name => Var.succ name) .zero world code supplied
  exact ⟨code, activities, supplied, inventory, sourceEq, actualEq⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoRuntime
