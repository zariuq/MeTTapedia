import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventory

/-!
# Supplied compiler outputs initialize the actual shared runtime

The whole guarded-unary fragment enters the active-image invariant with the
real allocator listener and its cursor token. Both source and actual rho
readouts use their existing structural equations. The token and seed bounds
are supplied by the explicit nominal world, not by a scheduler or an oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInitialRuntime

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive
open RhoUnaryExecution RhoUnaryImage RhoUnaryInventory
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

theorem source_with_allocator {Γ : Ctx sig} (activities : List (Activity Γ)) (seed : Nat) :
    StructuralEq (source (activities ++ [.allocatorReady, .token seed])) (source activities) := by
  refine .trans (.symm (source_append activities [.allocatorReady, .token seed])) ?_
  change StructuralEq (par (source activities) (par nil (par nil nil))) (source activities)
  exact .trans (.par (.refl _) (.trans (.par (.refl _) (.parUnit _)) (.parUnit _))) (.parUnit _)

/-- The actual supplied code and active frontier are equal modulo rho's
equations after adding the very same allocator components to each. -/
theorem actual_with_allocator {Γ : Ctx sig} (world : World Γ 0)
    (activities : List (Activity Γ)) (code : Code 0) (seed : Nat)
    (image : StructuralCongruence code.term (actual world activities)) :
    StructuralCongruence (runtime code seed)
      (actual world (activities ++ [.allocatorReady, .token seed])) := by
  refine .trans _ (RhoScopedServers.parallel [actual world activities,
    server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState seed]) _ ?_ ?_
  · apply StructuralCongruence.par_cong
      [code.term, server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState seed]
      [actual world activities, server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState seed] rfl
    intro index leftBound rightBound
    match index with
    | 0 => exact image
    | 1 | 2 => exact .refl _
    | index + 3 => simp at leftBound
  · simpa [actual, headers, HeaderInversion.parallel, List.map_append, Activity.header,
      Header.pattern, server, stateToken, GuardedReplication.idle] using
      Context.par_flatten_head ((headers world activities).map Header.pattern)
        [server allocatorSelf allocatorState allocatorRequest, stateToken allocatorState seed]

/-- Every successful output for every guarded source process has a
nonempty, valid runtime image with the original source readout. -/
theorem initial_runtime {Γ : Ctx sig} {process : Proc Γ}
    (guarded : GuardedUnary process) (world : SeedWorld Γ) (code : Code 0)
    (supplied : compile world.world process = some code) :
    ∃ activities : List (Activity Γ),
      Inventory world activities ∧
      StructuralEq process (source activities) ∧
      StructuralCongruence (runtime code world.available) (actual world.world activities) := by
  obtain ⟨image, initial, sourceImage, targetImage, balanced⟩ :=
    initial_image_balanced guarded world.world code supplied
  refine ⟨image ++ [.allocatorReady, .token world.available],
    initial_inventory world initial balanced, ?_,
    actual_with_allocator world.world image code world.available targetImage⟩
  exact .trans sourceImage (.symm (source_with_allocator image world.available))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInitialRuntime
