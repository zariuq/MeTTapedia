import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPhase
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReindex

/-!
# Private-name delivery into an arbitrary concrete active frame

The supplied reply receiver determines the source binder that is opened.
The unrelated activity frame is moved into that extended source context
without changing any actual rho header. The result includes the actual
compiled body image and the complete private source scope, including all
duplicate frame occurrences and suspended server continuations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryDelivery

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryWorld RhoUnaryActive
open RhoUnaryImage RhoUnaryPhase RhoUnaryReindex RhoUnaryCredit
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-- Replace one supplied contractum by its actual active image and retain
the complete supplied frame. This is only the existing parallel algebra. -/
theorem framed_image {Γ : Ctx sig} (world : World Γ 0)
    (head : Pattern) (image frame : List (Activity Γ))
    (represented : StructuralCongruence head (actual world image)) :
    StructuralCongruence
      (RhoScopedServers.parallel (head :: (headers world frame).map Header.pattern))
      (actual world (image ++ frame)) := by
  refine .trans _ (RhoScopedServers.parallel
    (actual world image :: (headers world frame).map Header.pattern)) _ ?_ ?_
  · apply StructuralCongruence.par_cong
      (head :: (headers world frame).map Header.pattern)
      (actual world image :: (headers world frame).map Header.pattern) rfl
    intro index leftBound rightBound
    cases index with
    | zero => exact represented
    | succ index => exact .refl _
  · simpa [actual, headers, HeaderInversion.parallel, List.map_append] using
      Context.par_flatten_head ((headers world image).map Header.pattern)
        ((headers world frame).map Header.pattern)

private theorem nil_par {Γ : Ctx sig} (process : Proc Γ) :
    StructuralEq (par nil process) process := .trans (.parComm _ _) (.parUnit _)

/-- The receiver consumes this exact fresh reply. Source restriction is
retained; the opened private name is not silently erased from the source. -/
theorem private_delivery_accounted {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name)
    (frame : List (Activity Γ)) :
    ∃ image : List (Activity (.nm :: Γ)),
      (∀ activity ∈ image, RhoUnaryImage.Initial activity) ∧
      StructuralEq (source (.privateScope body guarded :: .reply seed :: frame))
        (nu (source (image ++ frame.map (Activity.rename (fun _ name => Var.succ name))))) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (seedCode seed) ::
            (headers world.world frame).map Header.pattern))
        (actual (world.extendAt seed returned fresh).world
          (image ++ frame.map (Activity.rename (fun _ name => Var.succ name)))) ∧
      clientCount image = requestCount image ∧ total image = work body := by
  let nextWorld := world.extendAt seed returned fresh
  let after := compiled guarded nextWorld.world
  obtain ⟨image, initial, sourceImage, targetImage, balanced, credited⟩ := initial_image_accounted guarded nextWorld.world after
    (compiled_spec guarded _)
  refine ⟨image, initial, ?_, ?_, balanced, credited⟩
  · change StructuralEq (par (nu body) (par nil (source frame))) _
    refine .trans (.par (.refl _) (nil_par _)) ?_
    refine .trans (.nuPar _ _) (.nu ?_)
    refine .trans (q := par (source image)
      (source (frame.map (Activity.rename (fun _ name => Var.succ name))))) (.par sourceImage ?_) ?_
    · rw [source_rename]
      exact .refl _
    · exact source_append image _
  · have received : semanticCommSubst (ordinary guarded world.world).term (seedCode seed) = after.term := by
      simpa only [after, nextWorld, SeedWorld.extendAt_world] using private_received guarded world.world seed
    rw [received]
    have framed := framed_image nextWorld.world after.term image
      (frame.map (Activity.rename (fun _ name => Var.succ name))) targetImage
    rw [headers_extendAt] at framed
    exact framed


/-- Formation and pending balance retain the same accounted private delivery. -/
theorem private_delivery_balanced {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name)
    (frame : List (Activity Γ)) :
    ∃ image : List (Activity (.nm :: Γ)),
      (∀ activity ∈ image, Initial activity) ∧
      StructuralEq (source (.privateScope body guarded :: .reply seed :: frame))
        (nu (source (image ++ frame.map (Activity.rename (fun _ name => Var.succ name))))) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (seedCode seed) ::
            (headers world.world frame).map Header.pattern))
        (actual (world.extendAt seed returned fresh).world
          (image ++ frame.map (Activity.rename (fun _ name => Var.succ name)))) ∧
      clientCount image = requestCount image := by
  obtain ⟨image, initial, sourceEq, targetEq, balanced, _⟩ :=
    private_delivery_accounted guarded world seed returned fresh frame
  exact ⟨image, initial, sourceEq, targetEq, balanced⟩

theorem private_delivery {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : SeedWorld Γ) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name)
    (frame : List (Activity Γ)) :
    ∃ image : List (Activity (.nm :: Γ)),
      (∀ activity ∈ image, RhoUnaryImage.Initial activity) ∧
      StructuralEq (source (.privateScope body guarded :: .reply seed :: frame))
        (nu (source (image ++ frame.map (Activity.rename (fun _ name => Var.succ name))))) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (seedCode seed) ::
            (headers world.world frame).map Header.pattern))
        (actual (world.extendAt seed returned fresh).world
          (image ++ frame.map (Activity.rename (fun _ name => Var.succ name)))) := by
  obtain ⟨image, initial, sourceEq, targetEq, _⟩ :=
    private_delivery_balanced guarded world seed returned fresh frame
  exact ⟨image, initial, sourceEq, targetEq⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryDelivery
