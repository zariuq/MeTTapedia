import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryDelivery
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPairInversion

/-!
# Public core-rho receipt commits the exact source pi communication

The reflected source step happens at public receipt. Persistent-code rearm
does not delay that commitment. The supplied continuation, arbitrary active
frame, private scopes inside the released body and duplicate frame
occurrences are retained in the concrete target image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCommitment

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryWorld RhoUnaryActive
open RhoUnaryImage RhoUnaryPhase RhoUnaryDelivery RhoUnaryCredit
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-- The exact ordinary core contractum corresponds to one real source
COMM and the compiler's own active continuation image. -/
theorem ordinary_commitment_exact {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.input channel body guarded :: .output channel datum :: frame))
        (source (image ++ frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world (image ++ frame)) ∧
      clientCount image = requestCount image ∧ total image = work (inst body (.var datum)) ∧
      StructuralEq (source (image ++ frame)) (par (inst body (.var datum)) (source frame)) := by
  let opened := inst body (.var datum)
  let openedGuarded := inst_guarded guarded datum
  let after := compiled openedGuarded world.world
  obtain ⟨image, initial, sourceImage, targetImage, balanced, credited⟩ := initial_image_accounted openedGuarded world.world after
    (compiled_spec openedGuarded _)
  refine ⟨image, initial, ?_, ?_, balanced, credited, ?_⟩
  · let frontier : ScopedActiveFrontier.Frontier Γ :=
      ⟨Γ, .nil, (Activity.input channel body guarded).source ::
        (Activity.output channel datum).source :: frame.map Activity.source⟩
    obtain ⟨redex, endpoint, before, firing, afterSource⟩ :=
      frontier.unary_pair (.var channel) (.var datum) body (frame.map Activity.source)
        (List.Perm.swap _ _ _)
    refine ⟨redex, endpoint, before, firing, .trans afterSource ?_⟩
    exact .trans (.par sourceImage (.refl _)) (source_append image frame)
  · rw [ordinary_received guarded world datum]
    exact framed_image world.world after.term image frame targetImage
  · exact .trans (.symm (source_append image frame)) (.par (.symm sourceImage) (.refl _))

private theorem nil_par {Γ : Ctx sig} (process : Proc Γ) :
    StructuralEq (par nil process) process := .trans (.parComm _ _) (.parUnit _)

/-- The public receipt of a persistent request advances the source now and
keeps its original server in the rearm phase at the supplied rho endpoint. -/
theorem persistent_commitment_exact {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (self : Nat) (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.ready channel body guarded self :: .output channel datum :: frame))
        (source (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world
          (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) ∧
      clientCount image = requestCount image ∧ total image = work (inst body (.var datum)) ∧
      StructuralEq (source (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame))
        (par (inst body (.var datum)) (par (rep (inp1 (.var channel) body)) (source frame))) := by
  let openedGuarded := inst_guarded guarded datum
  let after := compiled openedGuarded world.world
  obtain ⟨image, initial, sourceImage, targetImage, balanced, credited⟩ := initial_image_accounted openedGuarded world.world after
    (compiled_spec openedGuarded _)
  let stage := Activity.sendCode channel body guarded self :: Activity.rearm channel body guarded self :: frame
  refine ⟨image, initial, ?_, ?_, balanced, credited, ?_⟩
  · let frontier : ScopedActiveFrontier.Frontier Γ :=
      ⟨Γ, .nil, (Activity.ready channel body guarded self).source ::
        (Activity.output channel datum).source :: frame.map Activity.source⟩
    obtain ⟨redex, endpoint, before, firing, afterSource⟩ :=
      frontier.unary_server (.var channel) (.var datum) body (frame.map Activity.source)
        (List.Perm.swap _ _ _)
    refine ⟨redex, endpoint, before, firing, .trans afterSource ?_⟩
    refine .trans (q := par (source image) (source stage)) (.par sourceImage ?_) (source_append image stage)
    exact .symm (nil_par _)
  · rw [persistent_received channel guarded world self datum]
    refine .trans _ _ _ (Context.par_flatten_head _ _) ?_
    refine .trans _ _ _ ?_ (framed_image world.world after.term image stage targetImage)
    apply StructuralCongruence.par_perm
    exact (List.perm_append_comm
      (l₁ := [(Activity.sendCode channel body guarded self).header world.world |>.pattern,
        (Activity.rearm channel body guarded self).header world.world |>.pattern])
      (l₂ := [after.term])).append_right ((headers world.world frame).map Header.pattern)
  · exact .trans (.symm (source_append image stage)) (.par (.symm sourceImage) (nil_par _))

/-- Dropping the source endpoint equation projects the same public receipt
and its exact activation account. -/
theorem ordinary_commitment_accounted {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.input channel body guarded :: .output channel datum :: frame))
        (source (image ++ frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world (image ++ frame)) ∧
      clientCount image = requestCount image ∧ total image = work (inst body (.var datum)) := by
  obtain ⟨image, initial, step, equation, balanced, credited, _⟩ :=
    ordinary_commitment_exact channel datum guarded world frame
  exact ⟨image, initial, step, equation, balanced, credited⟩

theorem persistent_commitment_accounted {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (self : Nat) (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.ready channel body guarded self :: .output channel datum :: frame))
        (source (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world
          (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) ∧
      clientCount image = requestCount image ∧ total image = work (inst body (.var datum)) := by
  obtain ⟨image, initial, step, equation, balanced, credited, _⟩ :=
    persistent_commitment_exact channel datum guarded world self frame
  exact ⟨image, initial, step, equation, balanced, credited⟩


/-- The unchanged source/target/balance API is the projection of the same
accounted communication construction. -/
theorem ordinary_commitment_balanced {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.input channel body guarded :: .output channel datum :: frame))
        (source (image ++ frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world (image ++ frame)) ∧
      clientCount image = requestCount image := by
  obtain ⟨image, initial, sourceStep, targetEq, balanced, _⟩ :=
    ordinary_commitment_accounted channel datum guarded world frame
  exact ⟨image, initial, sourceStep, targetEq, balanced⟩

theorem persistent_commitment_balanced {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (self : Nat) (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.ready channel body guarded self :: .output channel datum :: frame))
        (source (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world
          (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) ∧
      clientCount image = requestCount image := by
  obtain ⟨image, initial, sourceStep, targetEq, balanced, _⟩ :=
    persistent_commitment_accounted channel datum guarded world self frame
  exact ⟨image, initial, sourceStep, targetEq, balanced⟩

theorem ordinary_commitment {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.input channel body guarded :: .output channel datum :: frame))
        (source (image ++ frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world (image ++ frame)) := by
  obtain ⟨image, initial, sourceStep, targetEq, _⟩ :=
    ordinary_commitment_balanced channel datum guarded world frame
  exact ⟨image, initial, sourceStep, targetEq⟩

theorem persistent_commitment {Γ : Ctx sig} (channel datum : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : SeedWorld Γ)
    (self : Nat) (frame : List (Activity Γ)) :
    ∃ image : List (Activity Γ),
      (∀ activity ∈ image, Initial activity) ∧
      StepModulo (source (.ready channel body guarded self :: .output channel datum :: frame))
        (source (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload ::
            (headers world.world frame).map Header.pattern))
        (actual world.world
          (image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)) := by
  obtain ⟨image, initial, sourceStep, targetEq, _⟩ :=
    persistent_commitment_balanced channel datum guarded world self frame
  exact ⟨image, initial, sourceStep, targetEq⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCommitment
