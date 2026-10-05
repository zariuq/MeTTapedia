import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPhase

/-!
# Inverting actual unary compiler frontiers by their communication roles

Every actual core firing selects original input and output occurrences.
Namespace separation then determines whether it is a user communication,
private-name delivery, persistent rearming, or an allocator phase. The
rearming case retains both handler templates until a separate owner
coherence proof identifies them; equal channels alone cannot do that.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPairInversion

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryRoles
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-- This is a classification of already supplied actual selections; it is
not a transition relation for the guest or the implementation. -/
inductive Pair {Γ : Ctx sig} : Activity Γ → Activity Γ → Prop where
  | ordinary (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body) :
      Pair (.input channel body guarded) (.output channel datum)
  | persistent (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ))
      (guarded : GuardedUnary body) (self : Nat) :
      Pair (.ready channel body guarded self) (.output channel datum)
  | privateScope (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body) (seed : Nat) :
      Pair (.privateScope body guarded) (.reply seed)
  | install (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
      (guarded : GuardedUnary body) (seed : Nat) :
      Pair (.install channel body guarded) (.reply seed)
  | rearm (channel suppliedChannel : Var Γ .nm)
      (body suppliedBody : Proc (.nm :: Γ))
      (guarded : GuardedUnary body) (suppliedGuarded : GuardedUnary suppliedBody) (self : Nat) :
      Pair (.rearm channel body guarded self) (.sendCode suppliedChannel suppliedBody suppliedGuarded self)
  | allocatorRequest : Pair (.allocatorReady : Activity Γ) .request
  | allocatorRearm : Pair (.allocatorRearm : Activity Γ) .allocatorSendCode
  | token (seed : Nat) : Pair (.seedInput : Activity Γ) (.token seed)

theorem pair_of_headers {Γ : Ctx sig} (world : SeedWorld Γ) (input output : Activity Γ)
    {inputChannel body outputChannel payload : Pattern}
    (inputEq : input.header world.world = .input inputChannel body)
    (outputEq : output.header world.world = .output outputChannel payload)
    (ports : input.port = output.port) : Pair input output := by
  cases input <;> cases output <;>
    simp_all [Activity.header, Activity.port]
  all_goals constructor

/-- A supplied selected pair is one of the concrete compiler phases.
Multiplicity and both original positions are retained by Selection. -/
theorem selected_pair {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ))
    (fresh : ∀ activity ∈ activities, activity.port.Fresh world)
    (selected : Selection (headers world.world activities)) :
    Pair (activities[selected.inputIndex]'(by simpa [headers] using selected.inputBound))
      ((activities.eraseIdx selected.inputIndex)[selected.outputIndex]'
        (by simpa [headers, List.eraseIdx_map] using selected.outputBound)) := by
  apply pair_of_headers world
  · simpa [headers] using selected.inputEq
  · simpa [headers, List.eraseIdx_map] using selected.outputEq
  · exact selected_port_eq world activities fresh selected

/-- Arbitrary authored firing at an active image is classified from the
real matcher. The literal supplied endpoint is the original substitution
and untouched residual occurrences. -/
theorem pair_of_step {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ))
    (fresh : ∀ activity ∈ activities, activity.port.Fresh world)
    {fuel : Nat} {target : Pattern} (step : RhoStepAt fuel (actual world.world activities) target) :
    ∃ selected : Selection (headers world.world activities),
      target = selected.contractum ∧
      Pair (activities[selected.inputIndex]'(by simpa [headers] using selected.inputBound))
        ((activities.eraseIdx selected.inputIndex)[selected.outputIndex]'
          (by simpa [headers, List.eraseIdx_map] using selected.outputBound)) := by
  obtain ⟨selected, endpoint⟩ := selection_of_step (headers_typed world.world activities) step
  exact ⟨selected, endpoint, selected_pair world activities fresh selected⟩

/-- Sorting the actual frontier also preserves the classification of its
original selected occurrences and the canonical supplied endpoint. -/
theorem pair_of_canonical_step {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ))
    (fresh : ∀ activity ∈ activities, activity.port.Fresh world)
    {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (canonicalParallel (headers world.world activities)) target) :
    ∃ selected : Selection (headers world.world activities),
      Canonical.canonicalize target = Canonical.canonicalize selected.contractum ∧
      Pair (activities[selected.inputIndex]'(by simpa [headers] using selected.inputBound))
        ((activities.eraseIdx selected.inputIndex)[selected.outputIndex]'
          (by simpa [headers, List.eraseIdx_map] using selected.outputBound)) := by
  obtain ⟨selected, endpoint⟩ := canonical_selection_of_step
    (headers_typed world.world activities) (headers_safe world.world activities) step
  exact ⟨selected, endpoint, selected_pair world activities fresh selected⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPairInversion
