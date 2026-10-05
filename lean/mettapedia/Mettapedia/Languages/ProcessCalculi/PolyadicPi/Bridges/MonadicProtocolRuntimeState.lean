import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPublicReflection
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPrivateUpdate

/-!
# Offered, committed and released tuple occurrences

An offered occurrence retains its public subject and ordered fields. Its
callback position is unused until the actual selected receiver supplies its
guard. A committed occurrence retains both that original guard and its unary
lowering. Releasing the final field removes both private names from the actual
continuation. These are states of the existing authored protocol, not an
alternative transition relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeState

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open MonadicProtocol.Capabilities MonadicProtocol.Ownership ScopedActiveFrontier

def loweredCall {Γ : Ctx sig} (call : Call Γ) : Call Γ :=
  ⟨call.first, call.second, lower call.body⟩

theorem lowered_readback {Γ : Ctx sig} (call : Call Γ) :
    readback (loweredCall call) = lower (readback call) :=
  (lower_openPair call.body call.first call.second).symm

inductive Slot (Γ : Ctx sig) where
  | offered (channel : Name Γ) (first second : Name Γ)
  | pending (phase : Phase) (call : Call Γ)
  | released (call : Call Γ)

def Slot.source {Γ : Ctx sig} : Slot Γ → Proc Γ
  | .offered channel first second => out2 channel first second
  | .pending _ call | .released call => readback call

def Slot.template {Γ : Ctx sig} : Slot Γ → Proc (.nm :: .nm :: Γ)
  | .offered channel first second =>
      weaken (par (out1 (weaken channel) (.var .zero)) (sendFields first second))
  | .pending phase call => contents phase (loweredCall call)
  | .released call => weaken (weaken (lower (readback call)))

def Slot.remaining {Γ : Ctx sig} : Slot Γ → Nat
  | .offered _ _ _ | .released _ => 0
  | .pending phase _ => phase.remaining

def Slot.closed {Γ : Ctx sig} (slot : Slot Γ) : Proc Γ := nu (nu slot.template)

def Slot.placed {Γ : Ctx sig} (n : Nat) (owner : Fin n) (slot : Slot Γ) : Proc (World n Γ) :=
  rename (placement n owner) slot.template

/-- Reserving an unused callback position does not allocate a callback in
the runtime. The written sender is exactly the original one-session offer. -/
theorem offered_entry {Γ : Ctx sig} (channel first second : Name Γ) :
    StructuralEq (Slot.closed (.offered channel first second)) (sendPair channel first second) :=
  .nu (.nuUnused _)

theorem released_entry {Γ : Ctx sig} (call : Call Γ) :
    StructuralEq (Slot.closed (.released call)) (lower (readback call)) :=
  (StructuralEq.nu (.nuUnused _)).trans (.nuUnused _)

/-- Public receipt chooses the actual guard before creating private debt.
The supplied target is the new pending occurrence's real closed template. -/
theorem public_commitment {Γ : Ctx sig} (channel : Var Γ .nm) (call : Call Γ)
    {target : Proc Γ}
    (step : StepModulo (par (sendPair (.var channel) call.first call.second)
      (receivePair (.var channel) (lower call.body))) target) :
    Step (par (out2 (.var channel) call.first call.second) (inp2 (.var channel) call.body))
      (Slot.source (.pending .callback call)) ∧
    StructuralEq target (Slot.closed (.pending .callback call)) ∧
    Slot.remaining (.pending .callback call) = Slot.remaining (.offered (.var channel) call.first call.second) + 3 := by
  refine ⟨.comm2 _ _ _ _, ?_, rfl⟩
  exact PublicReflection.invocation_endpoint channel call.first call.second (lower call.body) step

def next {Γ : Ctx sig} (phase : Phase) (call : Call Γ) : Slot Γ :=
  match phase with
  | .callback => .pending .first call
  | .first => .pending .second call
  | .second => .released call

theorem source_unchanged {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    (next phase call).source = (Slot.pending phase call).source := by
  cases phase <;> rfl

theorem administrative_balance {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    (next phase call).remaining + 1 = (Slot.pending phase call).remaining := by
  cases phase <;> rfl

theorem next_template {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    (next phase call).template = nextContents phase (loweredCall call) := by
  cases phase with
  | callback | first => rfl
  | second =>
      simp only [next, Slot.template, nextContents]
      rw [lowered_readback]

/-- Every supplied raw private firing has the same retained source and an
actual next template. The final continuation is the lowering of the original
simultaneously opened source guard, with neither private name retained. -/
theorem placed_administrative {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (phase : Phase) (call : Call Γ) {target : Proc (World n Γ)}
    (step : Step ((Slot.pending phase call).placed n owner) target) :
    StructuralEq target ((next phase call).placed n owner) ∧
    (next phase call).source = (Slot.pending phase call).source ∧
    (next phase call).remaining + 1 = (Slot.pending phase call).remaining := by
  have endpoint := placed_actual_endpoint n owner phase (loweredCall call) step
  change StructuralEq target (rename (placement n owner) ((next phase call).template))
      ∧ _ ∧ _
  rw [next_template]
  exact ⟨endpoint, source_unchanged phase call, administrative_balance phase call⟩

theorem offered_source_no_private {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (port : Port) (channel first second : Name Γ) :
    countVar (key n owner port) (rename (ambient n) (Slot.source (.offered channel first second))) = 0 :=
  ambient_has_no_private n owner port _

theorem retained_source_no_private {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (port : Port) (phase : Phase) (call : Call Γ) :
    countVar (key n owner port) (rename (ambient n) (Slot.source (.pending phase call))) = 0 :=
  ambient_has_no_private n owner port _

theorem released_placed {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    (Slot.released call).placed n owner = rename (ambient n) (lower (readback call)) := by
  change rename (placement n owner) (weaken (weaken (lower (readback call)))) = _
  simp only [weaken, rename_comp]
  rfl

def privateScope {Γ : Ctx sig} : (n : Nat) → Scope Γ (World n Γ)
  | 0 => .nil
  | n + 1 => (privateScope n).append (.bind (.bind .nil))

private theorem inclusion_append : ∀ {Γ Δ Θ : Ctx sig} (first : Scope Γ Δ)
    (second : Scope Δ Θ) (sort : Srt) (name : Var Γ sort),
    (first.append second).inclusion sort name = second.inclusion sort (first.inclusion sort name)
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .bind rest, later, sort, name => inclusion_append rest later sort (.succ name)

theorem privateScope_inclusion {Γ : Ctx sig} (n : Nat) :
    (privateScope (Γ := Γ) n).inclusion = ambient n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext sort name
      rw [privateScope, inclusion_append, ih]
      rfl

def registrySource {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ) : Proc Γ :=
  par (parallel ((List.finRange n).map (fun owner => (registry owner).source))) frame

def registryTarget {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ) : Proc (World n Γ) :=
  par (parallel ((List.finRange n).map (fun owner => (registry owner).placed n owner)))
    (rename (ambient n) (lower frame))

def registryRemaining {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) : Nat :=
  ((List.finRange n).map (fun owner => (registry owner).remaining)).sum

theorem placed_extend {Γ : Ctx sig} (n : Nat) (owner : Fin n) (slot : Slot Γ) :
    slot.placed (n + 1) owner.succ = weaken (weaken (slot.placed n owner)) :=
  placement_term_extend n owner slot.template

theorem source_private_closing {Γ : Ctx sig} (n : Nat) (source : Proc Γ) :
    StructuralEq ((privateScope n).close (rename (ambient n) source)) source := by
  induction n with
  | zero =>
      change StructuralEq (rename (fun _ name => name) source) source
      rw [rename_id]
      exact .refl _
  | succ n ih =>
      rw [privateScope, Scope.close_append]
      change StructuralEq ((privateScope n).close
        (nu (nu (rename (ambient (n + 1)) source)))) source
      have same : rename (ambient (n + 1)) source = weaken (weaken (rename (ambient n) source)) := by
        simp only [weaken, rename_comp]
        rfl
      dsimp only [World, privatePrefix] at same ⊢
      rw [same]
      exact ((privateScope n).congr ((StructuralEq.nu (.nuUnused _)).trans (.nuUnused _))).trans ih

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeState
