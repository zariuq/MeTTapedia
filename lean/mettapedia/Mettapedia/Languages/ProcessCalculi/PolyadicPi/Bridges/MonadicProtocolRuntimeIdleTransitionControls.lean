import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeIdleTransition

/-!
# A real idle firing activates a guarded private tuple offer

The input guard allocates a private call channel only after receiving its
original unary datum. Its real lowered step and the original source step
admit a reconstructed runtime witness with no pending private debt.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleTransitionControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier NamePassingChannelRoles
open ActiveUnarySelectedBoundary

abbrev context : Ctx sig := [.nm, .nm]
def channel : Var context .nm := .zero
def datum : Var context .nm := .succ .zero
def roles : Roles context
  | .zero => .reference
  | .succ _ => .call
def body : Proc (.nm :: context) :=
  nu (out2 (.var .zero) (.var channel.succ.succ) (.var (.succ .zero)))
def frame : List (Proc context) := [out1 (.var channel) (.var datum), inp1 (.var channel) body]
def registry : Fin 0 → Slot context := Fin.elim0
def source : Proc context := registrySource registry (parallel frame)
def target : Proc context := registryTarget registry (parallel frame)

theorem body_guarded : Guarded body := .nu (.out2 _ _ _)
theorem body_typed : Typed (extendRole .call roles) body :=
  .nu .call (.out2 .zero channel.succ.succ (.succ .zero) rfl rfl rfl)
theorem frame_heads : ∀ atom ∈ frame, IdleFrame.Head atom := by
  intro atom member
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · subst atom; exact .output _ _
  · subst atom; exact .input1 _ body_guarded
theorem source_typed : Typed roles source :=
  .par (.nil roles) (.par (.out1 channel datum rfl rfl) (.par (.inp1 channel rfl body_typed) (.nil roles)))

def before : Witness source target where
  world := context
  scope := .nil
  n := 0
  registry := registry
  frame := frame
  heads := frame_heads
  live := fun owner => Fin.elim0 owner
  guards := fun owner => Fin.elim0 owner
  roles := roles
  typed := source_typed
  source := .refl _
  target := .refl _

def output : Fin before.frame.length := ⟨0, by decide⟩
def input : Fin before.frame.length := ⟨1, by decide⟩
def after : Proc context := par nil (par (inst (lower body) (.var datum)) nil)

/-- This is a primitive step of the actual lowered program, before any
new tuple's private communication is attempted. -/
theorem actual_guard_release : StepModulo target after := by
  change StepModulo (par nil (rename (ambient 0) (lower (parallel frame)))) after
  dsimp only [World, privatePrefix]
  have identity : (ambient (Γ := context) 0) = (fun _ name => name) := rfl
  rw [identity, rename_id]
  simp only [frame, parallel, lower_par, lower_nil, lower_out1, lower_inp1]
  exact ⟨par nil (par (par (out1 (.var channel) (.var datum)) (inp1 (.var channel) (lower body))) nil),
    after, .par (.refl _) (StructuralEq.parAssoc _ _ _).symm,
    .parR _ (.parL _ (.comm1 _ _ _)), .refl _⟩

theorem actual_endpoint : StructuralEq after
    (before.scope.close ((privateScope before.n).close
      (par (rename (ambient before.n) (lower (inst body (.var datum))))
        (registryTarget before.registry
          (parallel (RuntimeIdleUpdate.updatedFrame false before.frame output input)))))) := by
  dsimp only [before, Scope.close, privateScope, World, privatePrefix]
  have removed : RuntimeIdleUpdate.updatedFrame false frame output input = [] := rfl
  rw [removed]
  simp only [registryTarget, List.finRange_zero, List.map_nil, parallel, lower_nil]
  change StructuralEq (par nil (par (inst (lower body) (.var datum)) nil))
    (par (rename (fun _ name => name) (lower (inst body (.var datum)))) (par nil nil))
  rw [rename_id, RuntimeIdleUpdate.lower_inst_variable]
  exact (StructuralEq.parAssoc _ _ _).symm.trans
    ((StructuralEq.par (.parComm _ _) (.refl _)).trans (.parAssoc _ _ _))

theorem actual_source_target_witness :
    StepModulo target after ∧
      StepModulo source (RuntimeIdleTransition.sourceAfter before output input false body datum) ∧
      ∃ witness : Witness (RuntimeIdleTransition.sourceAfter before output input false body datum) after,
        witness.debt = 0 := by
  obtain ⟨sourceStep, witness, counted⟩ := RuntimeIdleTransition.updated before output input
    (by decide) false channel datum body rfl rfl actual_endpoint
  exact ⟨actual_guard_release, sourceStep, witness, counted⟩

theorem released_private_offer_is_not_nil : inst body (.var datum) ≠ nil := by
  intro same
  cases same

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleTransitionControls
