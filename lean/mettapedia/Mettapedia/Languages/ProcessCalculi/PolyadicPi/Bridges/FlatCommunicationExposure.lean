import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolScopeReflection

/-!
# Exact communication exposure after removing unused private scopes

A source without used active restrictions may still be rearranged through
unused scopes before its firing. The existing partial inverse reconstructs
that same primitive communication and its actual residual in the original
context. Closing its unchanged private telescope gives the supplied endpoint
by the actual unused-scope equation, including scopes activated in a newly
released continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatCommunicationExposure

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ScopedActiveFrontier ScopedCommunicationInversion ActiveHeaderInvariant
open MonadicProtocol.ScopeReflection

/-- The actual partial inverse to a private telescope's inclusion. -/
def inverse : {Γ Δ : Ctx sig} → (scope : Scope Γ Δ) → Strengthener scope.inclusion
  | _, _, .nil =>
      { un := fun _ name => some name
        un_rho := fun _ _ => rfl
        rho_un := by intro sort name old found; exact Option.some.inj found.symm }
  | _, _, .bind rest =>
      { un := fun sort name => (inverse rest).un sort name >>= (Strengthener.ofWeaken sig Srt.nm).un sort
        un_rho := by
          intro sort name
          change ((inverse rest).un sort (rest.inclusion sort (.succ name))).bind _ = some name
          rw [(inverse rest).un_rho]
          rfl
        rho_un := by
          intro sort name old found
          cases recognized : (inverse rest).un sort name with
          | none => simp [recognized] at found
          | some middle =>
              simp only [recognized] at found
              have first := (Strengthener.ofWeaken sig Srt.nm).rho_un sort middle old found
              have second := (inverse rest).rho_un sort name middle recognized
              change rest.inclusion sort (.succ old) = name
              exact (congrArg (rest.inclusion sort) first).trans second }

/-- Introducing only unused private binders is the existing structural
identity at every supplied process, including newly active restrictions. -/
theorem close_inclusion : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (process : Proc Γ),
    StructuralEq (scope.close (rename scope.inclusion process)) process
  | _, _, .nil, process => by
      simp only [Scope.close, Scope.inclusion, rename_id]
      exact .refl _
  | Γ, _, .bind rest, process => by
      change StructuralEq (nu (rest.close (rename (fun sort name => rest.inclusion sort (.succ name)) process))) process
      rw [← rename_comp (fun _ name => (Var.succ name : Var (Srt.nm :: Γ) _)) rest.inclusion process]
      exact (StructuralEq.nu (close_inclusion rest (weaken (t := Srt.nm) process))).trans (.nuUnused process)

/-- The selected actual communication is strengthened with its own supplied
subjects, fields and continuation. Its result renames back exactly. -/
theorem communication_strengthened {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) {redex reduct : Proc Δ}
    (chosen : Communication redex reduct) {oldRedex : Proc Γ}
    (found : strengthenT inverse redex = some oldRedex) :
    ∃ (oldReduct : Proc Γ) (oldChosen : Communication oldRedex oldReduct),
      inputHeader oldChosen = inputHeader chosen ∧ rename environment oldReduct = reduct := by
  cases chosen with
  | unary channel datum body =>
      obtain ⟨oldOutput, oldInput, outputFound, inputFound, rfl⟩ := par_found inverse _ _ found
      obtain ⟨oldChannel, oldDatum, channelFound, datumFound, rfl⟩ := out1_found inverse _ _ outputFound
      obtain ⟨inputChannel, oldBody, inputChannelFound, bodyFound, rfl⟩ := inp1_found inverse _ _ inputFound
      have subjects : inputChannel = oldChannel := Option.some.inj (inputChannelFound.symm.trans channelFound)
      subst inputChannel
      refine ⟨inst oldBody oldDatum, .unary oldChannel oldDatum oldBody, rfl, ?_⟩
      rw [rename_inst, rename_strengthenT (inverse.liftS [.nm]) _ _ bodyFound,
        rename_strengthenT inverse _ _ datumFound]
  | binary channel first second body =>
      obtain ⟨oldOutput, oldInput, outputFound, inputFound, rfl⟩ := par_found inverse _ _ found
      obtain ⟨oldChannel, oldFirst, oldSecond, channelFound, firstFound, secondFound, rfl⟩ :=
        out2_found inverse _ _ _ outputFound
      obtain ⟨inputChannel, oldBody, inputChannelFound, bodyFound, rfl⟩ := inp2_found inverse _ _ inputFound
      have subjects : inputChannel = oldChannel := Option.some.inj (inputChannelFound.symm.trans channelFound)
      subst inputChannel
      refine ⟨openPair oldBody oldFirst oldSecond, .binary oldChannel oldFirst oldSecond oldBody, rfl, ?_⟩
      rw [rename_openPair, rename_strengthenT (inverse.liftS [.nm, .nm]) _ _ bodyFound,
        rename_strengthenT inverse _ _ firstFound, rename_strengthenT inverse _ _ secondFound]

/-- Every supplied exposure of a source with only unused active scopes has a
real primitive COMM and exact frame in that source's original context. -/
theorem without_unused_scope_image {Γ : Ctx sig} {source target : Proc Γ}
    (exposure : Exposure source target) (unused : ScopedOpening.Vacuous source) :
    ∃ (redex reduct frame : Proc Γ) (chosen : Communication redex reduct),
      StructuralEq source (par redex frame) ∧ StructuralEq (par reduct frame) target ∧
        inputHeader chosen = inputHeader exposure.selected ∧
        rename exposure.scope.inclusion redex = exposure.redex ∧
        rename exposure.scope.inclusion reduct = exposure.reduct ∧
        rename exposure.scope.inclusion frame = exposure.frame := by
  have scopedUnused : ScopedOpening.Vacuous (exposure.scope.close (par exposure.redex exposure.frame)) :=
    (ScopedOpening.vacuous_structural exposure.before).mp unused
  obtain ⟨original, originalImage, _, closedOriginal⟩ :=
    ScopedOpening.vacuous_scope_strengthening exposure.scope (par exposure.redex exposure.frame) scopedUnused
  let recognizer := inverse exposure.scope
  have originalFound : strengthenT recognizer (par exposure.redex exposure.frame) = some original := by
    rw [originalImage]
    exact strengthenT_rename recognizer original
  obtain ⟨oldRedex, oldFrame, redexFound, frameFound, originalEqual⟩ :=
    par_found recognizer _ _ originalFound
  obtain ⟨oldReduct, chosen, arity, reductImage⟩ :=
    communication_strengthened recognizer exposure.selected redexFound
  have frameImage := rename_strengthenT recognizer exposure.frame oldFrame frameFound
  have targetImage : rename exposure.scope.inclusion (par oldReduct oldFrame) =
      par exposure.reduct exposure.frame := by
    rw [rename_par, reductImage, frameImage]
  have closedTarget : StructuralEq (exposure.scope.close (par exposure.reduct exposure.frame))
      (par oldReduct oldFrame) := by
    rw [← targetImage]
    exact close_inclusion exposure.scope _
  refine ⟨oldRedex, oldReduct, oldFrame, chosen, ?_, closedTarget.symm.trans exposure.after,
    arity, rename_strengthenT recognizer exposure.redex oldRedex redexFound,
    reductImage, frameImage⟩
  rw [← originalEqual]
  exact exposure.before.trans closedOriginal

/-- The same extraction with only its operational endpoint and arity receipt. -/
theorem without_unused_scope {Γ : Ctx sig} {source target : Proc Γ}
    (exposure : Exposure source target) (unused : ScopedOpening.Vacuous source) :
    ∃ (redex reduct frame : Proc Γ) (chosen : Communication redex reduct),
      StructuralEq source (par redex frame) ∧ StructuralEq (par reduct frame) target ∧
        inputHeader chosen = inputHeader exposure.selected := by
  obtain ⟨redex, reduct, frame, chosen, before, after, arity, _⟩ :=
    without_unused_scope_image exposure unused
  exact ⟨redex, reduct, frame, chosen, before, after, arity⟩

/-- The extracted primitive data is an actual exposure whose world is
literally the original context and whose private telescope is empty. -/
def unscoped {Γ : Ctx sig} {source target : Proc Γ} (redex reduct frame : Proc Γ)
    (chosen : Communication redex reduct) (before : StructuralEq source (par redex frame))
    (after : StructuralEq (par reduct frame) target) : Exposure source target where
  world := Γ
  scope := .nil
  redex := redex
  reduct := reduct
  selected := chosen
  frame := frame
  before := before
  after := after

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatCommunicationExposure
