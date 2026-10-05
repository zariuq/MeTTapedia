import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatCommunicationExposure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveScopeTransport

/-!
# Removing unused scopes keeps the supplied communication's actor origins

The partial inverse reconstructs the actual redex and frame. Their constructor
marks therefore strengthen unchanged. Stripping each unused private binder uses
the real unused-scope equation, preserving the selected prefix identities even
when unrelated replicated servers and identical one-shot guards are present.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatMarkedCommunicationExposure

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ScopedActiveFrontier ScopedCommunicationInversion ActiveHeaderInvariant

universe u

/-- The telescope's own marked binder is removed together with its actual
unused physical name; marks within the guarded body remain unchanged. -/
theorem strip_unused {Label : Type u} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Label scope) (marked : ActiveMarking.Tree Label) (process : Proc Γ) :
    Transport (binders.close marked) (scope.close (rename scope.inclusion process)) marked process := by
  induction binders with
  | nil => simp only [Scope.close, Scope.inclusion, ScopeMarks.close, rename_id]; exact .refl _ _
  | @bind Γ Δ rest origin binders ih =>
      change Transport (.nu origin (binders.close marked))
        (nu (rest.close (rename (fun sort name => rest.inclusion sort (.succ name)) process))) marked process
      rw [← rename_comp (fun _ name => (Var.succ name : Var (Srt.nm :: Γ) _)) rest.inclusion process]
      exact .trans (.nu origin (ih (weaken process))) (.nuUnused origin marked process)

theorem communication_fits {Label : Type u} {Γ : Ctx sig} {redex reduct : Proc Γ}
    {selected : Communication redex reduct} {marked : ActiveMarking.Tree Label}
    (chosen : MarkedCommunication selected marked) : Fits marked redex := by
  cases chosen with
  | unary channel datum body output input continuation fitted =>
      exact .par (.out1 output channel datum) (.inp1 input channel fitted)
  | binary channel first second body output input continuation fitted =>
      exact .par (.out2 output channel first second) (.inp2 input channel fitted)

/-- Communication origins are determined by the same actual constructor
marking, independently of the physical world in which its names are written. -/
theorem same_marks {Label : Type u} {Γ Δ : Ctx sig} {redex reduct : Proc Γ}
    {otherRedex otherReduct : Proc Δ} {selected : Communication redex reduct}
    {otherSelected : Communication otherRedex otherReduct} {marked : ActiveMarking.Tree Label}
    (first : MarkedCommunication selected marked) (second : MarkedCommunication otherSelected marked) :
    first.inputOrigin = second.inputOrigin ∧ first.outputOrigin = second.outputOrigin ∧
      inputHeader selected = inputHeader otherSelected ∧ outputHeader selected = outputHeader otherSelected := by
  cases first <;> cases second <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The supplied trace is strengthened together with the actual redex and
frame. No new tracing choice can replace one equal listener by another. -/
theorem without_unused_scope_traced {Label : Type u} {Γ : Ctx sig}
    {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {actual : Exposure source target} (traced : TracedExposure original actual)
    (unused : ScopedOpening.Vacuous source) :
    ∃ (redex reduct frame : Proc Γ) (chosen : Communication redex reduct)
      (before : StructuralEq source (par redex frame)) (after : StructuralEq (par reduct frame) target)
      (flat : TracedExposure original (FlatCommunicationExposure.unscoped redex reduct frame chosen before after)),
      flat.continuation.inputOrigin = traced.continuation.inputOrigin ∧
        flat.continuation.outputOrigin = traced.continuation.outputOrigin ∧
        inputHeader chosen = inputHeader actual.selected := by
  obtain ⟨redex, reduct, frame, chosen, before, after, arity, redexImage, reductImage, frameImage⟩ :=
    FlatCommunicationExposure.without_unused_scope_image actual unused
  have redexFits : Fits traced.redexMarks redex := by
    apply Fits.ofRename actual.scope.inclusion redex
    rw [redexImage]
    exact communication_fits traced.continuation
  have frameFits : Fits traced.frameMarks frame := by
    apply Fits.ofRename actual.scope.inclusion frame
    rw [frameImage]
    exact traced.frameFits
  obtain ⟨continuation⟩ := markedCommunication_exists chosen redexFits
  have origins := same_marks continuation traced.continuation
  have stripped := strip_unused traced.binders (.par traced.redexMarks traced.frameMarks) (par redex frame)
  rw [rename_par, redexImage, frameImage] at stripped
  let flat : TracedExposure original (FlatCommunicationExposure.unscoped redex reduct frame chosen before after) :=
    { binders := .nil
      redexMarks := traced.redexMarks
      frameMarks := traced.frameMarks
      continuation := continuation
      frameFits := frameFits
      transportedFits := .par redexFits frameFits
      transport := .trans traced.transport stripped
      originalInput := by
        change Selection (inputHeader chosen) continuation.inputOrigin original
        rw [origins.2.2.1, origins.1]
        exact traced.originalInput
      originalOutput := by
        change Selection (outputHeader chosen) continuation.outputOrigin original
        rw [origins.2.2.2, origins.2.1]
        exact traced.originalOutput }
  exact ⟨redex, reduct, frame, chosen, before, after, flat, origins.1, origins.2.1, arity⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.FlatMarkedCommunicationExposure
