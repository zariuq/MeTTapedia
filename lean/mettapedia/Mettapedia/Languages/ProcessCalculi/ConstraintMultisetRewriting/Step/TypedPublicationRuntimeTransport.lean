import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCodes
import Mettapedia.Machines.Cursor.QueryCore

/-!
# Retained typed code as a provider for adaptive runtime clients

A retained code/environment pair accepts the current refinement on each
request. Composing environments before readout preserves complete typed replies
and adaptive read histories. The provider does not freeze a live binding frame
or retype erased raw syntax under an unrelated type.

This is an optional typed-service adapter. It imposes no dependent-type service
or per-operation certificate on ordinary untyped execution. Native syntax,
frame-generation and owner-lifetime representations remain separate adapters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open Mettapedia.Machines

namespace RuntimeTransport

variable {Head : Type} {rules : Rules Head} {Γ Δ Θ : Context rules}

structure Request (environment : Δ ⟶ Γ) (target : Context rules) where
  code : Code Γ
  refinement : target ⟶ Δ
  licensed : (code.reindex environment).At refinement

/-- Direct reading composes the present refinement with the saved environment. -/
def direct (environment : Δ ⟶ Γ) (request : Request environment Θ) : TotalTerm Θ :=
  request.code.readout (request.refinement ≫ environment)
    ((request.code.at_reindex_iff environment request.refinement).mp request.licensed)

/-- The implementation retains typed code and applies the present refinement. -/
def retained (environment : Δ ⟶ Γ) (request : Request environment Θ) : TotalTerm Θ :=
  (request.code.reindex environment).readout request.refinement request.licensed

theorem replies_exact (environment : Δ ⟶ Γ) (request : Request environment Θ) :
    retained environment request = direct environment request :=
  request.code.readout_reindex environment request.refinement request.licensed

/-- Subsequent requests may choose different refinements after prior replies.
The complete finite reply history and final result are preserved. -/
theorem adaptive_client_exact (environment : Δ ⟶ Γ) {Answer : Type}
    (program : ReadOnlyQuery.Program (Request environment Θ) (TotalTerm Θ) Answer) :
    ReadOnlyQuery.run (retained environment) program =
      ReadOnlyQuery.run (direct environment) program := by
  have providers : (retained environment : Request environment Θ → TotalTerm Θ) =
      direct environment := funext (replies_exact environment)
  rw [providers]

/-- Bounded demand preserves the paid account, ordered reads and suspended
reply-indexed continuation as well as completed results. -/
def cursorBridge (environment : Δ ⟶ Γ) (target : Context rules) :
    Cursor.Hom
      (Cursor.ReadOnlyQuery.provider (retained (Θ := target) environment))
      (Cursor.ReadOnlyQuery.provider (direct (Θ := target) environment)) where
  map reads := reads
  step reads request := by
    simp only [Cursor.ReadOnlyQuery.provider]
    rw [replies_exact environment request]

theorem bounded_client_exact (environment : Δ ⟶ Γ) {Answer : Type}
    (price : Request environment Θ → Nat) (fuel : Nat)
    (program : ReadOnlyQuery.Program (Request environment Θ) (TotalTerm Θ) Answer)
    (reads : ReadOnlyQuery.Reads (Request environment Θ) (TotalTerm Θ)) :
    let result := Cursor.ReadOnlyQuery.Sampled.fixedAdvance (retained environment) price fuel program reads
    (result.1, (cursorBridge environment Θ).outcome Cursor.ReadOnlyQuery.client result.2) =
      Cursor.ReadOnlyQuery.Sampled.fixedAdvance (direct environment) price fuel program reads :=
  (cursorBridge environment Θ).advance_account Cursor.ReadOnlyQuery.client
    (Cursor.ReadOnlyQuery.Sampled.fixedCharge (retained environment) price)
    (Cursor.ReadOnlyQuery.Sampled.fixedCharge (direct environment) price)
    (fun _ _ => rfl) fuel ⟨PUnit.unit, program, reads⟩

/-- A second refinement transports the already checked typed result. This
licenses composition, not an arbitrary new type judgment on its raw code. -/
theorem typed_result_transport (environment : Δ ⟶ Γ) (request : Request environment Δ)
    (later : Θ ⟶ Δ) :
    (retained environment request).reindex later =
      request.code.readout (later ≫ request.refinement ≫ environment)
        (request.code.at_precompose
          ((request.code.at_reindex_iff environment request.refinement).mp request.licensed) later) := by
  rw [replies_exact]
  exact request.code.readout_precompose (request.refinement ≫ environment) later _

end RuntimeTransport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication
