import Mettapedia.Languages.LambdaCalculus.NamePassingReturningLambda

/-!
# Returned-function observation for name-passing environments

A function is returned when the active expression is a lambda, possibly
under retained definitions and one-shot declarations. Pending application
and unresolved reference requests are different observations. The existing
source application equations preserve this readout.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing.Environment

variable {Srt : Type} {nm : Srt}

def returning : {Γ : List Srt} → Expr nm Γ → Bool
  | _, .var _ | _, .app _ _ => false
  | _, .lam _ => true
  | _, .defn _ body => returning body
  | _, .carrier _ _ body => returning body

theorem returning_iff {Γ : List Srt} (term : Expr nm Γ) :
    returning term = true ↔ Nonempty (ReturningLambda term) := by
  induction term with
  | var =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨returned⟩; cases returned
  | lam body => exact ⟨fun _ => ⟨.lam body⟩, fun _ => rfl⟩
  | app =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨returned⟩; cases returned
  | defn value body _ bodyIH =>
      change returning body = true ↔ Nonempty (ReturningLambda (.defn value body))
      rw [bodyIH]
      constructor
      · rintro ⟨returned⟩; exact ⟨.defn value returned⟩
      · rintro ⟨returned⟩; cases returned with | defn _ inner => exact ⟨inner⟩
  | carrier name value body _ bodyIH =>
      change returning body = true ↔ Nonempty (ReturningLambda (.carrier name value body))
      rw [bodyIH]
      constructor
      · rintro ⟨returned⟩; exact ⟨.carrier name value returned⟩
      · rintro ⟨returned⟩; cases returned with | carrier _ _ inner => exact ⟨inner⟩

theorem returning_structural {Γ : List Srt} {first second : Expr nm Γ}
    (equal : Environment.StructuralEq first second) : returning first = returning second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | appDefinition | appCarrier | lam | app => rfl
  | defn _ _ _ bodyIH => exact bodyIH
  | carrier _ _ _ _ bodyIH => exact bodyIH

end Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation
