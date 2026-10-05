import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

/-!
# Scope extrusion transports the actual actor marks in both directions

The private telescope moves the same marked body and the same external frame
into one world. Neither direction copies, discards or reassigns their active
prefix origins. These are constructor refinements of the existing scope
equations, independent of any source compiler or execution authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveScopeTransport

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ScopedActiveFrontier

universe u

theorem congr {Label : Type u} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Label scope) {first second : Proc Δ}
    {left right : ActiveMarking.Tree Label} (inside : Transport left first right second) :
    Transport (binders.close left) (scope.close first) (binders.close right) (scope.close second) := by
  induction binders with
  | nil => exact inside
  | bind origin rest ih => exact .nu origin (ih inside)

theorem par_forward {Label : Type u} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Label scope) (body : Proc Δ) (frame : Proc Γ)
    (bodyMarks frameMarks : ActiveMarking.Tree Label) :
    Transport (.par (binders.close bodyMarks) frameMarks) (par (scope.close body) frame)
      (binders.close (.par bodyMarks frameMarks))
      (scope.close (par body (rename scope.inclusion frame))) := by
  induction binders with
  | nil => simp only [ScopeMarks.close, Scope.close, Scope.inclusion, rename_id]; exact .refl _ _
  | @bind Γ Δ rest origin binders ih =>
      apply Transport.trans (Transport.nuPar origin (binders.close bodyMarks) frameMarks _ frame)
      apply Transport.nu origin
      simpa only [ScopeMarks.close, Scope.close, weaken, rename_comp, Scope.inclusion] using
        ih body (weaken frame)

theorem par_backward {Label : Type u} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Label scope) (body : Proc Δ) (frame : Proc Γ)
    (bodyMarks frameMarks : ActiveMarking.Tree Label) :
    Transport (binders.close (.par bodyMarks frameMarks))
      (scope.close (par body (rename scope.inclusion frame)))
      (.par (binders.close bodyMarks) frameMarks) (par (scope.close body) frame) := by
  induction binders with
  | nil => simp only [ScopeMarks.close, Scope.close, Scope.inclusion, rename_id]; exact .refl _ _
  | @bind Γ Δ rest origin binders ih =>
      apply Transport.trans _ (Transport.nuParBack origin (binders.close bodyMarks) frameMarks _ frame)
      apply Transport.nu origin
      simpa only [ScopeMarks.close, Scope.close, weaken, rename_comp, Scope.inclusion] using
        ih body (weaken frame)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveScopeTransport
