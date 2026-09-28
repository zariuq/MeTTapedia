import Mettapedia.Languages.MeTTa.CursorPathObservation
import Mettapedia.Machines.Cursor.Transfer

/-!
# Adaptive cursor clients over MeTTa term views

This adapter lifts the existing source/environment path-observation theorem
to the generic cursor protocol. Requests are relative child paths. A found
path advances the focus and exposes its rigid layer; an unknown or absent
path leaves the focus untouched. Variable uncertainty is not exhaustion.

Clients may choose the next path from previous replies and may run forever.
Every bounded interaction with the borrowed view agrees with full forcing,
including the retained client control and current focus. This is a semantic
result; memory ownership, relocation, and C costs remain adapter obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TermViewCursorProtocol

open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
open Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
open Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation
open TermViewCompilation CursorPathObservation

def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := List Nat
  Position _ := Observation (TermLayer Unit)
  next _ _ := ()

def paths {Value : Type} (out : Value → TermLayer Value) : Provider protocol where
  State _ _ := Value
  step value path := match readPath out path value with
    | .unknown => ⟨.unknown, value⟩
    | .absent => ⟨.absent, value⟩
    | .found child => ⟨.found ((out child).map (fun _ => ())), child⟩

/-- Layer preservation is the local obligation. The general protocol theorem
then handles arbitrary adaptive clients, rather than a fixed list of paths. -/
def pathsHom {A B : Type} (outA : A → TermLayer A) (outB : B → TermLayer B)
    (denote : A → B)
    (exact : ∀ value, (outA value).map denote = outB (denote value)) :
    Hom (paths outA) (paths outB) where
  map := denote
  step value path := by
    have pathLaw := readPath_natural outA outB denote exact path value
    cases observed : readPath outA path value with
    | unknown =>
        simp only [observed, Observation.map] at pathLaw
        simp [paths, observed, ← pathLaw]
    | absent =>
        simp only [observed, Observation.map] at pathLaw
        simp [paths, observed, ← pathLaw]
    | found child =>
        simp only [observed, Observation.map] at pathLaw
        have label : (outA child).map (fun _ => ()) =
            (outB (denote child)).map (fun _ => ()) := by
          rw [← exact child, TermLayer.map_comp]
        simp [paths, observed, ← pathLaw, label]

def borrowedHom {Owner Revision Occurrence Plan : Type} :
    Hom (paths (Cursor.out (Owner := Owner) (Revision := Revision)
      (Occurrence := Occurrence) (Plan := Plan))) (paths outOpen) :=
  pathsHom Cursor.out outOpen Cursor.denote Cursor.out_exact

/-- Full forcing and source/environment cursors preserve every bounded
adaptive observation, in both directions, with the same live continuation. -/
theorem borrowed_advance {Owner Revision Occurrence Plan : Type}
    {Return : Unit → Unit → Type}
    (C : Client (P := protocol) (Return := Return))
    (borrowedCost : Charge (paths (Cursor.out (Owner := Owner) (Revision := Revision)
      (Occurrence := Occurrence) (Plan := Plan))))
    (forcedCost : Charge (paths outOpen)) (budget : Nat)
    (packet : Packet (paths (Cursor.out (Owner := Owner) (Revision := Revision)
      (Occurrence := Occurrence) (Plan := Plan))) C ()) :
    borrowedHom.outcome C (advance _ C borrowedCost budget packet).2 =
      (advance (paths outOpen) C forcedCost budget (borrowedHom.packet C packet)).2 :=
  Hom.advance C borrowedHom borrowedCost forcedCost budget packet

example : (paths outOpen).step (base := ()) (index := ()) (.variable ⟨7, 1⟩) [3] =
    ⟨.unknown, .variable ⟨7, 1⟩⟩ := rfl

example : (paths outOpen).step (base := ()) (index := ()) (.integer 42) [3] =
    ⟨.absent, .integer 42⟩ := rfl

example : (paths outOpen).step (base := ()) (index := ())
    (.application [102] (.cons (.integer 42) .nil)) [0] =
    ⟨.found (.integer 42), .integer 42⟩ := rfl

end Mettapedia.Languages.MeTTa.TermViewCursorProtocol
