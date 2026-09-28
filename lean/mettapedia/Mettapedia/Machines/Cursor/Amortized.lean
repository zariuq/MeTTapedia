import Mettapedia.Machines.Cursor.Protocol

/-!
# Amortized cursor costs over live residuals

A local potential inequality composes over any bounded interactive client,
including one that is suspended rather than finished. Construction savings
cannot hide transfer charges when they are included in the actual meter.
The result can be instantiated independently for any natural-valued resource
coordinate. It is not a statement that a receipt equals measured wall time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u, u, u, u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable {source target : Provider P}

abbrev Potential (M : Provider P) :=
  {base : Base} → {index : Index base} → M.State base index → Nat

def outcomePotential (C : Client (P := P) (Return := Return))
    (potential : Potential source) {base : Base} : Outcome source C base → Nat
  | .paused packet => potential packet.2.2
  | .done result => potential result.2.2

/-- The debit/credit obligation is local to one request and its real successor.
It permits expensive operations paid for by decreases of stored potential. -/
def Amortized (h : Hom source target) (sourceCost : Charge source)
    (targetCost : Charge target) (potential : Potential source) : Prop :=
  ∀ {base index} (state : source.State base index) (request : P.Shape base index),
    sourceCost state request + potential (source.step state request).2 ≤
      targetCost (h.map state) request + potential state

/-- Local accounting yields a bound on the whole executed prefix, retaining
the potential of the actual suspended or completed state. -/
theorem advance_amortized (C : Client (P := P) (Return := Return))
    (h : Hom source target) (sourceCost : Charge source)
    (targetCost : Charge target) (potential : Potential source)
    (localBound : Amortized h sourceCost targetCost potential)
    (fuel : Nat) {base : Base} (packet : Packet source C base) :
    (advance source C sourceCost fuel packet).1 +
        outcomePotential C potential (advance source C sourceCost fuel packet).2 ≤
      (advance target C targetCost fuel (h.packet C packet)).1 +
        potential packet.2.2 := by
  induction fuel generalizing packet with
  | zero => simp [advance, outcomePotential]
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      change (advance source C sourceCost (fuel + 1) ⟨index, control, state⟩).1 +
          outcomePotential C potential
            (advance source C sourceCost (fuel + 1) ⟨index, control, state⟩).2 ≤
        (advance target C targetCost (fuel + 1) ⟨index, control, h.map state⟩).1 +
          potential state
      cases eq : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [advance, eq, outcomePotential]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [advance, eq]
              dsimp only [withHoles]
              rw [← h.step state request]
              have next := ih ⟨_, children (source.step state request).1,
                (source.step state request).2⟩
              have debit := localBound state request
              dsimp only [Hom.packet] at next
              dsimp only at next debit ⊢
              omega

/-- A zero initial potential gives a direct whole-prefix work bound. -/
theorem advance_cost_le (C : Client (P := P) (Return := Return))
    (h : Hom source target) (sourceCost : Charge source)
    (targetCost : Charge target) (potential : Potential source)
    (localBound : Amortized h sourceCost targetCost potential)
    (fuel : Nat) {base : Base} (packet : Packet source C base)
    (initial : potential packet.2.2 = 0) :
    (advance source C sourceCost fuel packet).1 ≤
      (advance target C targetCost fuel (h.packet C packet)).1 := by
  have bound := advance_amortized C h sourceCost targetCost potential localBound fuel packet
  rw [initial, Nat.add_zero] at bound
  omega

/-- Two independently justified representation layers compose their potential
accounts. This avoids reproving every client for every backend combination. -/
theorem Amortized.comp {third : Provider P}
    (first : Hom source target) (second : Hom target third)
    (sourceCost : Charge source) (targetCost : Charge target) (thirdCost : Charge third)
    (firstPotential : Potential source) (secondPotential : Potential target)
    (firstBound : Amortized first sourceCost targetCost firstPotential)
    (secondBound : Amortized second targetCost thirdCost secondPotential) :
    Amortized (first.comp second) sourceCost thirdCost
      (fun state => firstPotential state + secondPotential (first.map state)) := by
  intro base index state request
  have a := firstBound state request
  have b := secondBound (first.map state) request
  rw [← first.step state request] at b
  dsimp only [Hom.comp] at a b ⊢
  omega

end Mettapedia.Machines.Cursor
