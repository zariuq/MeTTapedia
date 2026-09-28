import Mettapedia.Machines.Cursor.Protocol

/-!
# Relational cursor refinement

Not every representation has a preferred function into one canonical store.
A relation between stores is enough: each request must produce the same
reply and related successor states. The relation then lifts to arbitrary
bounded clients, preserving termination versus suspension and live control.

This is a strong protocol-level bisimulation. Implementations may perform
different internal work inside an operation; divergent internal work must be
exposed through resumable replies before these total-step laws apply.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}

abbrev StateRel (source target : Provider P) :=
  {base : Base} → {index : Index base} → source.State base index →
    target.State base index → Prop

variable {source target : Provider P}

/-- Equal replies at a common request determine the same successor capability. -/
def Bisimulation (rel : StateRel source target) : Prop :=
  ∀ {base index} (left : source.State base index) (right : target.State base index),
    rel left right → ∀ request : P.Shape base index,
      ∃ (reply : P.Position request)
        (left' : source.State base (P.next request reply))
        (right' : target.State base (P.next request reply)),
        source.step left request = ⟨reply, left'⟩ ∧
        target.step right request = ⟨reply, right'⟩ ∧ rel left' right'

variable {Return : (base : Base) → Index base → Type u}
variable (C : Client (P := P) (Return := Return)) (rel : StateRel source target)

inductive PacketRel {base : Base} : Packet source C base → Packet target C base → Prop
  | same {index : Index base} (control : C.V base index)
      {left : source.State base index} {right : target.State base index}
      (related : rel left right) :
      PacketRel ⟨index, control, left⟩ ⟨index, control, right⟩

inductive OutcomeRel {base : Base} : Outcome source C base → Outcome target C base → Prop
  | paused {left right} (related : PacketRel C rel left right) :
      OutcomeRel (.paused left) (.paused right)
  | done {index : Index base} (value : Return base index)
      {left : source.State base index} {right : target.State base index}
      (related : rel left right) :
      OutcomeRel (.done ⟨index, value, left⟩) (.done ⟨index, value, right⟩)

/-- Local relational refinement preserves every bounded interaction, without
assuming either store is computably reconstructible from the other. -/
theorem advance_related (localLaw : Bisimulation rel)
    (leftCost : Charge source) (rightCost : Charge target)
    (budget : Nat) {base : Base} {left : Packet source C base} {right : Packet target C base}
    (related : PacketRel C rel left right) :
    OutcomeRel C rel (advance source C leftCost budget left).2
      (advance target C rightCost budget right).2 := by
  induction budget generalizing left right with
  | zero => exact .paused related
  | succ budget ih =>
      cases related with
      | @same index control left right related =>
          cases layer : C.str base index control with
          | mk shape children =>
              cases shape with
              | inl value =>
                  simp only [advance, layer]
                  exact .done value related
              | inr request =>
                  dsimp only [withHoles] at children
                  obtain ⟨reply, left', right', leftStep, rightStep, nextRelated⟩ :=
                    localLaw left right related request
                  simp only [advance, layer]
                  dsimp only [withHoles]
                  rw [leftStep, rightStep]
                  exact ih (.same (children reply) nextRelated)

/-- Functional representation maps are a special case of the relational law. -/
theorem Hom.bisimulation (h : Hom source target) :
    Bisimulation (fun left right => h.map left = right) := by
  intro base index left right related request
  subst right
  refine ⟨(source.step left request).1, (source.step left request).2,
    h.map (source.step left request).2, ?_, ?_, rfl⟩
  · rfl
  · exact (h.step left request).symm

end Mettapedia.Machines.Cursor
