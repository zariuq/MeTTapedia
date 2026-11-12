import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceSystems

/-!
# Placing a finite coexistence family in a native frame

A formal family is always available. A placement supplies the maps into a
chosen original frame; no common-frame existence law is assumed. Realization
uses the original equation-store transport and occurrence union. Its solutions
are exactly the shared-frame solutions of the complete family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore.Systems

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (effect : EffectCore X O State Firing)

def Placement.tail {state : State} {rest : effect.Systems} {target : Obj}
    (placement : Placement effect (state :: rest) target) : Placement effect rest target :=
  fun source member => placement source (List.mem_cons_of_mem _ member)

theorem models_cons {state : State} {rest : effect.Systems} {target : Obj}
    (placement : Placement effect (state :: rest) target) :
    Models effect (state :: rest) target placement ↔
      X.Models (Placement.at effect placement state List.mem_cons_self) (effect.knowledge state) ∧
        Models effect rest target (Placement.tail effect placement) := by
  constructor
  · intro solved
    exact ⟨solved state List.mem_cons_self,
      fun other member => solved other (List.mem_cons_of_mem _ member)⟩
  · rintro ⟨first, rest⟩ other member
    rcases List.mem_cons.mp member with same | later
    · subst other
      exact first
    · exact rest other later

def realize {target : Obj} : (systems : effect.Systems) →
    Placement effect systems target → Configuration (Tm target) O
  | [], _ => Coexistence.unit
  | state :: rest, placement => Coexistence.tensor
      (Coexistence.transport X (Placement.at effect placement state List.mem_cons_self)
        (effect.configuration state))
      (realize rest (Placement.tail effect placement))

theorem realize_present {target : Obj} (systems : effect.Systems)
    (placement : Placement effect systems target) :
    (realize effect systems placement).present = present effect systems := by
  induction systems with
  | nil => rfl
  | cons state rest ih =>
      change effect.present state ∪ (realize effect rest _).present =
        effect.present state ∪ present effect rest
      rw [ih]

/-- Realization neither invents nor loses a family solution. -/
theorem models_realize {target later : Obj} (next : Hom target later)
    (systems : effect.Systems) (placement : Placement effect systems target) :
    X.Models next (realize effect systems placement).equations ↔
      Models effect systems later (Placement.post effect next placement) := by
  induction systems with
  | nil =>
      constructor
      · intro _ state member
        cases member
      · intro _
        exact Frames.models_nil _
  | cons state rest ih =>
      rw [models_cons]
      change X.Models next (Coexistence.tensor
        (Coexistence.transport X (Placement.at effect placement state List.mem_cons_self)
          (effect.configuration state))
        (realize effect rest (Placement.tail effect placement))).equations ↔ _
      rw [Coexistence.models_tensor, Coexistence.models_transport, ih]
      rfl

theorem nativeSolvable_iff_realizable : ∀ systems : effect.Systems,
    NativeSolvable effect systems ↔ ∃ (target : Obj) (placement : Placement effect systems target),
      X.Solvable (realize effect systems placement).equations := by
  intro systems
  constructor
  · rintro ⟨target, placement, solved⟩
    refine ⟨target, placement, target, X.id target, ?_⟩
    exact (models_realize effect (X.id target) systems placement).mpr
      (models_post effect (X.id target) placement solved)
  · rintro ⟨target, placement, later, next, solved⟩
    exact ⟨later, Placement.post effect next placement,
      (models_realize effect next systems placement).mp solved⟩

/-- The only placement-existence requirement is a map for every represented frame. -/
theorem placement_exists_iff (systems : effect.Systems) (target : Obj) :
    Nonempty (Placement effect systems target) ↔
      ∀ state ∈ systems, Nonempty (Hom (effect.frame state) target) := by
  constructor
  · rintro ⟨placement⟩ state member
    exact ⟨Placement.at effect placement state member⟩
  · intro supplied
    classical
    refine ⟨fun source member => Classical.choice ?_⟩
    obtain ⟨state, present, same⟩ := List.mem_map.mp member
    subst source
    exact supplied state present

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore.Systems
