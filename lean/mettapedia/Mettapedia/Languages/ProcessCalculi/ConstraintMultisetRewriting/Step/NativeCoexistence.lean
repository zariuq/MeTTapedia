import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ScopedEffects

/-!
# Native interpretations of two coexisting states

A native interpretation retains the complete chosen state and separate maps
for the two source roles. Its resource and knowledge laws describe the shared
configuration. They do not assert transition closure: that is an additional
contract about candidates and their actual admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)

structure NativePair (left right : State) where
  state : State
  leftMap : Hom (E.frame left) (E.frame state)
  rightMap : Hom (E.frame right) (E.frame state)
  knowledge : X.Equivalent (E.knowledge state)
    (X.applyStore leftMap (E.knowledge left) ++ X.applyStore rightMap (E.knowledge right))
  present : E.present state = E.present left ∪ E.present right

namespace NativePair

variable {E} {left right : State} (pair : E.NativePair left right)

theorem models_iff {later : Obj} (σ : Hom (E.frame pair.state) later) :
    X.Models σ (E.knowledge pair.state) ↔
      X.Models (X.comp σ pair.leftMap) (E.knowledge left) ∧
        X.Models (X.comp σ pair.rightMap) (E.knowledge right) := by
  rw [pair.knowledge later σ, Frames.models_append,
    Frames.models_applyStore, Frames.models_applyStore]

theorem solvable_iff : X.Solvable (E.knowledge pair.state) ↔
    ∃ (later : Obj) (σ : Hom (E.frame pair.state) later),
      X.Models (X.comp σ pair.leftMap) (E.knowledge left) ∧
        X.Models (X.comp σ pair.rightMap) (E.knowledge right) := by
  constructor
  · rintro ⟨later, σ, solved⟩
    exact ⟨later, σ, (pair.models_iff σ).mp solved⟩
  · rintro ⟨later, σ, solved⟩
    exact ⟨later, σ, (pair.models_iff σ).mpr solved⟩

/-- Swapping source roles retains the same chosen native state. -/
def swap : E.NativePair right left where
  state := pair.state
  leftMap := pair.rightMap
  rightMap := pair.leftMap
  knowledge := fun later σ => (pair.knowledge later σ).trans (by
    rw [Frames.models_append, Frames.models_append]
    exact and_comm)
  present := pair.present.trans (Finset.union_comm _ _)

theorem swap_swap : pair.swap.swap = pair := by cases pair; rfl

theorem snapshot :
    X.Equivalent (E.configuration pair.state).equations
      (Coexistence.tensor
        (Coexistence.transport X pair.leftMap (E.configuration left))
        (Coexistence.transport X pair.rightMap (E.configuration right))).equations ∧
      (E.configuration pair.state).present =
        (Coexistence.tensor
          (Coexistence.transport X pair.leftMap (E.configuration left))
          (Coexistence.transport X pair.rightMap (E.configuration right))).present :=
  ⟨pair.knowledge, pair.present⟩

/-- Separate role keys keep the two maps distinct even when the frame values coincide. -/
def scopedPlacement : Systems.Placement (E.withScopeKeys Bool)
    [(false, left), (true, right)] (false, E.frame pair.state) := by
  rintro ⟨role, source⟩ member
  change (role, source) ∈ [(false, E.frame left), (true, E.frame right)] at member
  cases role with
  | false =>
      have same : source = E.frame left := by
        rcases List.mem_cons.mp member with same | later
        · exact (Prod.mk.inj same).2
        · have wrong := (Prod.mk.inj (List.mem_singleton.mp later)).1
          cases wrong
      cases same
      exact pair.leftMap
  | true =>
      have same : source = E.frame right := by
        rcases List.mem_cons.mp member with wrong | later
        · cases (Prod.mk.inj wrong).1
        · exact (Prod.mk.inj (List.mem_singleton.mp later)).2
      cases same
      exact pair.rightMap

theorem scoped_snapshot :
    X.Equivalent (E.configuration pair.state).equations
      (Systems.realize (E.withScopeKeys Bool) [(false, left), (true, right)] pair.scopedPlacement).equations ∧
    (E.configuration pair.state).present =
      (Systems.realize (E.withScopeKeys Bool) [(false, left), (true, right)] pair.scopedPlacement).present := by
  rw [Systems.realize, Systems.realize, Systems.realize, Coexistence.tensor_unit]
  exact pair.snapshot

end NativePair
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore
