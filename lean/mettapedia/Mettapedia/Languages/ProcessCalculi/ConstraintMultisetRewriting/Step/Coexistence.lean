import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectCore

/-!
# Coexistence in an arbitrary declaration frame

The carrier is the existing configuration of equations and occurrence identities.
Coexistence requires neither disjoint occurrences nor consistent joint knowledge.
Its solution observation is the intersection of the component observations.
Transport commutes with coexistence. An effect core has a canonical configuration
view, without a claim that its arbitrary native state carrier is closed under
this operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF

namespace Coexistence

variable {O : Type uOcc} [DecidableEq O]

section Algebra

variable {T : Type uT}

def tensor (left right : Configuration T O) : Configuration T O :=
  ⟨left.equations ++ right.equations, left.present ∪ right.present⟩

def unit : Configuration T O := ⟨[], ∅⟩

theorem tensor_assoc (left middle right : Configuration T O) :
    tensor (tensor left middle) right = tensor left (tensor middle right) := by
  simp [tensor, List.append_assoc, Finset.union_assoc]

@[simp] theorem unit_tensor (state : Configuration T O) :
    tensor unit state = state := by
  cases state
  simp [tensor, unit]

@[simp] theorem tensor_unit (state : Configuration T O) :
    tensor state unit = state := by
  cases state
  simp [tensor, unit]

end Algebra

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {a b c : Obj} (X : Frames Tm Hom)

def Same (left right : Configuration (Tm a) O) : Prop :=
  left.present = right.present ∧ X.Equivalent left.equations right.equations

omit [DecidableEq O] in
theorem Same.refl (state : Configuration (Tm a) O) : Same X state state :=
  ⟨rfl, fun _ _ => Iff.rfl⟩

omit [DecidableEq O] in
theorem Same.symm {left right : Configuration (Tm a) O} (same : Same X left right) :
    Same X right left := ⟨same.1.symm, fun b f => (same.2 b f).symm⟩

omit [DecidableEq O] in
theorem Same.trans {left middle right : Configuration (Tm a) O}
    (first : Same X left middle) (second : Same X middle right) : Same X left right :=
  ⟨first.1.trans second.1, fun b f => (first.2 b f).trans (second.2 b f)⟩

theorem models_tensor (f : Hom a b) (left right : Configuration (Tm a) O) :
    X.Models f (tensor left right).equations ↔
      X.Models f left.equations ∧ X.Models f right.equations :=
  Frames.models_append f left.equations right.equations

theorem tensor_comm (left right : Configuration (Tm a) O) :
    Same X (tensor left right) (tensor right left) := by
  refine ⟨Finset.union_comm _ _, fun b f => ?_⟩
  rw [models_tensor, models_tensor]
  exact and_comm

/-- Reusing the same occurrence identity aliases its cell; it creates no copy. -/
theorem tensor_self (state : Configuration (Tm a) O) : Same X (tensor state state) state := by
  refine ⟨Finset.union_self _, fun b f => ?_⟩
  rw [models_tensor]
  exact ⟨And.left, fun solved => ⟨solved, solved⟩⟩

theorem tensor_congr {left left' right right' : Configuration (Tm a) O}
    (one : Same X left left') (two : Same X right right') :
    Same X (tensor left right) (tensor left' right') := by
  refine ⟨?_, fun b f => ?_⟩
  · change left.present ∪ right.present = left'.present ∪ right'.present
    rw [one.1, two.1]
  · rw [models_tensor, models_tensor]
    exact and_congr (one.2 b f) (two.2 b f)

/-- Joint solvability asks for one common future solution, not two unrelated ones. -/
theorem solvable_tensor_iff (left right : Configuration (Tm a) O) :
    X.Solvable (tensor left right).equations ↔
      ∃ (b : Obj) (f : Hom a b), X.Models f left.equations ∧ X.Models f right.equations := by
  constructor
  · rintro ⟨b, f, solved⟩
    exact ⟨b, f, (models_tensor X f left right).mp solved⟩
  · rintro ⟨b, f, solved⟩
    exact ⟨b, f, (models_tensor X f left right).mpr solved⟩

def transport (f : Hom a b) (state : Configuration (Tm a) O) : Configuration (Tm b) O :=
  ⟨X.applyStore f state.equations, state.present⟩

omit [DecidableEq O] in
@[simp] theorem transport_unit (f : Hom a b) :
    transport X f (unit (T := Tm a) (O := O)) = unit := rfl

theorem transport_tensor (f : Hom a b) (left right : Configuration (Tm a) O) :
    transport X f (tensor left right) = tensor (transport X f left) (transport X f right) := by
  simp [transport, tensor, Frames.applyStore, List.map_append]

omit [DecidableEq O] in
@[simp] theorem transport_id (state : Configuration (Tm a) O) :
    transport X (X.id a) state = state := by
  cases state
  simp [transport, Frames.applyStore_id]

omit [DecidableEq O] in
theorem transport_comp (f : Hom a b) (g : Hom b c) (state : Configuration (Tm a) O) :
    transport X (X.comp g f) state = transport X g (transport X f state) := by
  simp only [transport, Frames.applyStore, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pair _
  simp only [Function.comp_apply, Frames.act_comp]

omit [DecidableEq O] in
theorem models_transport (f : Hom a b) (g : Hom b c) (state : Configuration (Tm a) O) :
    X.Models g (transport X f state).equations ↔ X.Models (X.comp g f) state.equations :=
  Frames.models_applyStore f g state.equations

omit [DecidableEq O] in
theorem transport_congr (f : Hom a b) {left right : Configuration (Tm a) O}
    (same : Same X left right) : Same X (transport X f left) (transport X f right) := by
  refine ⟨same.1, fun c g => ?_⟩
  rw [models_transport, models_transport]
  exact same.2 c (X.comp g f)

end Coexistence

namespace EffectCore

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

def configuration (effect : EffectCore X O State Firing) (state : State) :
    Configuration (Tm (effect.frame state)) O :=
  ⟨effect.knowledge state, effect.present state⟩

@[simp] theorem configuration_present (effect : EffectCore X O State Firing) (state : State) :
    (effect.configuration state).present = effect.present state := rfl

@[simp] theorem configuration_knowledge (effect : EffectCore X O State Firing) (state : State) :
    (effect.configuration state).equations = effect.knowledge state := rfl

end EffectCore
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
