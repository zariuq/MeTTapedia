import Mettapedia.Logic.Relation.Normalization

/-!
# Componentwise development

An inverted constructor step recovers the reductions of its operands.
The same one-step law supports complete developments and finite path
decomposition, including operands from different binding contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Relation

open _root_.Relation

universe u v w

/-- An immediate successor shared by all immediate reducts of the source. -/
def HasCompleteDevelopment {α : Type u} (step : α → α → Prop) (source : α) : Prop :=
  ∃ common, ∀ reduct, step source reduct → step reduct common

/-- Every step from an assembled pair comes from steps in both components. -/
def BinaryDecomposition {α : Type u} {β : Type v} {γ : Type w}
    (first : α → α → Prop) (second : β → β → Prop) (step : γ → γ → Prop)
    (assemble : α → β → γ) : Prop :=
  ∀ {a b target}, step (assemble a b) target →
    ∃ a' b', target = assemble a' b' ∧ first a a' ∧ second b b'

theorem HasCompleteDevelopment.binary {α : Type u} {β : Type v} {γ : Type w}
    {first : α → α → Prop} {second : β → β → Prop} {step : γ → γ → Prop}
    (assemble : α → β → γ) {a : α} {b : β}
    (left : HasCompleteDevelopment first a)
    (right : HasCompleteDevelopment second b)
    (congruence : ∀ {a a' b b'}, first a a' → second b b' →
      step (assemble a b) (assemble a' b'))
    (invert : ∀ {target}, step (assemble a b) target →
      ∃ a' b', target = assemble a' b' ∧ first a a' ∧ second b b') :
    HasCompleteDevelopment step (assemble a b) := by
  obtain ⟨leftTarget, leftDevelops⟩ := left
  obtain ⟨rightTarget, rightDevelops⟩ := right
  refine ⟨assemble leftTarget rightTarget, ?_⟩
  intro _ reduced
  obtain ⟨a', b', rfl, toLeft, toRight⟩ := invert reduced
  exact congruence (leftDevelops a' toLeft) (rightDevelops b' toRight)

theorem BinaryDecomposition.path {α : Type u} {β : Type v} {γ : Type w}
    {first : α → α → Prop} {second : β → β → Prop} {step : γ → γ → Prop}
    {assemble : α → β → γ} (invert : BinaryDecomposition first second step assemble)
    {a : α} {b : β} {target : γ} (reduced : ReflTransGen step (assemble a b) target) :
    ∃ a' b', target = assemble a' b' ∧ ReflTransGen first a a' ∧ ReflTransGen second b b' := by
  induction reduced with
  | refl => exact ⟨a, b, rfl, .refl, .refl⟩
  | tail _ last induction =>
      obtain ⟨middleLeft, middleRight, rfl, leftSteps, rightSteps⟩ := induction
      obtain ⟨_, _, same, leftStep, rightStep⟩ := invert last
      exact ⟨_, _, same, leftSteps.tail leftStep, rightSteps.tail rightStep⟩

theorem image_of_path {α : Type u} {β : Type v} {step : β → β → Prop}
    (map : α → β) (closed : ∀ {value next}, step (map value) next → ∃ image, next = map image)
    {source : α} {target : β} (steps : ReflTransGen step (map source) target) :
    ∃ image, target = map image := by
  induction steps with
  | refl => exact ⟨source, rfl⟩
  | tail _ last induction =>
      obtain ⟨_, rfl⟩ := induction
      exact closed last

theorem confluent_of_diamond {α : Type u} {step : α → α → Prop}
    (diamond : ∀ {source left right}, step source left → step source right → Join step left right) :
    Confluent step := by
  intro source left right first second
  apply church_rosser _ first second
  intro a b c ab ac
  obtain ⟨join, bj, cj⟩ := diamond ab ac
  exact ⟨join, .single bj, .single cj⟩

section Controls

private def binaryStep : Bool × Bool → Bool × Bool → Prop :=
  fun _ target => target = (true, false)

example : HasCompleteDevelopment binaryStep (false, true) := by
  apply HasCompleteDevelopment.binary Prod.mk
    (first := fun _ next => next = true) (second := fun _ next => next = false)
  · exact ⟨true, fun _ _ => rfl⟩
  · exact ⟨false, fun _ _ => rfl⟩
  · rintro _ _ _ _ rfl rfl
    rfl
  · rintro _ rfl
    exact ⟨true, false, rfl, rfl, rfl⟩

private def rootStep : Option (Bool × Bool) → Option (Bool × Bool) → Prop
  | some _, none => True
  | _, _ => False

example {r₁ r₂ : Bool → Bool → Prop} :
    ¬ BinaryDecomposition r₁ r₂ rootStep (fun a b => some (a, b)) := by
  intro inverted
  obtain ⟨_, _, impossible, _, _⟩ := inverted (a := false) (b := true) (target := none) .intro
  cases impossible

end Controls

end Mettapedia.Logic.Relation
