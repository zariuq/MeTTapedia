import Mettapedia.Logic.Relation.Development
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-! # Complete development from the constructor rules -/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedConstructorDevelopment

open Mettapedia.Logic.Relation

variable {α β γ δ : Type*}

/-- The two directions of a constructor step at one unary source. -/
structure Unary (inside : α → α → Prop) (step : β → β → Prop)
    (make : α → β) (source : α) : Prop where
  lift : ∀ {a b}, inside a b → step (make a) (make b)
  invert : ∀ {target}, step (make source) target → ∃ a, target = make a ∧ inside source a

theorem Unary.develop {inside : α → α → Prop} {step : β → β → Prop}
    {make : α → β} {source : α} (rule : Unary inside step make source)
    (inner : HasCompleteDevelopment inside source) : HasCompleteDevelopment step (make source) := by
  obtain ⟨common, next⟩ := inner
  refine ⟨make common, ?_⟩
  intro _ reduction
  obtain ⟨a, rfl, inside⟩ := rule.invert reduction
  exact rule.lift (next a inside)

/-- The constructor has congruence and no extra root step. -/
structure Binary (left : α → α → Prop) (right : β → β → Prop)
    (step : γ → γ → Prop) (make : α → β → γ) : Prop where
  lift : ∀ {a a' b b'}, left a a' → right b b' → step (make a b) (make a' b')
  invert : BinaryDecomposition left right step make

theorem Binary.develop {left : α → α → Prop} {right : β → β → Prop}
    {step : γ → γ → Prop} {make : α → β → γ} (rule : Binary left right step make)
    {a : α} {b : β} (first : HasCompleteDevelopment left a) (second : HasCompleteDevelopment right b) :
    HasCompleteDevelopment step (make a b) :=
  HasCompleteDevelopment.binary make first second rule.lift rule.invert

structure Ternary (first : α → α → Prop) (second : β → β → Prop) (third : γ → γ → Prop)
    (step : δ → δ → Prop) (make : α → β → γ → δ) : Prop where
  lift : ∀ {a a' b b' c c'}, first a a' → second b b' → third c c' →
    step (make a b c) (make a' b' c')
  invert : ∀ {a b c target}, step (make a b c) target →
    ∃ a' b' c', target = make a' b' c' ∧ first a a' ∧ second b b' ∧ third c c'

theorem Ternary.develop {first : α → α → Prop} {second : β → β → Prop}
    {third : γ → γ → Prop} {step : δ → δ → Prop} {make : α → β → γ → δ}
    (rule : Ternary first second third step make) {a : α} {b : β} {c : γ}
    (left : HasCompleteDevelopment first a) (middle : HasCompleteDevelopment second b)
    (right : HasCompleteDevelopment third c) : HasCompleteDevelopment step (make a b c) := by
  obtain ⟨a', toLeft⟩ := left
  obtain ⟨b', toMiddle⟩ := middle
  obtain ⟨c', toRight⟩ := right
  refine ⟨make a' b' c', ?_⟩
  intro _ reduction
  obtain ⟨u, v, w, rfl, hu, hv, hw⟩ := rule.invert reduction
  exact rule.lift (toLeft u hu) (toMiddle v hv) (toRight w hw)

variable {Head : Type}
variable (step : {n : Nat} → Tm Head n → Tm Head n → Prop)

/-- The structural rules. Applications and projections of pairs can have
additional reductions, so their complete developments are separate premises. -/
structure Structural : Prop where
  variableReturns : ∀ {n} (i : Fin n) {target}, step (.var i) target → step target (.var i)
  constantReturns : ∀ {n} (name : DeclName) {target : Tm Head n},
    step (.const name) target → step target (.const name)
  headReturns : ∀ {n} (value : Head) {target : Tm Head n},
    step (.head value) target → step target (.head value)
  pi : ∀ {n : Nat}, Binary (@step n) (@step (n + 1)) (@step n) Tm.pi
  sigma : ∀ {n : Nat}, Binary (@step n) (@step (n + 1)) (@step n) Tm.sigma
  id : ∀ {n : Nat}, Ternary (@step n) (@step n) (@step n) (@step n) Tm.id
  lam : ∀ {n : Nat} (body : Tm Head (n + 1)), Unary (@step (n + 1)) (@step n) Tm.lam body
  pair : ∀ {n : Nat}, Binary (@step n) (@step n) (@step n) Tm.pair
  fst : ∀ {n : Nat} (body : Tm Head n), (¬ ∃ a b, body = Tm.pair a b) →
    Unary (@step n) (@step n) Tm.fst body
  snd : ∀ {n : Nat} (body : Tm Head n), (¬ ∃ a b, body = Tm.pair a b) →
    Unary (@step n) (@step n) Tm.snd body
  refl : ∀ {n : Nat} (body : Tm Head n), Unary (@step n) (@step n) Tm.refl body

abbrev Cofinal {n : Nat} (source : Tm Head n) := HasCompleteDevelopment (@step n) source

/-- Root-specific arguments are used only at applications and pair projections. -/
theorem cofinal (rules : Structural step)
    (application : ∀ {n} {a b : Tm Head n}, Cofinal step a → Cofinal step b →
      Cofinal step (Tm.app a b))
    (firstProjection : ∀ {n} {a b : Tm Head n}, Cofinal step (.pair a b) →
      Cofinal step (.fst (.pair a b)))
    (secondProjection : ∀ {n} {a b : Tm Head n}, Cofinal step (.pair a b) →
      Cofinal step (.snd (.pair a b)))
    {n : Nat} (source : Tm Head n) : Cofinal step source := by
  induction source with
  | var index => exact ⟨_, fun _ => rules.variableReturns index⟩
  | const name => exact ⟨_, fun _ => rules.constantReturns name⟩
  | head value => exact ⟨_, fun _ => rules.headReturns value⟩
  | pi _ _ domain codomain => exact rules.pi.develop domain codomain
  | sigma _ _ domain codomain => exact rules.sigma.develop domain codomain
  | id _ _ _ type left right => exact rules.id.develop type left right
  | lam body inner => exact (rules.lam body).develop inner
  | app _ _ function argument => exact application function argument
  | pair _ _ first second => exact rules.pair.develop first second
  | fst body inner =>
      classical
      by_cases pair : ∃ a b, body = Tm.pair a b
      · obtain ⟨a, b, rfl⟩ := pair
        exact firstProjection inner
      · exact (rules.fst body pair).develop inner
  | snd body inner =>
      classical
      by_cases pair : ∃ a b, body = Tm.pair a b
      · obtain ⟨a, b, rfl⟩ := pair
        exact secondProjection inner
      · exact (rules.snd body pair).develop inner
  | refl body inner => exact (rules.refl body).develop inner

end ScopedConstructorDevelopment
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
