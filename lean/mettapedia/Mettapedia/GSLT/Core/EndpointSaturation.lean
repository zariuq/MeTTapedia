import Mettapedia.GSLT.Core.GSLT

/-!
# One authored step, modulo equations at its endpoints

The saturated relation is the least one containing the authored steps
and insensitive to representatives at both ends. In particular, changing
representative does not count as firing an additional rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.EndpointSaturation

variable {A : Type*}

def Step (equations : Setoid A) (authored : A → A → Prop) (source target : A) : Prop :=
  ∃ before after, equations.r source before ∧ authored before after ∧ equations.r after target

def theory (equations : Setoid A) (authored : A → A → Prop) : GSLT where
  Term := A
  equations := equations
  rewrites := Step equations authored
  rewrites_resp_left := by
    intro source other target equivalent h
    obtain ⟨before, after, into, applied, out⟩ := h
    exact ⟨target, ⟨before, after, equations.iseqv.trans (equations.iseqv.symm equivalent) into,
      applied, out⟩, equations.iseqv.refl target⟩
  rewrites_resp_right := by
    intro source target other h equivalent
    obtain ⟨before, after, into, applied, out⟩ := h
    exact ⟨before, after, into, applied, equations.iseqv.trans out equivalent⟩

theorem contains {equations : Setoid A} {authored : A → A → Prop} {a b : A}
    (fired : authored a b) : Step equations authored a b :=
  ⟨a, b, equations.iseqv.refl a, fired, equations.iseqv.refl b⟩

theorem least {equations : Setoid A} {authored target : A → A → Prop}
    (includes : ∀ x y, authored x y → target x y)
    (left : ∀ x x' y, equations.r x x' → target x' y → target x y)
    (right : ∀ x y y', target x y → equations.r y y' → target x y')
    {a b : A} (fired : Step equations authored a b) : target a b := by
  obtain ⟨x, y, sourceEq, step, targetEq⟩ := fired
  exact right a y b (left a x y sourceEq (includes x y step)) targetEq

/-! ## Equations only on the input of an observation -/

variable {B : Type*}

def inputEq (equations : Setoid A) : A ⊕ B → A ⊕ B → Prop
  | .inl first, .inl second => equations.r first second
  | .inr first, .inr second => first = second
  | _, _ => False

def inputSetoid (equations : Setoid A) : Setoid (A ⊕ B) where
  r := inputEq equations
  iseqv := by
    constructor
    · rintro (a | b)
      · exact equations.iseqv.refl a
      · rfl
    · intro a b h
      cases a <;> cases b <;> first
      | exact equations.iseqv.symm h
      | exact Eq.symm h
      | cases h
    · intro a b c h k
      cases a <;> cases b <;> cases c <;> first
      | exact equations.iseqv.trans h k
      | exact Eq.trans h k
      | exact False.elim h
      | exact False.elim k

def observe (entry : A → B → Prop) : A ⊕ B → A ⊕ B → Prop
  | .inl a, .inr b => entry a b
  | _, _ => False

/-- An equation-aware observation reads the input through its quotient
but returns the actual observation unchanged. -/
def inputTheory (equations : Setoid A) (entry : A → B → Prop) : GSLT :=
  theory (inputSetoid equations) (observe entry)

theorem input_step_iff (equations : Setoid A) (entry : A → B → Prop) (a : A) (b : B) :
    (inputTheory equations entry).Step (.inl a) (.inr b) ↔
      ∃ representative, equations.r a representative ∧ entry representative b := by
  change Step (inputSetoid equations) (observe entry) _ _ ↔ _
  constructor
  · rintro ⟨before, after, input, selected, output⟩
    cases before with
    | inr _ => cases input
    | inl representative =>
      cases after with
      | inl _ => cases output
      | inr chosen =>
        change chosen = b at output
        subst chosen
        exact ⟨representative, input, selected⟩
  · rintro ⟨representative, same, admitted⟩
    exact ⟨.inl representative, .inr b, same, admitted, rfl⟩

theorem output_eq_iff (equations : Setoid A) (entry : A → B → Prop) (first second : B) :
    (inputTheory equations entry).Equiv (.inr first) (.inr second) ↔ first = second := Iff.rfl

theorem output_is_final (equations : Setoid A) (entry : A → B → Prop) (chosen : B) :
    (inputTheory equations entry).IsNormalForm (.inr chosen) := by
  rintro ⟨_, before, after, into, fired, _⟩
  cases before with
  | inl _ => cases into
  | inr _ => cases after <;> cases fired

end Mettapedia.GSLT.EndpointSaturation
