/-
# Standard Deontic Logic (SDL)

Formalization of Standard Deontic Logic, a modal logic for normative reasoning.

## Key Operators

- O φ : "φ is obligatory" (ought)
- P φ : "φ is permitted" (may)
- F φ : "φ is forbidden" (must not)

## Axioms

SDL extends classical propositional logic with:
- K: O(φ → ψ) → (Oφ → Oψ)
- D: Oφ → Pφ (ought implies may)
- Nec: From ⊢ φ, infer ⊢ Oφ

## References

- von Wright (1951): Deontic Logic
- Chellas (1980): Modal Logic, Chapter 10
- McNamara (2014): Stanford Encyclopedia of Philosophy
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

namespace Mettapedia.AutoBooks.ClaudeProcWam.Governance

/-! ## SDL Syntax -/

/-- Propositional variables -/
abbrev DeonticVar := String

/-- SDL formulas -/
inductive DeonticFormula where
  | var : DeonticVar → DeonticFormula
  | tt : DeonticFormula
  | ff : DeonticFormula
  | neg : DeonticFormula → DeonticFormula
  | conj : DeonticFormula → DeonticFormula → DeonticFormula
  | disj : DeonticFormula → DeonticFormula → DeonticFormula
  | impl : DeonticFormula → DeonticFormula → DeonticFormula
  /-- Obligation: Oφ means φ is obligatory -/
  | oblig : DeonticFormula → DeonticFormula
  deriving DecidableEq, Repr, Inhabited

namespace DeonticFormula

/-- Permission: Pφ ≡ ¬O¬φ -/
def perm (φ : DeonticFormula) : DeonticFormula :=
  .neg (.oblig (.neg φ))

/-- Forbidden: Fφ ≡ O¬φ -/
def forbidden (φ : DeonticFormula) : DeonticFormula :=
  .oblig (.neg φ)

/-- Optional: φ is neither obligatory nor forbidden -/
def optional (φ : DeonticFormula) : DeonticFormula :=
  .conj (.neg (.oblig φ)) (.neg (.oblig (.neg φ)))

instance : ToString DeonticFormula where
  toString f := go f
where
  go : DeonticFormula → String
    | .var v => v
    | .tt => "⊤"
    | .ff => "⊥"
    | .neg p => s!"¬{go p}"
    | .conj p q => s!"({go p} ∧ {go q})"
    | .disj p q => s!"({go p} ∨ {go q})"
    | .impl p q => s!"({go p} → {go q})"
    | .oblig p => s!"O{go p}"

end DeonticFormula

/-! ## SDL Semantics (Possible Worlds)

SDL is interpreted over Kripke frames where:
- Worlds represent possible situations
- Accessibility relation captures "ideal" alternatives
- O φ holds at w iff φ holds at all w-accessible worlds
-/

/-- A possible world -/
abbrev World := Nat

/-- Deontic Kripke model -/
structure DeonticModel where
  /-- Set of possible worlds -/
  worlds : Set World
  /-- Accessibility relation (w R v means v is an ideal alternative to w) -/
  access : World → World → Prop
  /-- Valuation: which variables are true at which worlds -/
  val : World → DeonticVar → Bool
  /-- Accessibility only relates worlds in the model -/
  access_closed : ∀ w v, w ∈ worlds → access w v → v ∈ worlds

/-- Truth at a world in a model -/
def DeonticFormula.truthy (m : DeonticModel) (w : World) : DeonticFormula → Prop
  | .var p => m.val w p = true
  | .tt => True
  | .ff => False
  | .neg φ => ¬φ.truthy m w
  | .conj φ ψ => φ.truthy m w ∧ ψ.truthy m w
  | .disj φ ψ => φ.truthy m w ∨ ψ.truthy m w
  | .impl φ ψ => φ.truthy m w → ψ.truthy m w
  | .oblig φ => ∀ v, m.access w v → φ.truthy m v

/-- Validity in a model: true at all worlds -/
def DeonticFormula.validInModel (m : DeonticModel) (φ : DeonticFormula) : Prop :=
  ∀ w ∈ m.worlds, φ.truthy m w

/-- Validity: true in all serial models (frames where ∀w. ∃v. R w v) -/
def DeonticFormula.valid (φ : DeonticFormula) : Prop :=
  ∀ m : DeonticModel, (∀ w ∈ m.worlds, ∃ v ∈ m.worlds, m.access w v) →
    φ.validInModel m

/-! ## SDL Proof System

We define a Hilbert-style proof system for SDL.
-/

/-- SDL provability -/
inductive SDLProvable : DeonticFormula → Prop where
  /-- All propositional tautologies are provable -/
  | taut (φ : DeonticFormula) (htaut : ∀ m : DeonticModel, φ.validInModel m) :
      SDLProvable φ
  /-- K axiom: O(φ → ψ) → (Oφ → Oψ) -/
  | ax_K (φ ψ : DeonticFormula) :
      SDLProvable (.impl (.oblig (.impl φ ψ)) (.impl (.oblig φ) (.oblig ψ)))
  /-- D axiom: Oφ → Pφ (equivalently, Oφ → ¬O¬φ) -/
  | ax_D (φ : DeonticFormula) :
      SDLProvable (.impl (.oblig φ) (.neg (.oblig (.neg φ))))
  /-- Modus ponens: From φ and φ → ψ, derive ψ -/
  | mp (φ ψ : DeonticFormula) :
      SDLProvable φ → SDLProvable (.impl φ ψ) → SDLProvable ψ
  /-- Necessitation: From ⊢ φ, derive ⊢ Oφ -/
  | nec (φ : DeonticFormula) :
      SDLProvable φ → SDLProvable (.oblig φ)

notation "⊢SDL " φ => SDLProvable φ

/-! ## Derived Theorems -/

/-- O⊤ is provable -/
theorem oblig_top : ⊢SDL .oblig .tt := by
  apply SDLProvable.nec
  apply SDLProvable.taut
  intro m
  unfold DeonticFormula.validInModel DeonticFormula.truthy
  intro w _
  trivial

/-- Permission definition: P φ ↔ ¬O¬φ -/
theorem perm_def (φ : DeonticFormula) :
    ⊢SDL .impl φ.perm (.neg (.oblig (.neg φ))) := by
  unfold DeonticFormula.perm
  apply SDLProvable.taut
  intro m
  unfold DeonticFormula.validInModel DeonticFormula.truthy
  intro w _
  simp

/-- Forbidden definition: F φ ↔ O¬φ -/
theorem forbidden_def (φ : DeonticFormula) :
    ⊢SDL .impl φ.forbidden (.oblig (.neg φ)) := by
  unfold DeonticFormula.forbidden
  apply SDLProvable.taut
  intro m
  unfold DeonticFormula.validInModel DeonticFormula.truthy
  intro w _ h
  exact h

/-! ## Soundness -/

/-- SDL is sound with respect to serial Kripke frames -/
theorem SDL_sound (φ : DeonticFormula) (hprov : ⊢SDL φ) : φ.valid := by
  induction hprov with
  | taut _ htaut =>
    unfold DeonticFormula.valid
    intro m _
    exact htaut m
  | ax_K ψ χ =>
    unfold DeonticFormula.valid DeonticFormula.validInModel DeonticFormula.truthy
    intro m _ w _
    intro hOimp hOψ v hRwv
    apply hOimp v hRwv
    exact hOψ v hRwv
  | ax_D ψ =>
    unfold DeonticFormula.valid DeonticFormula.validInModel DeonticFormula.truthy
    intro m hserial w hw
    intro hOψ hOneg
    obtain ⟨v, hv, hRwv⟩ := hserial w hw
    have := hOψ v hRwv
    have := hOneg v hRwv
    contradiction
  | mp ψ χ _ _ ih1 ih2 =>
    unfold DeonticFormula.valid at *
    intro m hserial
    unfold DeonticFormula.validInModel at *
    intro w hw
    have h1 := ih1 m hserial w hw
    have h2 := ih2 m hserial w hw
    unfold DeonticFormula.truthy at h2
    exact h2 h1
  | nec ψ _ ih =>
    unfold DeonticFormula.valid at *
    intro m hserial
    unfold DeonticFormula.validInModel at *
    intro w hw
    unfold DeonticFormula.truthy
    intro v hRwv
    -- v ∈ m.worlds by access_closed
    have hv : v ∈ m.worlds := m.access_closed w v hw hRwv
    exact ih m hserial v hv

/-! ## Examples -/

/-- Ross's paradox: O(mail letter) → O(mail letter ∨ burn letter)
    This is valid in SDL but counterintuitive -/
def rosssParadox : DeonticFormula :=
  .impl
    (.oblig (.var "mail"))
    (.oblig (.disj (.var "mail") (.var "burn")))

/-- Ross's paradox is derivable in SDL -/
theorem ross_derivable : ⊢SDL rosssParadox := by
  unfold rosssParadox
  apply SDLProvable.mp _ _ _ (SDLProvable.ax_K _ _)
  apply SDLProvable.nec
  apply SDLProvable.taut
  intro m
  unfold DeonticFormula.validInModel DeonticFormula.truthy
  intro w _ h
  left
  exact h

#check rosssParadox

end Mettapedia.AutoBooks.ClaudeProcWam.Governance
