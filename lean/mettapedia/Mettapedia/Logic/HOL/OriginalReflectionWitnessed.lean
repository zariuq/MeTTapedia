import Mettapedia.Logic.HOL.DerivationExtensionality

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
# Witnessed Source Signatures

The obstruction in
`/home/zar/claude/lean-projects/mettapedia/Mettapedia/Logic/HOL/OriginalReflectionObstruction.lean`
shows that naive constant-based reflection fails when the source signature can
leave quantified base types syntactically empty.

This file packages the clean positive replacement target:

- if the original signature supplies a closed witness at each base type,
- then every simple type already has a closed source term,
- so source-level existential theorems like `∃ x : τ, ⊤` match the existential
  power added by constant-based Henkinization.
-/

/-- Closed witnesses for each base type of the original signature. -/
structure BaseWitnesses (Base : Type u) (Const : Ty Base → Type v) where
  witness : ∀ b : Base, ClosedTerm Const (.base b)

namespace BaseWitnesses

/-- Recursively build a closed source term at every simple type. -/
def witnessTerm (W : BaseWitnesses Base Const) : (τ : Ty Base) → ClosedTerm Const τ
  | .prop => .top
  | .base b => W.witness b
  | .arr σ τ => .lam (weaken (Base := Base) (σ := σ) (witnessTerm W τ))

@[simp] theorem witnessTerm_prop (W : BaseWitnesses Base Const) :
    witnessTerm W .prop = (.top : ClosedFormula Const) :=
  rfl

@[simp] theorem witnessTerm_base (W : BaseWitnesses Base Const) (b : Base) :
    witnessTerm W (.base b) = W.witness b :=
  rfl

@[simp] theorem witnessTerm_arr (W : BaseWitnesses Base Const) (σ τ : Ty Base) :
    witnessTerm W (σ ⇒ τ) =
      .lam (weaken (Base := Base) (σ := σ) (witnessTerm W τ)) :=
  rfl

/-- Positive example: every simple type becomes syntactically inhabited. -/
theorem nonempty_closedTerm (W : BaseWitnesses Base Const) (τ : Ty Base) :
    Nonempty (ClosedTerm Const τ) :=
  ⟨witnessTerm W τ⟩

/--
Under base-type witnesses, the original source calculus already proves
`∃ x : τ, ⊤` for every simple type `τ`.
-/
theorem theorem_existsTop (W : BaseWitnesses Base Const) (τ : Ty Base) :
    ExtDerivation.Theorem Const (.ex (.top : Formula Const [τ])) := by
  refine ExtDerivation.exI (witnessTerm W τ) ?_
  simpa using
    (ExtDerivation.topI : ExtDerivation Const [] (.top : ClosedFormula Const))

/-- Positive base-type specialization of the witnessed existential theorem. -/
theorem theorem_existsTop_base (W : BaseWitnesses Base Const) (b : Base) :
    ExtDerivation.Theorem Const (.ex (.top : Formula Const [.base b])) :=
  theorem_existsTop W (.base b)

end BaseWitnesses

end Mettapedia.Logic.HOL
