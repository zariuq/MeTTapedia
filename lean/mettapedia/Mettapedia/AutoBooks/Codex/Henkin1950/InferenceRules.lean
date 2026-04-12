import Mettapedia.AutoBooks.Codex.Henkin1950.DerivedResults

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-facing interface for Henkin's inference rules on p. 83.

The trusted HOL core already provides structurally stronger operations than the
paper's raw rule list.  This file exposes the directly supported fragment in the
Henkin Codex namespace and states the quantifier/application rules in the
one-free-variable theorem form that the current core supports cleanly.
-/

/-- Codex counterpart of Henkin's Rule I: capture-avoiding renaming is admissible
for extensional derivations.  This is stronger and cleaner than the paper's
single-variable presentation. -/
theorem ruleI_rename
    {Γ Γ' : Ctx Atom}
    (ρ : Rename Atom Γ Γ')
    {Δ : List (Formula Γ)} {φ : Formula Γ} :
    ExtDerivation Primitive Δ φ →
      ExtDerivation Primitive
        (Δ.map (Mettapedia.Logic.HOL.rename ρ))
        (Mettapedia.Logic.HOL.rename ρ φ) :=
  ExtDerivation.rename ρ

/-- Codex counterpart of Henkin's Rule II: beta reduction. -/
theorem ruleII_beta {α β : HTy}
    (t : ClosedTerm α) (u : Term [α] β) :
    ExtTheorem (eq (.app (.lam u) t) (instantiate t u)) :=
  .beta t u

/-- Codex counterpart of Henkin's Rule III: beta conversion may be used in the
reverse direction as well. -/
theorem ruleIII_beta_symm {α β : HTy}
    (t : ClosedTerm α) (u : Term [α] β) :
    ExtTheorem (eq (instantiate t u) (.app (.lam u) t)) :=
  .eqSymm (.beta t u)

/-- Closed-theorem form of Henkin's Rule VI: from an open theorem in one
variable, universally generalize. -/
theorem ruleVI_generalize {α : HTy}
    (φ : Formula [α]) :
    ExtTheoremInContext φ →
      ExtTheorem (.all φ) := by
  intro hφ
  exact .allI (by simpa [weakenHyps] using hφ)

/-- Closed-theorem form of Henkin's Rule IV: specialize a one-variable open
theorem at a closed term. -/
theorem ruleIV_specialize {α : HTy}
    (φ : Formula [α]) (t : ClosedTerm α) :
    ExtTheoremInContext φ →
      ExtTheorem (instantiate t φ) := by
  intro hφ
  exact .allE t (ruleVI_generalize φ hφ)

/-- Codex counterpart of Henkin's Rule V: modus ponens on closed theorems. -/
theorem ruleV_modusPonens {A B : Sentence} :
    ExtTheorem (imp A B) →
      ExtTheorem A →
      ExtTheorem B := by
  intro hAB hA
  exact .impE hAB hA

end Mettapedia.AutoBooks.Codex.Henkin1950
