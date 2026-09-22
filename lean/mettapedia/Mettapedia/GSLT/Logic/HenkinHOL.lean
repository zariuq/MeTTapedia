import Mettapedia.GSLT.Core.GSLT
import Mettapedia.Logic.HOL.Derivation

/-!
# HOL / Henkin as a GSLT seed

The native HOL kernel is `Logic.HOL.Derivation` (typed natural deduction)
with Henkin models in `Logic.HOL.Semantics.Henkin` and completeness in
`Logic.HOL.TermModel.HenkinCompleteness`.  Substitution as an operational
GSLT already exists at `Logic.HOL.TH0SubstitutionOperationalGSLT`.

This file only seeds the *language* as a GSLT: intrinsically typed terms
and closed formulas, discrete equations, empty rewrite relation.  It does
not grow a first-order sequent, Robinson resolution, or Henkin-completeness
rewrite theory.  Those remain consumers, in the same way propositional
resolution is a consumer of the GSLT kernel.

No Foundation. No LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.HenkinHOL

open Mettapedia.GSLT
open Mettapedia.Logic.HOL

/-- Packed intrinsically typed HOL term. -/
def Packed (Base : Type) (Const : Ty Base → Type) : Type :=
  Σ Γ : Ctx Base, Σ τ : Ty Base, Term Const Γ τ

/-- HOL language as a GSLT: terms, definitional equality, no computational
rewrites.  Inference is `Derivation`, not this relation. -/
def holTermGSLT (Base : Type) (Const : Ty Base → Type) : GSLT where
  Term := Packed Base Const
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

theorem holTerm_no_step {Base : Type} {Const : Ty Base → Type}
    (source target : Packed Base Const) :
    ¬ (holTermGSLT Base Const).Step source target :=
  fun step => step

/-- Seed signature: no constants. -/
def SeedConst : Ty Unit → Type := fun _ => Empty

abbrev SeedFormula : Type := Formula SeedConst []

/-- Closed HOL formulas as a GSLT.  Empty rewrites: tautology is a property
of `Derivation`, not a one-step relation. -/
def holFormulaGSLT : GSLT where
  Term := SeedFormula
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

theorem holFormula_no_step (source target : SeedFormula) :
    ¬ holFormulaGSLT.Step source target :=
  fun step => step

/-- Native provability, hosted at `Derivation`, not at `holFormulaGSLT.Step`. -/
def proved (φ : SeedFormula) : Prop :=
  Derivation SeedConst [] φ

theorem top_proved : proved .top :=
  Derivation.topI

/-- The language GSLT has no dynamics; the native kernel still proves `⊤`. -/
theorem proved_not_a_step (φ : SeedFormula) :
    proved φ → ¬ holFormulaGSLT.Step φ φ :=
  fun _ step => step

#print axioms holTerm_no_step
#print axioms holFormula_no_step
#print axioms top_proved
#print axioms proved_not_a_step

end Mettapedia.GSLT.Logic.HenkinHOL
