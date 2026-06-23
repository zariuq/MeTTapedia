import Mettapedia.AutoBooks.Codex.Henkin1950.Soundness

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-facing axiom schemata from Henkin (1950), p. 83.

This file currently formalizes the first four propositional schemata, which are
clear in the scanned text and map cleanly to the trusted HOL derivation core.
The remaining quantifier, extensionality, and description/choice schemata are
recorded below at their proper open-formula level.
-/

/-- Henkin axiom 1: `(X ∨ X) ⊃ X`. -/
def axiom1 (X : Sentence) : Sentence :=
  imp (or X X) X

/-- Henkin axiom 2: `X ⊃ (X ∨ Y)`. -/
def axiom2 (X Y : Sentence) : Sentence :=
  imp X (or X Y)

/-- Henkin axiom 3: `(X ∨ Y) ⊃ (Y ∨ X)`. -/
def axiom3 (X Y : Sentence) : Sentence :=
  imp (or X Y) (or Y X)

/-- Henkin axiom 4: `(X ⊃ Y) ⊃ ((Z ∨ X) ⊃ (Z ∨ Y))`. -/
def axiom4 (X Y Z : Sentence) : Sentence :=
  imp (imp X Y) (imp (or Z X) (or Z Y))

/-- Henkin axiom 5 as a schema in context: `(∀x, f x) ⊃ f x`. -/
def axiom5 {α : HTy} : Formula [α, Pred α] :=
  .imp
    (Term.all (.app (.var (.vs (.vs .vz))) (.var .vz)))
    (.app (.var (.vs .vz)) (.var .vz))

/-- Henkin axiom 6 as a schema in context:
`(∀x, y ∨ f x) ⊃ (y ∨ ∀x, f x)`. -/
def axiom6 {α : HTy} : Formula [o, Pred α] :=
  .imp
    (Term.all (.or (.var (.vs .vz)) (.app (.var (.vs (.vs .vz))) (.var .vz))))
    (.or (.var .vz) (Term.all (.app (.var (.vs (.vs .vz))) (.var .vz))))

/-- Henkin axiom 10 as a schema in context:
`(∀x, f x = g x) ⊃ (f = g)`. -/
def axiom10 {σ τ : HTy} : Formula [σ ⇒ τ, σ ⇒ τ] :=
  .imp
    (Term.all (.eq (.app (.var (.vs .vz)) (.var .vz))
                  (.app (.var (.vs (.vs .vz))) (.var .vz))))
    (.eq (.var .vz) (.var (.vs .vz)))

/-- Henkin axiom 11 as a schema in context:
`f x ⊃ f (ι f)`. -/
def axiom11 {α : HTy} : Formula [α, Pred α] :=
  .imp
    (.app (.var (.vs .vz)) (.var .vz))
    (.app (.var (.vs .vz)) (iotaTerm (.var (.vs .vz))))

theorem axiom1_theorem (X : Sentence) : Theorem (axiom1 X) := by
  simp [axiom1, imp, or]
  refine .impI ?_
  show Derivation Primitive [Term.or X X] X
  exact Derivation.orE (φ := X) (ψ := X) (χ := X)
    (.hyp (by simp))
    (.hyp (by simp))
    (.hyp (by simp))

theorem axiom2_theorem (X Y : Sentence) : Theorem (axiom2 X Y) := by
  simp [axiom2, imp, or]
  refine .impI ?_
  exact .orIL (.hyp (by simp))

theorem axiom3_theorem (X Y : Sentence) : Theorem (axiom3 X Y) := by
  simp [axiom3, imp, or]
  refine .impI ?_
  show Derivation Primitive [Term.or X Y] (Term.or Y X)
  exact Derivation.orE (φ := X) (ψ := Y) (χ := Term.or Y X)
    (.hyp (by simp))
    (.orIR (.hyp (by simp)))
    (.orIL (.hyp (by simp)))

theorem axiom4_theorem (X Y Z : Sentence) : Theorem (axiom4 X Y Z) := by
  simp [axiom4, imp, or]
  refine .impI ?_
  refine .impI ?_
  show Derivation Primitive [Term.or Z X, Term.imp X Y] (Term.or Z Y)
  exact Derivation.orE (φ := Z) (ψ := X) (χ := Term.or Z Y)
    (.hyp (by simp))
    (.orIL (.hyp (by simp)))
    (by
      have hImp : Derivation Primitive [X, Term.or Z X, Term.imp X Y] (Term.imp X Y) :=
        .hyp (show Term.imp X Y ∈ [X, Term.or Z X, Term.imp X Y] from by simp)
      have hX : Derivation Primitive [X, Term.or Z X, Term.imp X Y] X :=
        .hyp (show X ∈ [X, Term.or Z X, Term.imp X Y] from by simp)
      have hY : Derivation Primitive [X, Term.or Z X, Term.imp X Y] Y :=
        .impE hImp hX
      exact .orIR hY)

theorem axiom5_theorem {α : HTy} : TheoremInContext (axiom5 (α := α)) := by
  refine .impI ?_
  exact
    (Derivation.allE (.var .vz)
      (.hyp (show
        (Term.all (.app (.var (.vs (.vs .vz))) (.var .vz))) ∈
          [(Term.all (.app (.var (.vs (.vs .vz))) (.var .vz)))] from by
        simp)))

theorem axiom10_theorem {σ τ : HTy} :
    TheoremInContext (axiom10 (σ := σ) (τ := τ)) := by
  refine .impI ?_
  simpa [axiom10] using
    (Derivation.funExt
      (.hyp (show
        (Term.all (.eq (.app (.var (.vs .vz)) (.var .vz))
                      (.app (.var (.vs (.vs .vz))) (.var .vz)))) ∈
          [(Term.all (.eq (.app (.var (.vs .vz)) (.var .vz))
                        (.app (.var (.vs (.vs .vz))) (.var .vz))))] from by
        simp)))

theorem axiom1_validInGeneral (X : Sentence) : ValidInGeneral (axiom1 X) :=
  theorem_validInGeneral (axiom1_theorem X)

theorem axiom2_validInGeneral (X Y : Sentence) : ValidInGeneral (axiom2 X Y) :=
  theorem_validInGeneral (axiom2_theorem X Y)

theorem axiom3_validInGeneral (X Y : Sentence) : ValidInGeneral (axiom3 X Y) :=
  theorem_validInGeneral (axiom3_theorem X Y)

theorem axiom4_validInGeneral (X Y Z : Sentence) : ValidInGeneral (axiom4 X Y Z) :=
  theorem_validInGeneral (axiom4_theorem X Y Z)

theorem axiom5_validInGeneral {α : HTy} :
    ValidInGeneralCtx (axiom5 (α := α)) :=
  theoremInContext_validInGeneral axiom5_theorem

theorem axiom6_validInGeneral {α : HTy} :
    ValidInGeneralCtx (axiom6 (α := α)) := by
  intro M ρ hρ
  classical
  let HM := M.toHenkinModel
  let y : Ty.denote HM.Carrier o := ρ .vz
  show (HenkinModel.denote HM (axiom6 (α := α)) ρ).down
  simp [axiom6, HM]
  intro hall
  by_cases hy : y.down
  · exact Or.inl hy
  · exact Or.inr (by
      intro x hx
      have h := hall x hx
      cases h with
      | inl hy' => exact False.elim (hy hy')
      | inr hx' => exact hx')

theorem axiom10_validInGeneral {σ τ : HTy} :
    ValidInGeneralCtx (axiom10 (σ := σ) (τ := τ)) :=
  theoremInContext_validInGeneral axiom10_theorem

theorem axiom11_validInGeneral {α : HTy} :
    ValidInGeneralCtx (axiom11 (α := α)) := by
  intro M ρ hρ
  let HM := M.toHenkinModel
  let x : Ty.denote HM.Carrier α := ρ .vz
  let p : Ty.denote HM.Carrier (Pred α) := ρ (.vs .vz)
  have hx : HM.adm α x := hρ .vz
  have hp : HM.adm (Pred α) p := hρ (.vs .vz)
  show (HenkinModel.denote HM (axiom11 (α := α)) ρ).down
  simp [axiom11, iotaTerm, HM]
  intro hpx
  exact M.iota_sound α p hp ⟨x, hx, hpx⟩

end Mettapedia.AutoBooks.Codex.Henkin1950
