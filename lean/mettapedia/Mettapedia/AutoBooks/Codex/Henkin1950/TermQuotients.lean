import Mettapedia.AutoBooks.Codex.Henkin1950.Syntax
import Mettapedia.Logic.HOL.DerivationExtensionality

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Typed quotient infrastructure for Henkin pp. 86-87.

Henkin's domains are built from equivalence classes of closed formulas/terms
under provable equality, with higher-type application descending to those
classes.  The trusted HOL core already contains the needed extensional equality
rules; this file packages the corresponding closed-theory quotient layer in the
Codex Henkin namespace.
-/

/-- Finite extensional derivability from a set of closed Henkin formulas. -/
def ExtSetProvable (T : ClosedTheorySet) (φ : Sentence) : Prop :=
  ∃ Γ : ClosedTheory,
    (∀ ψ : Sentence, ψ ∈ Γ → ψ ∈ T) ∧
      ExtDerivation Primitive Γ φ

/-- Build extensional set-provability from a finite closed subtheory. -/
theorem extSetProvable_of_closedTheory
    {T : ClosedTheorySet} {Δ : ClosedTheory} {φ : Sentence}
    (hΔ : ∀ {ψ : Sentence}, ψ ∈ Δ → ψ ∈ T)
    (hφ : ExtDerivation Primitive Δ φ) :
    ExtSetProvable T φ :=
  ⟨Δ, by intro ψ hψ; exact hΔ hψ, hφ⟩

/-- Any member of a closed theory is extentionally provable from that theory. -/
theorem extSetProvable_of_mem
    {T : ClosedTheorySet} {φ : Sentence}
    (hφ : φ ∈ T) :
    ExtSetProvable T φ := by
  refine ⟨[φ], ?_, ?_⟩
  · intro ψ hψ
    simp at hψ
    subst hψ
    exact hφ
  · exact .hyp (by simp)

/-- Closed extensional theorems are extentionally provable in every theory. -/
theorem extSetProvable_of_theorem
    {T : ClosedTheorySet} {φ : Sentence}
    (hφ : ExtDerivation.Theorem Primitive φ) :
    ExtSetProvable T φ := by
  refine ⟨[], ?_, hφ⟩
  intro ψ hψ
  cases hψ

/-- Extensional set-provability is monotone in the underlying closed theory. -/
theorem extSetProvable_mono
    {T U : ClosedTheorySet} {φ : Sentence}
    (hTU : ∀ {ψ : Sentence}, ψ ∈ T → ψ ∈ U) :
    ExtSetProvable T φ →
      ExtSetProvable U φ := by
  rintro ⟨Γ, hΓ, hφ⟩
  exact ⟨Γ, by intro ψ hψ; exact hTU (hΓ ψ hψ), hφ⟩

/-- Modus ponens for extensional set-provability. -/
theorem extSetProvable_imp_mp
    {T : ClosedTheorySet} {A B : Sentence}
    (hImp : ExtSetProvable T (imp A B))
    (hA : ExtSetProvable T A) :
    ExtSetProvable T B := by
  rcases hImp with ⟨Γ₁, hΓ₁, hImp⟩
  rcases hA with ⟨Γ₂, hΓ₂, hA⟩
  refine extSetProvable_of_closedTheory (T := T) (Δ := Γ₁ ++ Γ₂) ?_ ?_
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hΓ₁ ψ hψ
    · exact hΓ₂ ψ hψ
  · exact
      .impE
        (ExtDerivation.mono
          (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := imp A B)
          (by
            intro ψ hψ
            exact List.mem_append.mpr (.inl hψ))
          hImp)
        (ExtDerivation.mono
          (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := A)
          (by
            intro ψ hψ
            exact List.mem_append.mpr (.inr hψ))
          hA)

/-- Provable equality of closed terms over a fixed theory. -/
def TermEquivalent (T : ClosedTheorySet) {α : HTy}
    (t u : ClosedTerm α) : Prop :=
  ExtSetProvable T (eq t u)

/-- Reflexivity of provable term equality. -/
theorem termEquivalent_refl
    (T : ClosedTheorySet) {α : HTy} (t : ClosedTerm α) :
    TermEquivalent T t t :=
  extSetProvable_of_theorem (.eqRefl t)

/-- Symmetry of provable term equality. -/
theorem termEquivalent_symm
    {T : ClosedTheorySet} {α : HTy} {t u : ClosedTerm α} :
    TermEquivalent T t u →
      TermEquivalent T u t := by
  rintro ⟨Γ, hΓ, hEq⟩
  exact extSetProvable_of_closedTheory (T := T) (Δ := Γ)
    (by intro ψ hψ; exact hΓ ψ hψ)
    (.eqSymm hEq)

/-- Transitivity of provable term equality. -/
theorem termEquivalent_trans
    {T : ClosedTheorySet} {α : HTy} {t u v : ClosedTerm α} :
    TermEquivalent T t u →
      TermEquivalent T u v →
      TermEquivalent T t v := by
  rintro ⟨Γ₁, hΓ₁, htu⟩ ⟨Γ₂, hΓ₂, huv⟩
  refine extSetProvable_of_closedTheory (T := T) (Δ := Γ₁ ++ Γ₂) ?_ ?_
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hΓ₁ ψ hψ
    · exact hΓ₂ ψ hψ
  · exact
      .eqTrans
        (ExtDerivation.mono
          (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := eq t u)
          (by
            intro ψ hψ
            exact List.mem_append.mpr (.inl hψ))
          htu)
        (ExtDerivation.mono
          (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := eq u v)
          (by
            intro ψ hψ
            exact List.mem_append.mpr (.inr hψ))
          huv)

/-- Application respects provable equivalence classes of functions and
arguments. -/
theorem termEquivalent_app
    {T : ClosedTheorySet} {σ τ : HTy}
    {f g : ClosedTerm (σ ⇒ τ)} {t u : ClosedTerm σ} :
    TermEquivalent T f g →
      TermEquivalent T t u →
      TermEquivalent T (.app f t) (.app g u) := by
  rintro ⟨Γ₁, hΓ₁, hfg⟩ ⟨Γ₂, hΓ₂, htu⟩
  refine extSetProvable_of_closedTheory (T := T) (Δ := Γ₁ ++ Γ₂) ?_ ?_
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hΓ₁ ψ hψ
    · exact hΓ₂ ψ hψ
  · exact
      ExtDerivation.eqAppCongr
        (ExtDerivation.mono
          (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := eq f g)
          (by
            intro ψ hψ
            exact List.mem_append.mpr (.inl hψ))
          hfg)
        (ExtDerivation.mono
          (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := eq t u)
          (by
            intro ψ hψ
            exact List.mem_append.mpr (.inr hψ))
          htu)

/-- The setoid of closed terms of type `α` modulo extensional provable equality
over a closed Henkin theory `T`. -/
def termSetoid (T : ClosedTheorySet) (α : HTy) : Setoid (ClosedTerm α) where
  r := TermEquivalent T
  iseqv :=
    { refl := termEquivalent_refl T
      symm := termEquivalent_symm
      trans := termEquivalent_trans }

/-- The quotient class of closed Henkin terms of type `α` modulo provable
equality over `T`. -/
abbrev TermClass (T : ClosedTheorySet) (α : HTy) :=
  Quotient (termSetoid T α)

/-- The quotient class of a closed term. -/
def classOf {T : ClosedTheorySet} {α : HTy}
    (t : ClosedTerm α) : TermClass T α :=
  Quotient.mk (termSetoid T α) t

/-- Equality of quotient classes is exactly provable term equivalence. -/
theorem classOf_eq_iff
    {T : ClosedTheorySet} {α : HTy} {t u : ClosedTerm α} :
    classOf (T := T) t = classOf u ↔
      TermEquivalent T t u :=
  Quotient.eq

/-- Application descends to quotient classes. -/
def appClass {T : ClosedTheorySet} {σ τ : HTy} :
    TermClass T (σ ⇒ τ) → TermClass T σ → TermClass T τ :=
  Quotient.lift₂
    (fun f t => classOf (T := T) (.app f t))
    (by
      intro f g t u hfg htu
      exact Quotient.sound (termEquivalent_app hfg htu))

@[simp] theorem appClass_classOf
    {T : ClosedTheorySet} {σ τ : HTy}
    (f : ClosedTerm (σ ⇒ τ)) (t : ClosedTerm σ) :
    appClass (T := T) (classOf f) (classOf t) =
      classOf (T := T) (.app f t) :=
  rfl

/-- Positive canary: quotient application respects representatives by
construction. -/
theorem appClass_respects_representatives
    {T : ClosedTheorySet} {σ τ : HTy}
    {f g : ClosedTerm (σ ⇒ τ)} {t u : ClosedTerm σ}
    (hfg : TermEquivalent T f g)
    (htu : TermEquivalent T t u) :
    appClass (T := T) (classOf f) (classOf t) =
      appClass (T := T) (classOf g) (classOf u) := by
  exact congrArg₂ (appClass (T := T))
    ((classOf_eq_iff (T := T)).2 hfg)
    ((classOf_eq_iff (T := T)).2 htu)

end Mettapedia.AutoBooks.Codex.Henkin1950
