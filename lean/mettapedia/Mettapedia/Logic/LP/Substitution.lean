import Mettapedia.Logic.LP.Core

/-!
# Logic Programming Kernel: Substitutions

First-order substitutions over LP signatures.  A substitution maps variables
to terms; applying it structurally replaces each variable occurrence.

## Design

- `Subst σ := σ.vars → Term σ` — total function (identity on unmapped vars).
- `Subst.id = Term.var` — the identity substitution.
- `Subst.applyTerm` — structural recursion on terms.
- `Subst.comp` — composition: `(θ₁ ∘ θ₂) v = θ₁.applyTerm (θ₂ v)`.
- `Subst.moreGeneral` — θ₁ ≤ θ₂ iff ∃ θ₃, θ₂ = θ₃ ∘ θ₁ (preorder on substitutions).
- `Grounding σ := σ.vars → GroundTerm σ` — total ground substitution (for T_P).

## References

- Lloyd, *Foundations of Logic Programming*, Ch. 1–2
- Robinson, "A Machine-Oriented Logic", 1965
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Substitutions -/

/-- A first-order substitution: maps variables to terms. -/
def Subst (σ : LPSignature) := σ.vars → Term σ

/-- The identity substitution (each variable maps to itself). -/
def Subst.id (σ : LPSignature) : Subst σ := Term.var

/-- Apply a substitution to a term (structural recursion). -/
def Subst.applyTerm {σ : LPSignature} (θ : Subst σ) : Term σ → Term σ
  | .var v    => θ v
  | .const c  => .const c
  | .app f ts => .app f (fun i => θ.applyTerm (ts i))

/-- Apply a substitution to an atom. -/
def Subst.applyAtom {σ : LPSignature} (θ : Subst σ) (a : Atom σ) : Atom σ where
  symbol := a.symbol
  args   := fun i => θ.applyTerm (a.args i)

/-- Apply a substitution to a list of atoms (e.g., a clause body / goal list). -/
def Subst.applyAtoms {σ : LPSignature} (θ : Subst σ) (as : List (Atom σ)) : List (Atom σ) :=
  as.map θ.applyAtom

/-- Composition of substitutions: `(θ₁ ∘ θ₂) v = θ₁.applyTerm (θ₂ v)`. -/
def Subst.comp {σ : LPSignature} (θ₁ θ₂ : Subst σ) : Subst σ :=
  fun v => θ₁.applyTerm (θ₂ v)

infixl:90 " ∘ₛ " => Subst.comp

/-! ## Section 2: Identity laws -/

@[simp]
theorem Subst.applyTerm_var {σ : LPSignature} (θ : Subst σ) (v : σ.vars) :
    θ.applyTerm (.var v) = θ v := rfl

@[simp]
theorem Subst.applyTerm_const {σ : LPSignature} (θ : Subst σ) (c : σ.constants) :
    θ.applyTerm (.const c) = .const c := rfl

@[simp]
theorem Subst.applyTerm_app {σ : LPSignature} (θ : Subst σ) (f : σ.functionSymbols)
    (ts : Fin (σ.functionArity f) → Term σ) :
    θ.applyTerm (.app f ts) = .app f (fun i => θ.applyTerm (ts i)) := rfl

theorem Subst.applyTerm_id {σ : LPSignature} (t : Term σ) :
    (Subst.id σ).applyTerm t = t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f ts ih => simp [Subst.applyTerm, ih]

@[simp]
theorem Subst.applyAtom_id {σ : LPSignature} (a : Atom σ) :
    (Subst.id σ).applyAtom a = a := by
  ext
  · rfl
  · simp [Subst.applyAtom, Subst.applyTerm_id]

theorem Subst.applyAtoms_id {σ : LPSignature} (as : List (Atom σ)) :
    (Subst.id σ).applyAtoms as = as := by
  simp [Subst.applyAtoms, show (Subst.id σ).applyAtom = _root_.id from funext applyAtom_id]

/-! ## Section 3: Composition laws -/

theorem Subst.applyTerm_comp {σ : LPSignature} (θ₁ θ₂ : Subst σ) (t : Term σ) :
    (θ₁ ∘ₛ θ₂).applyTerm t = θ₁.applyTerm (θ₂.applyTerm t) := by
  induction t with
  | var v => rfl
  | const _ => rfl
  | app f ts ih => simp [Subst.applyTerm, ih]

theorem Subst.applyAtom_comp {σ : LPSignature} (θ₁ θ₂ : Subst σ) (a : Atom σ) :
    (θ₁ ∘ₛ θ₂).applyAtom a = θ₁.applyAtom (θ₂.applyAtom a) := by
  simp [Subst.applyAtom, Subst.applyTerm_comp]

theorem Subst.applyAtoms_comp {σ : LPSignature} (θ₁ θ₂ : Subst σ) (as : List (Atom σ)) :
    (θ₁ ∘ₛ θ₂).applyAtoms as = θ₁.applyAtoms (θ₂.applyAtoms as) := by
  simp [Subst.applyAtoms, Subst.applyAtom_comp, List.map_map]

theorem Subst.comp_assoc {σ : LPSignature} (θ₁ θ₂ θ₃ : Subst σ) :
    (θ₁ ∘ₛ θ₂) ∘ₛ θ₃ = θ₁ ∘ₛ (θ₂ ∘ₛ θ₃) := by
  funext v
  simp [Subst.comp, Subst.applyTerm_comp]

theorem Subst.comp_id_right {σ : LPSignature} (θ : Subst σ) :
    θ ∘ₛ Subst.id σ = θ := by
  funext v; rfl

theorem Subst.comp_id_left {σ : LPSignature} (θ : Subst σ) :
    Subst.id σ ∘ₛ θ = θ := by
  funext v
  simp [Subst.comp, Subst.applyTerm_id]

/-! ## Section 4: Single-variable substitution -/

/-- Substitute a single variable, leaving others unchanged. -/
def Subst.single {σ : LPSignature} [DecidableEq σ.vars] (v : σ.vars) (t : Term σ) : Subst σ :=
  fun w => if w = v then t else .var w

theorem Subst.single_eq {σ : LPSignature} [DecidableEq σ.vars] (v : σ.vars) (t : Term σ) :
    Subst.single v t v = t := by
  simp [Subst.single]

theorem Subst.single_ne {σ : LPSignature} [DecidableEq σ.vars]
    {v w : σ.vars} (t : Term σ) (h : w ≠ v) :
    Subst.single v t w = .var w := by
  simp [Subst.single, h]

/-! ## Section 5: Generality ordering -/

/-- θ₁ is more general than θ₂ if there exists θ₃ such that θ₂ = θ₃ ∘ θ₁. -/
def Subst.moreGeneral {σ : LPSignature} (θ₁ θ₂ : Subst σ) : Prop :=
  ∃ θ₃ : Subst σ, ∀ v, θ₂ v = θ₃.applyTerm (θ₁ v)

theorem Subst.moreGeneral_refl {σ : LPSignature} (θ : Subst σ) :
    θ.moreGeneral θ := by
  exact ⟨Subst.id σ, fun v => (Subst.applyTerm_id (θ v)).symm⟩

theorem Subst.moreGeneral_trans {σ : LPSignature} {θ₁ θ₂ θ₃ : Subst σ}
    (h₁₂ : θ₁.moreGeneral θ₂) (h₂₃ : θ₂.moreGeneral θ₃) :
    θ₁.moreGeneral θ₃ := by
  obtain ⟨δ₁, hδ₁⟩ := h₁₂
  obtain ⟨δ₂, hδ₂⟩ := h₂₃
  exact ⟨δ₂ ∘ₛ δ₁, fun v => by rw [hδ₂ v, hδ₁ v, Subst.applyTerm_comp]⟩

theorem Subst.id_moreGeneral {σ : LPSignature} (θ : Subst σ) :
    (Subst.id σ).moreGeneral θ :=
  ⟨θ, fun _ => rfl⟩

/-! ## Section 6: Ground substitutions -/

/-- A ground substitution: maps variables to ground terms. -/
def Grounding (σ : LPSignature) := σ.vars → GroundTerm σ

/-- Convert a grounding to a general substitution. -/
def Grounding.toSubst {σ : LPSignature} (g : Grounding σ) : Subst σ :=
  fun v => (g v).toTerm

/-- Apply a grounding to a term, yielding a ground term.
    Requires the term to be ground (all variables are mapped). -/
def Grounding.applyTerm {σ : LPSignature} (g : Grounding σ) : Term σ → Term σ :=
  g.toSubst.applyTerm

/-- Apply a grounding to an atom. -/
def Grounding.applyAtom {σ : LPSignature} (g : Grounding σ) (a : Atom σ) : Atom σ :=
  g.toSubst.applyAtom a

/-- A grounding applied to any term produces a ground term. -/
theorem Grounding.applyTerm_isGround {σ : LPSignature} (g : Grounding σ) (t : Term σ) :
    (g.applyTerm t).isGround := by
  induction t with
  | var v => exact GroundTerm.toTerm_isGround (g v)
  | const _ => exact trivial
  | app f ts ih => exact fun i => ih i

/-- A grounding applied to any atom produces a ground atom. -/
theorem Grounding.applyAtom_isGround {σ : LPSignature} (g : Grounding σ) (a : Atom σ) :
    (g.applyAtom a).isGround :=
  fun i => g.applyTerm_isGround (a.args i)

/-! ## Section 7: Substitution preserves list length -/

@[simp]
theorem Subst.applyAtoms_length {σ : LPSignature} (θ : Subst σ) (as : List (Atom σ)) :
    (θ.applyAtoms as).length = as.length := by
  simp [Subst.applyAtoms]

/-! ## Section 8: Ground body satisfaction -/

/-- A list of ground atoms is satisfied by an interpretation when every atom is in it. -/
def groundBodySatisfied {σ : LPSignature}
    (body : List (GroundAtom σ)) (I : Interpretation σ) : Prop :=
  ∀ a ∈ body, a ∈ I

/-- Satisfaction is monotone: larger interpretations satisfy more bodies. -/
theorem groundBodySatisfied_mono {σ : LPSignature}
    (body : List (GroundAtom σ)) {I J : Interpretation σ} (hIJ : I ⊆ J)
    (h : groundBodySatisfied body I) : groundBodySatisfied body J :=
  fun a ha => hIJ (h a ha)

end Mettapedia.Logic.LP
