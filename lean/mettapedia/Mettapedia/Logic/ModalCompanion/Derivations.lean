import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Propositional.Hilbert.Standard

/-!
# Derivation trees for the intuitionistic, classical and S4 Hilbert calculi

Foundation presents `Propositional.Int`, `Propositional.Cl` and `Modal.S4` as sets of
formulas (inductive predicates), so a Foundation "proof" `L ⊢! φ` of such a logic is a proof
of membership: it carries no derivation. To state proof transformations we need derivations
as data. This file defines them, with assumptions, and relates them to Foundation's systems.

* `PropDeriv cl Γ φ` is a Hilbert derivation of `φ` from the list of assumptions `Γ`, with the
  axioms of Foundation's `Propositional.Int` (minimal logic and ex falso); for `cl = true` the
  law of excluded middle is added, giving `Propositional.Cl`. `IntDeriv` and `ClDeriv` are the
  two instances.
* `S4Deriv Γ φ` is a Hilbert derivation of the modal formula `φ` from assumptions `Γ`, with
  Foundation's classical base (`Axioms.ImplyK`, `Axioms.ImplyS`, `Axioms.ElimContra`), the
  axioms K, T, 4 and the rules of modus ponens and necessitation. Necessitation may be applied
  to any derived formula, so for nonempty `Γ` this is the global consequence relation of S4;
  for `Γ = []` the derivable formulas are exactly the theorems of Foundation's `Modal.S4`.

The wrappers `IntH` and `S4H` make these calculi Foundation entailment systems
(`Entailment.Int` and `Modal.Entailment.S4`), so Foundation's generic combinators produce
derivation trees. The correspondence with Foundation is `IntDeriv.toFiniteContext`,
`IntDeriv.nonempty_of_provable`, `ClDeriv.nonempty_of_provable`, `S4Deriv.provable` and
`S4Deriv.nonempty_of_provable`. Finally `ttVal` is the truth-table value of a propositional
formula and `PropDeriv.ttVal_sound` is soundness of classical derivations for it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalCompanion

open LO LO.Entailment

/-! ## Propositional derivations -/

/-- Hilbert-style derivations of a propositional formula from the assumptions `Γ`, as data.
The axioms are those of Foundation's `Propositional.Int`; `cl = true` adds excluded middle. -/
inductive PropDeriv (cl : Bool) (Γ : List (Propositional.Formula ℕ)) :
    Propositional.Formula ℕ → Type
  | hyp {φ : Propositional.Formula ℕ} : φ ∈ Γ → PropDeriv cl Γ φ
  | efq (φ : Propositional.Formula ℕ) : PropDeriv cl Γ (⊥ ➝ φ)
  | lem (φ : Propositional.Formula ℕ) : cl = true → PropDeriv cl Γ (φ ⋎ ∼φ)
  | implyK (φ ψ : Propositional.Formula ℕ) : PropDeriv cl Γ (φ ➝ ψ ➝ φ)
  | implyS (φ ψ χ : Propositional.Formula ℕ) :
      PropDeriv cl Γ ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ)
  | andElimL (φ ψ : Propositional.Formula ℕ) : PropDeriv cl Γ (φ ⋏ ψ ➝ φ)
  | andElimR (φ ψ : Propositional.Formula ℕ) : PropDeriv cl Γ (φ ⋏ ψ ➝ ψ)
  | andIntro (φ ψ : Propositional.Formula ℕ) : PropDeriv cl Γ (φ ➝ ψ ➝ φ ⋏ ψ)
  | orIntroL (φ ψ : Propositional.Formula ℕ) : PropDeriv cl Γ (φ ➝ φ ⋎ ψ)
  | orIntroR (φ ψ : Propositional.Formula ℕ) : PropDeriv cl Γ (ψ ➝ φ ⋎ ψ)
  | orElim (φ ψ χ : Propositional.Formula ℕ) :
      PropDeriv cl Γ ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ)
  | mdp {φ ψ : Propositional.Formula ℕ} :
      PropDeriv cl Γ (φ ➝ ψ) → PropDeriv cl Γ φ → PropDeriv cl Γ ψ

/-- Intuitionistic derivations from assumptions. -/
abbrev IntDeriv := PropDeriv false

/-- Classical derivations from assumptions. -/
abbrev ClDeriv := PropDeriv true

namespace PropDeriv

variable {cl : Bool}

/-- Replace every assumption by a derivation of it from new assumptions. -/
def cut {Γ Δ : List (Propositional.Formula ℕ)}
    (σ : (ψ : Propositional.Formula ℕ) → ψ ∈ Γ → PropDeriv cl Δ ψ) :
    {φ : Propositional.Formula ℕ} → PropDeriv cl Γ φ → PropDeriv cl Δ φ
  | _, hyp h => σ _ h
  | _, efq φ => efq φ
  | _, lem φ h => lem φ h
  | _, implyK φ ψ => implyK φ ψ
  | _, implyS φ ψ χ => implyS φ ψ χ
  | _, andElimL φ ψ => andElimL φ ψ
  | _, andElimR φ ψ => andElimR φ ψ
  | _, andIntro φ ψ => andIntro φ ψ
  | _, orIntroL φ ψ => orIntroL φ ψ
  | _, orIntroR φ ψ => orIntroR φ ψ
  | _, orElim φ ψ χ => orElim φ ψ χ
  | _, mdp d₁ d₂ => mdp (cut σ d₁) (cut σ d₂)

/-- Weakening of the assumptions. -/
def weaken {Γ Δ : List (Propositional.Formula ℕ)} (h : Γ ⊆ Δ)
    {φ : Propositional.Formula ℕ} (d : PropDeriv cl Γ φ) : PropDeriv cl Δ φ :=
  cut (fun _ hψ => hyp (h hψ)) d

/-- The derivation `φ ➝ φ` from `S` and `K`. -/
def selfImp {Γ : List (Propositional.Formula ℕ)} (φ : Propositional.Formula ℕ) :
    PropDeriv cl Γ (φ ➝ φ) :=
  mdp (mdp (implyS φ (φ ➝ φ) φ) (implyK φ (φ ➝ φ))) (implyK φ φ)

/-- The deduction theorem, as an operation on derivations. -/
def deduct {Γ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ} :
    {ψ : Propositional.Formula ℕ} → PropDeriv cl (φ :: Γ) ψ → PropDeriv cl Γ (φ ➝ ψ)
  | ψ, hyp h =>
    if e : ψ = φ then by subst e; exact selfImp ψ
    else mdp (implyK ψ φ) (hyp ((List.mem_cons.mp h).resolve_left e))
  | _, efq χ => mdp (implyK _ φ) (efq χ)
  | _, lem χ h => mdp (implyK _ φ) (lem χ h)
  | _, implyK χ ξ => mdp (implyK _ φ) (implyK χ ξ)
  | _, implyS χ ξ ζ => mdp (implyK _ φ) (implyS χ ξ ζ)
  | _, andElimL χ ξ => mdp (implyK _ φ) (andElimL χ ξ)
  | _, andElimR χ ξ => mdp (implyK _ φ) (andElimR χ ξ)
  | _, andIntro χ ξ => mdp (implyK _ φ) (andIntro χ ξ)
  | _, orIntroL χ ξ => mdp (implyK _ φ) (orIntroL χ ξ)
  | _, orIntroR χ ξ => mdp (implyK _ φ) (orIntroR χ ξ)
  | _, orElim χ ξ ζ => mdp (implyK _ φ) (orElim χ ξ ζ)
  | _, mdp d₁ d₂ => mdp (mdp (implyS _ _ _) (deduct d₁)) (deduct d₂)

/-- Every intuitionistic derivation is a classical derivation. -/
def toCl {Γ : List (Propositional.Formula ℕ)} :
    {φ : Propositional.Formula ℕ} → IntDeriv Γ φ → ClDeriv Γ φ
  | _, hyp h => hyp h
  | _, efq φ => efq φ
  | _, lem _ h => nomatch h
  | _, implyK φ ψ => implyK φ ψ
  | _, implyS φ ψ χ => implyS φ ψ χ
  | _, andElimL φ ψ => andElimL φ ψ
  | _, andElimR φ ψ => andElimR φ ψ
  | _, andIntro φ ψ => andIntro φ ψ
  | _, orIntroL φ ψ => orIntroL φ ψ
  | _, orIntroR φ ψ => orIntroR φ ψ
  | _, orElim φ ψ χ => orElim φ ψ χ
  | _, mdp d₁ d₂ => mdp (toCl d₁) (toCl d₂)

end PropDeriv

/-! ## Truth tables -/

/-- Truth-table value of a propositional formula under a Boolean valuation of its atoms. -/
def ttVal (v : ℕ → Bool) : Propositional.Formula ℕ → Bool
  | .atom a => v a
  | .falsum => false
  | .and φ ψ => ttVal v φ && ttVal v ψ
  | .or φ ψ => ttVal v φ || ttVal v ψ
  | .imp φ ψ => !ttVal v φ || ttVal v ψ

@[simp] theorem ttVal_atom (v : ℕ → Bool) (a : ℕ) :
    ttVal v (.atom a) = v a := rfl
@[simp] theorem ttVal_bot (v : ℕ → Bool) : ttVal v ⊥ = false := rfl
@[simp] theorem ttVal_and (v : ℕ → Bool) (φ ψ : Propositional.Formula ℕ) :
    ttVal v (φ ⋏ ψ) = (ttVal v φ && ttVal v ψ) := rfl
@[simp] theorem ttVal_or (v : ℕ → Bool) (φ ψ : Propositional.Formula ℕ) :
    ttVal v (φ ⋎ ψ) = (ttVal v φ || ttVal v ψ) := rfl
@[simp] theorem ttVal_imp (v : ℕ → Bool) (φ ψ : Propositional.Formula ℕ) :
    ttVal v (φ ➝ ψ) = (!ttVal v φ || ttVal v ψ) := rfl
@[simp] theorem ttVal_neg (v : ℕ → Bool) (φ : Propositional.Formula ℕ) :
    ttVal v (∼φ) = !ttVal v φ := by
  change (!ttVal v φ || false) = !ttVal v φ
  cases ttVal v φ <;> rfl

/-- Truth-table soundness of classical (hence of intuitionistic) derivations. -/
theorem PropDeriv.ttVal_sound {cl : Bool} {Γ : List (Propositional.Formula ℕ)}
    (v : ℕ → Bool) (hΓ : ∀ γ ∈ Γ, ttVal v γ = true) :
    {φ : Propositional.Formula ℕ} → PropDeriv cl Γ φ → ttVal v φ = true
  | _, .hyp h => hΓ _ h
  | _, .efq _ => rfl
  | _, .lem φ _ => by simp only [ttVal_or, ttVal_neg]; cases ttVal v φ <;> rfl
  | _, .implyK φ ψ => by
    simp only [ttVal_imp]; cases ttVal v φ <;> cases ttVal v ψ <;> rfl
  | _, .implyS φ ψ χ => by
    simp only [ttVal_imp]
    cases ttVal v φ <;> cases ttVal v ψ <;> cases ttVal v χ <;> rfl
  | _, .andElimL φ ψ => by
    simp only [ttVal_imp, ttVal_and]; cases ttVal v φ <;> cases ttVal v ψ <;> rfl
  | _, .andElimR φ ψ => by
    simp only [ttVal_imp, ttVal_and]; cases ttVal v φ <;> cases ttVal v ψ <;> rfl
  | _, .andIntro φ ψ => by
    simp only [ttVal_imp, ttVal_and]; cases ttVal v φ <;> cases ttVal v ψ <;> rfl
  | _, .orIntroL φ ψ => by
    simp only [ttVal_imp, ttVal_or]; cases ttVal v φ <;> cases ttVal v ψ <;> rfl
  | _, .orIntroR φ ψ => by
    simp only [ttVal_imp, ttVal_or]; cases ttVal v φ <;> cases ttVal v ψ <;> rfl
  | _, .orElim φ ψ χ => by
    simp only [ttVal_imp, ttVal_or]
    cases ttVal v φ <;> cases ttVal v ψ <;> cases ttVal v χ <;> rfl
  | _, .mdp (φ := φ) d₁ d₂ => by
    have h₁ := PropDeriv.ttVal_sound v hΓ d₁
    have h₂ := PropDeriv.ttVal_sound v hΓ d₂
    simp only [ttVal_imp] at h₁
    rw [h₂] at h₁
    exact h₁

/-! ## The intuitionistic calculus as a Foundation entailment system -/

/-- The intuitionistic Hilbert calculus over the assumptions `hyps`; its proofs are the
derivation trees `IntDeriv hyps`. -/
structure IntH where
  /-- The assumptions. -/
  hyps : List (Propositional.Formula ℕ)

instance : Entailment IntH (Propositional.Formula ℕ) :=
  ⟨fun 𝓢 φ => IntDeriv 𝓢.hyps φ⟩

instance (𝓢 : IntH) : Entailment.Int 𝓢 where
  mdp := PropDeriv.mdp
  negEquiv {φ} := PropDeriv.mdp (PropDeriv.mdp (PropDeriv.andIntro (∼φ ➝ (φ ➝ ⊥)) _)
    (PropDeriv.selfImp (φ ➝ ⊥))) (PropDeriv.selfImp (φ ➝ ⊥))
  verum := PropDeriv.efq ⊥
  implyK := PropDeriv.implyK _ _
  implyS := PropDeriv.implyS _ _ _
  and₁ := PropDeriv.andElimL _ _
  and₂ := PropDeriv.andElimR _ _
  and₃ := PropDeriv.andIntro _ _
  or₁ := PropDeriv.orIntroL _ _
  or₂ := PropDeriv.orIntroR _ _
  or₃ := PropDeriv.orElim _ _ _
  efq := PropDeriv.efq _

/-! ## Agreement with Foundation's `Propositional.Int` and `Propositional.Cl` -/

/-- A derivation from assumptions `Γ` gives a Foundation proof in `Propositional.Int` from the
finite context `Γ`. -/
def IntDeriv.toFiniteContext {Γ : List (Propositional.Formula ℕ)} :
    {φ : Propositional.Formula ℕ} → IntDeriv Γ φ → Γ ⊢[Propositional.Int]! φ
  | _, .hyp h => FiniteContext.byAxm h
  | _, .efq _ => FiniteContext.of efq
  | _, .lem _ h => nomatch h
  | _, .implyK _ _ => FiniteContext.of implyK
  | _, .implyS _ _ _ => FiniteContext.of implyS
  | _, .andElimL _ _ => FiniteContext.of and₁
  | _, .andElimR _ _ => FiniteContext.of and₂
  | _, .andIntro _ _ => FiniteContext.of and₃
  | _, .orIntroL _ _ => FiniteContext.of or₁
  | _, .orIntroR _ _ => FiniteContext.of or₂
  | _, .orElim _ _ _ => FiniteContext.of or₃
  | _, .mdp d₁ d₂ => IntDeriv.toFiniteContext d₁ ⨀ IntDeriv.toFiniteContext d₂

/-- A closed intuitionistic derivation proves its conclusion in Foundation's
`Propositional.Int`. -/
theorem IntDeriv.provable {φ : Propositional.Formula ℕ} (d : IntDeriv [] φ) :
    Propositional.Int ⊢ φ :=
  ⟨FiniteContext.emptyPrf d.toFiniteContext⟩

/-- Every theorem of Foundation's `Propositional.Int` has a derivation tree. -/
theorem IntDeriv.nonempty_of_provable {φ : Propositional.Formula ℕ}
    (h : Propositional.Int ⊢ φ) : Nonempty (IntDeriv [] φ) := by
  obtain ⟨⟨hφ⟩⟩ := h
  induction hφ with
  | axm s hax =>
    cases hax
    exact ⟨PropDeriv.efq (s 0)⟩
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨d₁⟩ := ih₁
    obtain ⟨d₂⟩ := ih₂
    exact ⟨PropDeriv.mdp d₁ d₂⟩
  | verum => exact ⟨PropDeriv.efq ⊥⟩
  | implyS φ ψ => exact ⟨PropDeriv.implyK φ ψ⟩
  | implyK φ ψ χ => exact ⟨PropDeriv.implyS φ ψ χ⟩
  | andElimL φ ψ => exact ⟨PropDeriv.andElimL φ ψ⟩
  | andElimR φ ψ => exact ⟨PropDeriv.andElimR φ ψ⟩
  | andIntro φ ψ => exact ⟨PropDeriv.andIntro φ ψ⟩
  | orIntroL φ ψ => exact ⟨PropDeriv.orIntroL φ ψ⟩
  | orIntroR φ ψ => exact ⟨PropDeriv.orIntroR φ ψ⟩
  | orElim φ ψ χ => exact ⟨PropDeriv.orElim φ ψ χ⟩

/-- Every theorem of Foundation's `Propositional.Cl` has a classical derivation tree. -/
theorem ClDeriv.nonempty_of_provable {φ : Propositional.Formula ℕ}
    (h : Propositional.Cl ⊢ φ) : Nonempty (ClDeriv [] φ) := by
  obtain ⟨⟨hφ⟩⟩ := h
  induction hφ with
  | axm s hax =>
    rcases hax with hax | hax
    · cases hax
      exact ⟨PropDeriv.efq (s 0)⟩
    · cases hax
      exact ⟨PropDeriv.lem (s 0) rfl⟩
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨d₁⟩ := ih₁
    obtain ⟨d₂⟩ := ih₂
    exact ⟨PropDeriv.mdp d₁ d₂⟩
  | verum => exact ⟨PropDeriv.efq ⊥⟩
  | implyS φ ψ => exact ⟨PropDeriv.implyK φ ψ⟩
  | implyK φ ψ χ => exact ⟨PropDeriv.implyS φ ψ χ⟩
  | andElimL φ ψ => exact ⟨PropDeriv.andElimL φ ψ⟩
  | andElimR φ ψ => exact ⟨PropDeriv.andElimR φ ψ⟩
  | andIntro φ ψ => exact ⟨PropDeriv.andIntro φ ψ⟩
  | orIntroL φ ψ => exact ⟨PropDeriv.orIntroL φ ψ⟩
  | orIntroR φ ψ => exact ⟨PropDeriv.orIntroR φ ψ⟩
  | orElim φ ψ χ => exact ⟨PropDeriv.orElim φ ψ χ⟩

/-! ## S4 derivations -/

/-- Decidable equality of modal formulas by constructor injectivity. Foundation's instance
decides the same relation but proves its negative cases with classical tactics; the scoped
instance below keeps the computations of this development free of `Classical.choice`. -/
def modalFormulaDecEq : (φ ψ : Modal.Formula ℕ) → Decidable (φ = ψ)
  | .atom a, .atom b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .falsum, .falsum => isTrue rfl
  | .imp φ ψ, .imp φ' ψ' =>
    match modalFormulaDecEq φ φ', modalFormulaDecEq ψ ψ' with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h₁, _ => isFalse fun e => h₁ (by cases e; rfl)
    | _, isFalse h₂ => isFalse fun e => h₂ (by cases e; rfl)
  | .box φ, .box φ' =>
    match modalFormulaDecEq φ φ' with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (by cases e; rfl)
  | .atom _, .falsum => isFalse fun e => by cases e
  | .atom _, .imp _ _ => isFalse fun e => by cases e
  | .atom _, .box _ => isFalse fun e => by cases e
  | .falsum, .atom _ => isFalse fun e => by cases e
  | .falsum, .imp _ _ => isFalse fun e => by cases e
  | .falsum, .box _ => isFalse fun e => by cases e
  | .imp _ _, .atom _ => isFalse fun e => by cases e
  | .imp _ _, .falsum => isFalse fun e => by cases e
  | .imp _ _, .box _ => isFalse fun e => by cases e
  | .box _, .atom _ => isFalse fun e => by cases e
  | .box _, .falsum => isFalse fun e => by cases e
  | .box _, .imp _ _ => isFalse fun e => by cases e

scoped instance (priority := high) : DecidableEq (Modal.Formula ℕ) := modalFormulaDecEq

/-- Hilbert-style derivations of a modal formula from the assumptions `Γ` in S4, as data.
The classical base is Foundation's (`Axioms.ImplyK`, `Axioms.ImplyS`, `Axioms.ElimContra`,
over `⊥`, `➝` and `□`); necessitation applies to every derived formula. -/
inductive S4Deriv (Γ : List (Modal.Formula ℕ)) : Modal.Formula ℕ → Type
  | hyp {φ : Modal.Formula ℕ} : φ ∈ Γ → S4Deriv Γ φ
  | implyK (φ ψ : Modal.Formula ℕ) : S4Deriv Γ (φ ➝ ψ ➝ φ)
  | implyS (φ ψ χ : Modal.Formula ℕ) : S4Deriv Γ ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ)
  | elimContra (φ ψ : Modal.Formula ℕ) : S4Deriv Γ ((∼ψ ➝ ∼φ) ➝ (φ ➝ ψ))
  | axiomK (φ ψ : Modal.Formula ℕ) : S4Deriv Γ (□(φ ➝ ψ) ➝ □φ ➝ □ψ)
  | axiomT (φ : Modal.Formula ℕ) : S4Deriv Γ (□φ ➝ φ)
  | axiomFour (φ : Modal.Formula ℕ) : S4Deriv Γ (□φ ➝ □□φ)
  | mdp {φ ψ : Modal.Formula ℕ} : S4Deriv Γ (φ ➝ ψ) → S4Deriv Γ φ → S4Deriv Γ ψ
  | nec {φ : Modal.Formula ℕ} : S4Deriv Γ φ → S4Deriv Γ (□φ)

/-- Substitution of formulas for atoms in a closed S4 derivation. -/
def S4Deriv.subst (s : Modal.Substitution ℕ) :
    {φ : Modal.Formula ℕ} → S4Deriv [] φ → S4Deriv [] (φ⟦s⟧)
  | _, .hyp h => absurd h List.not_mem_nil
  | _, .implyK φ ψ => .implyK (φ⟦s⟧) (ψ⟦s⟧)
  | _, .implyS φ ψ χ => .implyS (φ⟦s⟧) (ψ⟦s⟧) (χ⟦s⟧)
  | _, .elimContra φ ψ => .elimContra (φ⟦s⟧) (ψ⟦s⟧)
  | _, .axiomK φ ψ => .axiomK (φ⟦s⟧) (ψ⟦s⟧)
  | _, .axiomT φ => .axiomT (φ⟦s⟧)
  | _, .axiomFour φ => .axiomFour (φ⟦s⟧)
  | _, .mdp d₁ d₂ => .mdp (S4Deriv.subst s d₁) (S4Deriv.subst s d₂)
  | _, .nec d => .nec (S4Deriv.subst s d)

/-- The S4 Hilbert calculus over the assumptions `hyps`; its proofs are the derivation trees
`S4Deriv hyps`. -/
structure S4H where
  /-- The assumptions. -/
  hyps : List (Modal.Formula ℕ)

instance : Entailment S4H (Modal.Formula ℕ) := ⟨fun 𝓢 φ => S4Deriv 𝓢.hyps φ⟩

instance (𝓢 : S4H) : Entailment.Łukasiewicz 𝓢 where
  mdp := S4Deriv.mdp
  implyK := S4Deriv.implyK _ _
  implyS := S4Deriv.implyS _ _ _
  elimContra := S4Deriv.elimContra _ _

instance (𝓢 : S4H) : Modal.Entailment.Necessitation 𝓢 := ⟨S4Deriv.nec⟩
instance (𝓢 : S4H) : Modal.Entailment.HasAxiomK 𝓢 := ⟨S4Deriv.axiomK⟩
instance (𝓢 : S4H) : Modal.Entailment.HasAxiomT 𝓢 := ⟨S4Deriv.axiomT⟩
instance (𝓢 : S4H) : Modal.Entailment.HasAxiomFour 𝓢 := ⟨S4Deriv.axiomFour⟩
instance (𝓢 : S4H) : Modal.Entailment.S4 𝓢 where

/-! ## Agreement with Foundation's `Modal.S4` -/

/-- A closed S4 derivation proves its conclusion in Foundation's `Modal.S4`. The axioms K, T
and 4 are obtained as substitution instances of Foundation's axiom schemata. -/
theorem S4Deriv.provable : {φ : Modal.Formula ℕ} → S4Deriv [] φ → Modal.S4 ⊢ φ
  | _, .hyp h => absurd h List.not_mem_nil
  | _, .implyK φ ψ => ⟨⟨Modal.Hilbert.Normal.implyK φ ψ⟩⟩
  | _, .implyS φ ψ χ => ⟨⟨Modal.Hilbert.Normal.implyS φ ψ χ⟩⟩
  | _, .elimContra φ ψ => ⟨⟨Modal.Hilbert.Normal.ec φ ψ⟩⟩
  | _, .axiomK φ ψ =>
    ⟨⟨Modal.Hilbert.Normal.axm (φ := Modal.Axioms.K (.atom 0) (.atom 1))
      (fun n => if n = 0 then φ else ψ) (Or.inl rfl)⟩⟩
  | _, .axiomT φ =>
    ⟨⟨Modal.Hilbert.Normal.axm (φ := Modal.Axioms.T (.atom 0))
      (fun _ => φ) (Or.inr (Or.inl rfl))⟩⟩
  | _, .axiomFour φ =>
    ⟨⟨Modal.Hilbert.Normal.axm (φ := Modal.Axioms.Four (.atom 0))
      (fun _ => φ) (Or.inr (Or.inr rfl))⟩⟩
  | _, .mdp d₁ d₂ => by
    obtain ⟨⟨h₁⟩⟩ := S4Deriv.provable d₁
    obtain ⟨⟨h₂⟩⟩ := S4Deriv.provable d₂
    exact ⟨⟨Modal.Hilbert.Normal.mdp h₁ h₂⟩⟩
  | _, .nec d => by
    obtain ⟨⟨h⟩⟩ := S4Deriv.provable d
    exact ⟨⟨Modal.Hilbert.Normal.nec h⟩⟩

/-- Every theorem of Foundation's `Modal.S4` has a derivation tree. -/
theorem S4Deriv.nonempty_of_provable {φ : Modal.Formula ℕ} (h : Modal.S4 ⊢ φ) :
    Nonempty (S4Deriv [] φ) := by
  obtain ⟨⟨hφ⟩⟩ := h
  induction hφ with
  | axm s hax =>
    rcases hax with hax | hax | hax
    · cases hax
      exact ⟨S4Deriv.axiomK (s 0) (s 1)⟩
    · cases hax
      exact ⟨S4Deriv.axiomT (s 0)⟩
    · cases hax
      exact ⟨S4Deriv.axiomFour (s 0)⟩
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨d₁⟩ := ih₁
    obtain ⟨d₂⟩ := ih₂
    exact ⟨S4Deriv.mdp d₁ d₂⟩
  | nec _ ih =>
    obtain ⟨d⟩ := ih
    exact ⟨S4Deriv.nec d⟩
  | implyK φ ψ => exact ⟨S4Deriv.implyK φ ψ⟩
  | implyS φ ψ χ => exact ⟨S4Deriv.implyS φ ψ χ⟩
  | ec φ ψ => exact ⟨S4Deriv.elimContra φ ψ⟩

end Mettapedia.Logic.ModalCompanion
