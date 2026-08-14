import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical.Frame

/-!
# Recursive canonical forcing and truth bridges

Recursive and level-indexed canonical forcing over supported presented worlds,
together with the closed and open truth-bridge clauses that connect recursive
forcing back to membership where the bridge is supported.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin

namespace SupportedCanonicalFrame

open ClosedTheorySet

/-! ## Recursive canonical forcing -/

/-- Recursive Kripke forcing over supported presented canonical worlds.

Atomic formulas and equality are read from the world's closed carrier, while
logical structure is interpreted by the usual substitutional Kripke clauses.
This is separate from membership forcing: the eventual canonical truth lemma is
the theorem that the two readings agree at the supported formulas needed for
completeness. -/
def RecursiveForcesOpen :
    {Γ : Ctx Base} →
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const →
        Formula (WithParams Const) Γ → ClosedEnv (WithParams Const) Γ → Prop
  | _, W, .var v, ρ => Atom (Base := Base) (Const := Const) W (subst ρ (.var v))
  | _, W, .const c, ρ => Atom (Base := Base) (Const := Const) W (subst ρ (.const c))
  | _, W, .app f t, ρ => Atom (Base := Base) (Const := Const) W (subst ρ (.app f t))
  | _, W, .eq s t, ρ => EqVal (Base := Base) (Const := Const) W (subst ρ s) (subst ρ t)
  | _, _W, .top, _ρ => True
  | _, _W, .bot, _ρ => False
  | _, W, .and φ ψ, ρ => RecursiveForcesOpen W φ ρ ∧ RecursiveForcesOpen W ψ ρ
  | _, W, .or φ ψ, ρ => RecursiveForcesOpen W φ ρ ∨ RecursiveForcesOpen W ψ ρ
  | _, W, .imp φ ψ, ρ =>
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          RecursiveForcesOpen V φ ρ → RecursiveForcesOpen V ψ ρ
  | _, W, .not φ, ρ =>
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → ¬ RecursiveForcesOpen V φ ρ
  | _, W, .all φ, ρ =>
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) _,
            RecursiveForcesOpen V φ (ClosedEnv.extend (Base := Base) ρ t)
  | _, W, .ex φ, ρ =>
      ∃ t : ClosedTerm (WithParams Const) _,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            RecursiveForcesOpen V φ (ClosedEnv.extend (Base := Base) ρ t)
termination_by _Γ _W φ _ρ => sizeOf φ

/-- Closed-formula specialization of recursive canonical forcing. -/
def RecursiveForces
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  RecursiveForcesOpen (Base := Base) (Const := Const) W φ
    (ClosedEnv.empty (Base := Base) (Const := WithParams Const))

/-- Recursive forcing depends only on the closed terms assigned by the
environment, not on the particular function representing that assignment. -/
theorem recursiveForcesOpen_env_ext
    {Γ : Ctx Base}
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {ρ ρ' : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    (hρ : ∀ {τ : Ty Base} (v : Var Γ τ), ρ v = ρ' v)
    (φ : Formula (WithParams Const) Γ) :
    RecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ ↔
      RecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ' := by
  cases φ with
  | var v =>
      simp [RecursiveForcesOpen, hρ v]
  | const c =>
      simp [RecursiveForcesOpen, subst]
  | app f t =>
      have hsubst : subst (Base := Base) (Const := WithParams Const) ρ (.app f t) =
          subst (Base := Base) (Const := WithParams Const) ρ' (.app f t) := by
        exact subst_ext (Base := Base) (Const := WithParams Const)
          (σs := ρ) (τs := ρ') hρ (.app f t)
      simp [RecursiveForcesOpen, hsubst]
  | top =>
      simp [RecursiveForcesOpen]
  | bot =>
      simp [RecursiveForcesOpen]
  | and φ ψ =>
      simp [RecursiveForcesOpen,
        (recursiveForcesOpen_env_ext (W := W) hρ φ),
        (recursiveForcesOpen_env_ext (W := W) hρ ψ)]
  | or φ ψ =>
      simp [RecursiveForcesOpen,
        (recursiveForcesOpen_env_ext (W := W) hρ φ),
        (recursiveForcesOpen_env_ext (W := W) hρ ψ)]
  | imp φ ψ =>
      simp [RecursiveForcesOpen]
      constructor
      · intro h V hWV hφ
        exact (recursiveForcesOpen_env_ext (W := V) hρ ψ).mp
          (h V hWV ((recursiveForcesOpen_env_ext (W := V) hρ φ).mpr hφ))
      · intro h V hWV hφ
        exact (recursiveForcesOpen_env_ext (W := V) hρ ψ).mpr
          (h V hWV ((recursiveForcesOpen_env_ext (W := V) hρ φ).mp hφ))
  | not φ =>
      simp [RecursiveForcesOpen]
      constructor
      · intro h V hWV hφ
        exact h V hWV ((recursiveForcesOpen_env_ext (W := V) hρ φ).mpr hφ)
      · intro h V hWV hφ
        exact h V hWV ((recursiveForcesOpen_env_ext (W := V) hρ φ).mp hφ)
  | eq s t =>
      have hs : subst (Base := Base) (Const := WithParams Const) ρ s =
          subst (Base := Base) (Const := WithParams Const) ρ' s := by
        exact subst_ext (Base := Base) (Const := WithParams Const)
          (σs := ρ) (τs := ρ') hρ s
      have ht : subst (Base := Base) (Const := WithParams Const) ρ t =
          subst (Base := Base) (Const := WithParams Const) ρ' t := by
        exact subst_ext (Base := Base) (Const := WithParams Const)
          (σs := ρ) (τs := ρ') hρ t
      simp [RecursiveForcesOpen, hs, ht]
  | all φ =>
      simp [RecursiveForcesOpen]
      constructor
      · intro h V hWV t
        exact (recursiveForcesOpen_env_ext (W := V)
          (by
            intro τ v
            cases v with
            | vz => rfl
            | vs v => exact hρ v) φ).mp (h V hWV t)
      · intro h V hWV t
        exact (recursiveForcesOpen_env_ext (W := V)
          (by
            intro τ v
            cases v with
            | vz => rfl
            | vs v => exact hρ v) φ).mpr (h V hWV t)
  | ex φ =>
      simp [RecursiveForcesOpen]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, fun V hWV => (recursiveForcesOpen_env_ext (W := V)
          (by
            intro τ v
            cases v with
            | vz => rfl
            | vs v => exact hρ v) φ).mp (ht V hWV)⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, fun V hWV => (recursiveForcesOpen_env_ext (W := V)
          (by
            intro τ v
            cases v with
            | vz => rfl
            | vs v => exact hρ v) φ).mpr (ht V hWV)⟩
termination_by sizeOf φ

/-- Closed recursive forcing is independent of the chosen empty environment. -/
theorem recursiveForcesOpen_empty_env
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (ρ : ClosedEnv (Base := Base) (Const := WithParams Const) [])
    (φ : ClosedFormula (WithParams Const)) :
    RecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ ↔
      RecursiveForces (Base := Base) (Const := Const) W φ := by
  exact recursiveForcesOpen_env_ext (Base := Base) (Const := Const) (W := W)
    (ρ := ρ) (ρ' := ClosedEnv.empty (Base := Base) (Const := WithParams Const))
    (by
      intro τ v
      cases v)
    φ

/-- Recursive canonical forcing is monotone along carrier inclusion. -/
theorem recursiveForcesOpen_mono
    {Γ : Ctx Base}
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (φ : Formula (WithParams Const) Γ)
    (ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ) :
    RecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ →
      RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ := by
  cases φ with
  | var v =>
      intro h
      simpa [RecursiveForcesOpen, Atom] using
        hWV (by simpa [RecursiveForcesOpen, Atom] using h)
  | const c =>
      intro h
      simpa [RecursiveForcesOpen, Atom] using
        hWV (by simpa [RecursiveForcesOpen, Atom] using h)
  | app f t =>
      intro h
      simpa [RecursiveForcesOpen, Atom] using
        hWV (by simpa [RecursiveForcesOpen, Atom] using h)
  | top =>
      intro _
      simp [RecursiveForcesOpen]
  | bot =>
      intro h
      simp [RecursiveForcesOpen] at h
  | and φ ψ =>
      intro h
      have h' : RecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ ∧
          RecursiveForcesOpen (Base := Base) (Const := Const) W ψ ρ := by
        simpa [RecursiveForcesOpen] using h
      simpa [RecursiveForcesOpen] using
        And.intro (recursiveForcesOpen_mono hWV φ ρ h'.1)
          (recursiveForcesOpen_mono hWV ψ ρ h'.2)
  | or φ ψ =>
      intro h
      have h' : RecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ ∨
          RecursiveForcesOpen (Base := Base) (Const := Const) W ψ ρ := by
        simpa [RecursiveForcesOpen] using h
      rcases h' with hφ | hψ
      · simpa [RecursiveForcesOpen] using
          (Or.inl (recursiveForcesOpen_mono hWV φ ρ hφ) :
            RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
              RecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)
      · simpa [RecursiveForcesOpen] using
          (Or.inr (recursiveForcesOpen_mono hWV ψ ρ hψ) :
            RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
              RecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)
  | imp φ ψ =>
      intro h
      have h' :
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W U →
              RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
                RecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ := by
        simpa [RecursiveForcesOpen] using h
      simpa [RecursiveForcesOpen] using
        (show
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) V U →
              RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
                RecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ from
          fun U hVU hφU => h' U (le_trans (Base := Base) (Const := Const) hWV hVU) hφU)
  | not φ =>
      intro h
      have h' :
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W U →
              ¬ RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ := by
        simpa [RecursiveForcesOpen] using h
      simpa [RecursiveForcesOpen] using
        (show
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) V U →
              ¬ RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ from
          fun U hVU hφU => h' U (le_trans (Base := Base) (Const := Const) hWV hVU) hφU)
  | eq s t =>
      intro h
      simpa [RecursiveForcesOpen, EqVal] using
        hWV (by simpa [RecursiveForcesOpen, EqVal] using h)
  | all φ =>
      intro h
      have h' :
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W U →
              ∀ t : ClosedTerm (WithParams Const) _,
                RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) := by
        simpa [RecursiveForcesOpen] using h
      simpa [RecursiveForcesOpen] using
        (show
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) V U →
              ∀ t : ClosedTerm (WithParams Const) _,
                RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) from
          fun U hVU t => h' U (le_trans (Base := Base) (Const := Const) hWV hVU) t)
  | ex φ =>
      intro h
      have h' :
          ∃ t : ClosedTerm (WithParams Const) _,
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              Le (Base := Base) (Const := Const) W U →
                RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) := by
        simpa [RecursiveForcesOpen] using h
      rcases h' with ⟨t, ht⟩
      simpa [RecursiveForcesOpen] using
        (show
          ∃ t : ClosedTerm (WithParams Const) _,
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              Le (Base := Base) (Const := Const) V U →
                RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) from
          ⟨t, fun U hVU => ht U (le_trans (Base := Base) (Const := Const) hWV hVU)⟩)
termination_by sizeOf φ

/-- Closed recursive forcing is monotone along carrier inclusion. -/
theorem recursiveForces_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hWV : Le (Base := Base) (Const := Const) W V)
    {φ : ClosedFormula (WithParams Const)}
    (hφ : RecursiveForces (Base := Base) (Const := Const) W φ) :
    RecursiveForces (Base := Base) (Const := Const) V φ :=
  recursiveForcesOpen_mono (Base := Base) (Const := Const) hWV φ
    (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) hφ

/-- Recursive Kripke forcing whose accessibility relation is the level-growing
canonical preorder.  This is the recursive counterpart of
`canonicalLevelKripkeHenkin`: atomic formulas and equality are still read from
carrier membership, but implication, negation, universals, and existentials
range only over successors that also preserve the level invariant. -/
def LevelRecursiveForcesOpen :
    {Γ : Ctx Base} →
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const →
        Formula (WithParams Const) Γ → ClosedEnv (WithParams Const) Γ → Prop
  | _, W, .var v, ρ => Atom (Base := Base) (Const := Const) W (subst ρ (.var v))
  | _, W, .const c, ρ => Atom (Base := Base) (Const := Const) W (subst ρ (.const c))
  | _, W, .app f t, ρ => Atom (Base := Base) (Const := Const) W (subst ρ (.app f t))
  | _, W, .eq s t, ρ => EqVal (Base := Base) (Const := Const) W (subst ρ s) (subst ρ t)
  | _, _W, .top, _ρ => True
  | _, _W, .bot, _ρ => False
  | _, W, .and φ ψ, ρ => LevelRecursiveForcesOpen W φ ρ ∧ LevelRecursiveForcesOpen W ψ ρ
  | _, W, .or φ ψ, ρ => LevelRecursiveForcesOpen W φ ρ ∨ LevelRecursiveForcesOpen W ψ ρ
  | _, W, .imp φ ψ, ρ =>
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          LevelRecursiveForcesOpen V φ ρ → LevelRecursiveForcesOpen V ψ ρ
  | _, W, .not φ, ρ =>
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V → ¬ LevelRecursiveForcesOpen V φ ρ
  | _, W, .all φ, ρ =>
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) _,
            LevelRecursiveForcesOpen V φ (ClosedEnv.extend (Base := Base) ρ t)
  | _, W, .ex φ, ρ =>
      ∃ t : ClosedTerm (WithParams Const) _,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            LevelRecursiveForcesOpen V φ (ClosedEnv.extend (Base := Base) ρ t)
termination_by _Γ _W φ _ρ => sizeOf φ

/-- Closed-formula specialization of level-recursive canonical forcing. -/
def LevelRecursiveForces
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  LevelRecursiveForcesOpen (Base := Base) (Const := Const) W φ
    (ClosedEnv.empty (Base := Base) (Const := WithParams Const))

/-- Level-recursive canonical forcing is monotone along the level-growing
canonical preorder. -/
theorem levelRecursiveForcesOpen_mono
    {Γ : Ctx Base}
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (φ : Formula (WithParams Const) Γ)
    (ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ) :
    LevelRecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ →
      LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ := by
  cases φ with
  | var v =>
      intro h
      simpa [LevelRecursiveForcesOpen, Atom] using
        hWV.2 (by simpa [LevelRecursiveForcesOpen, Atom] using h)
  | const c =>
      intro h
      simpa [LevelRecursiveForcesOpen, Atom] using
        hWV.2 (by simpa [LevelRecursiveForcesOpen, Atom] using h)
  | app f t =>
      intro h
      simpa [LevelRecursiveForcesOpen, Atom] using
        hWV.2 (by simpa [LevelRecursiveForcesOpen, Atom] using h)
  | top =>
      intro _
      simp [LevelRecursiveForcesOpen]
  | bot =>
      intro h
      simp [LevelRecursiveForcesOpen] at h
  | and φ ψ =>
      intro h
      have h' : LevelRecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ ∧
          LevelRecursiveForcesOpen (Base := Base) (Const := Const) W ψ ρ := by
        simpa [LevelRecursiveForcesOpen] using h
      simpa [LevelRecursiveForcesOpen] using
        And.intro (levelRecursiveForcesOpen_mono hWV φ ρ h'.1)
          (levelRecursiveForcesOpen_mono hWV ψ ρ h'.2)
  | or φ ψ =>
      intro h
      have h' : LevelRecursiveForcesOpen (Base := Base) (Const := Const) W φ ρ ∨
          LevelRecursiveForcesOpen (Base := Base) (Const := Const) W ψ ρ := by
        simpa [LevelRecursiveForcesOpen] using h
      rcases h' with hφ | hψ
      · simpa [LevelRecursiveForcesOpen] using
          (Or.inl (levelRecursiveForcesOpen_mono hWV φ ρ hφ) :
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)
      · simpa [LevelRecursiveForcesOpen] using
          (Or.inr (levelRecursiveForcesOpen_mono hWV ψ ρ hψ) :
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)
  | imp φ ψ =>
      intro h
      have h' :
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W U →
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
                LevelRecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ := by
        simpa [LevelRecursiveForcesOpen] using h
      simpa [LevelRecursiveForcesOpen] using
        (show
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) V U →
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
                LevelRecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ from
          fun U hVU hφU =>
            h' U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) hφU)
  | not φ =>
      intro h
      have h' :
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W U →
              ¬ LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ := by
        simpa [LevelRecursiveForcesOpen] using h
      simpa [LevelRecursiveForcesOpen] using
        (show
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) V U →
              ¬ LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ from
          fun U hVU hφU =>
            h' U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) hφU)
  | eq s t =>
      intro h
      simpa [LevelRecursiveForcesOpen, EqVal] using
        hWV.2 (by simpa [LevelRecursiveForcesOpen, EqVal] using h)
  | all φ =>
      intro h
      have h' :
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W U →
              ∀ t : ClosedTerm (WithParams Const) _,
                LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) := by
        simpa [LevelRecursiveForcesOpen] using h
      simpa [LevelRecursiveForcesOpen] using
        (show
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) V U →
              ∀ t : ClosedTerm (WithParams Const) _,
                LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) from
          fun U hVU t =>
            h' U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) t)
  | ex φ =>
      intro h
      have h' :
          ∃ t : ClosedTerm (WithParams Const) _,
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              LevelLe (Base := Base) (Const := Const) W U →
                LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) := by
        simpa [LevelRecursiveForcesOpen] using h
      rcases h' with ⟨t, ht⟩
      simpa [LevelRecursiveForcesOpen] using
        (show
          ∃ t : ClosedTerm (WithParams Const) _,
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              LevelLe (Base := Base) (Const := Const) V U →
                LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
                  (ClosedEnv.extend (Base := Base) ρ t) from
          ⟨t, fun U hVU =>
            ht U (levelLe_trans (Base := Base) (Const := Const) hWV hVU)⟩)
termination_by sizeOf φ

/-- Closed level-recursive forcing is monotone along the level-growing
canonical preorder. -/
theorem levelRecursiveForces_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveForces (Base := Base) (Const := Const) W φ) :
    LevelRecursiveForces (Base := Base) (Const := Const) V φ :=
  levelRecursiveForcesOpen_mono (Base := Base) (Const := Const) hWV φ
    (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) hφ

theorem levelRecursiveForces_atom_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (c : WithParams Const propTy) :
    LevelRecursiveForces (Base := Base) (Const := Const) W
        (.const c : ClosedFormula (WithParams Const)) ↔
      Atom (Base := Base) (Const := Const) W (.const c : ClosedFormula (WithParams Const)) := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen, ClosedEnv.subst_empty]

theorem levelRecursiveForces_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ propTy))
    (t : ClosedTerm (WithParams Const) σ) :
    LevelRecursiveForces (Base := Base) (Const := Const) W
        (.app f t : ClosedFormula (WithParams Const)) ↔
      Atom (Base := Base) (Const := Const) W (.app f t : ClosedFormula (WithParams Const)) := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen, ClosedEnv.subst_empty]

theorem levelRecursiveForces_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    LevelRecursiveForces (Base := Base) (Const := Const) W (.top : ClosedFormula (WithParams Const)) := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

theorem levelRecursiveForces_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    ¬ LevelRecursiveForces (Base := Base) (Const := Const) W (.bot : ClosedFormula (WithParams Const)) := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

theorem levelRecursiveForces_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)} :
    LevelRecursiveForces (Base := Base) (Const := Const) W (.and φ ψ) ↔
      LevelRecursiveForces (Base := Base) (Const := Const) W φ ∧
        LevelRecursiveForces (Base := Base) (Const := Const) W ψ := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

theorem levelRecursiveForces_or
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)} :
    LevelRecursiveForces (Base := Base) (Const := Const) W (.or φ ψ) ↔
      LevelRecursiveForces (Base := Base) (Const := Const) W φ ∨
        LevelRecursiveForces (Base := Base) (Const := Const) W ψ := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

theorem levelRecursiveForces_imp
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)} :
    LevelRecursiveForces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          LevelRecursiveForces (Base := Base) (Const := Const) V φ →
            LevelRecursiveForces (Base := Base) (Const := Const) V ψ := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

theorem levelRecursiveForces_not
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)} :
    LevelRecursiveForces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ¬ LevelRecursiveForces (Base := Base) (Const := Const) V φ := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

theorem levelRecursiveForces_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {τ : Ty Base} (s t : ClosedTerm (WithParams Const) τ) :
    LevelRecursiveForces (Base := Base) (Const := Const) W
        (.eq s t : ClosedFormula (WithParams Const)) ↔
      EqVal (Base := Base) (Const := Const) W s t := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen, ClosedEnv.subst_empty]

theorem levelRecursiveForces_all
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    LevelRecursiveForces (Base := Base) (Const := Const) W
        (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

theorem levelRecursiveForces_ex
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    LevelRecursiveForces (Base := Base) (Const := Const) W
        (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
  simp [LevelRecursiveForces, LevelRecursiveForcesOpen]

/-- Closed truth bridge for the level-recursive canonical forcing relation. -/
def LevelRecursiveClosedTruthAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  LevelRecursiveForces (Base := Base) (Const := Const) W φ ↔
    Forces (Base := Base) (Const := Const) W φ

/-- Level-recursive body truth bridge for one-variable quantifier bodies. -/
def LevelRecursiveBodyClosedTruthBridge
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {σ : Ty Base} (φ : Formula (WithParams Const) [σ]) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    LevelLe (Base := Base) (Const := Const) W V →
      ∀ t : ClosedTerm (WithParams Const) σ,
        LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ
            (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
              (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ↔
          Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ)

/-- Level-recursive closed truth above a world. -/
def LevelRecursiveClosedTruthAbove
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    LevelLe (Base := Base) (Const := Const) W V →
      LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) V φ

/-- Open truth bridge for level-recursive forcing under arbitrary closed-term
environments.  Its one-variable instance is the body bridge needed by
substitutional quantifier clauses. -/
def LevelRecursiveOpenTruthBridge
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} (φ : Formula (WithParams Const) Γ) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    LevelLe (Base := Base) (Const := Const) W V →
      ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
        LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ↔
          Forces (Base := Base) (Const := Const) V (subst ρ φ)

theorem levelRecursiveBodyClosedTruthBridge_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) V φ := by
  intro U hVU t
  exact hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) t

theorem levelRecursiveClosedTruthAbove_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) V φ := by
  intro U hVU
  exact hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU)

theorem levelRecursiveOpenTruthBridge_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) V φ := by
  intro U hVU ρ
  exact hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ

theorem levelRecursiveBodyClosedTruthBridge_of_openTruthBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ := by
  intro V hWV t
  simpa [ClosedEnv.subst_extend_empty] using
    hφ V hWV
      (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
        (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t)

theorem levelRecursiveClosedTruthAt_of_openTruthBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W φ := by
  simpa [LevelRecursiveClosedTruthAt, LevelRecursiveForces, ClosedEnv.subst_empty] using
    hφ W (levelLe_refl (Base := Base) (Const := Const) W)
      (ClosedEnv.empty (Base := Base) (Const := WithParams Const))

theorem levelRecursiveClosedTruthAbove_of_openTruthBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_mono (Base := Base) (Const := Const) hWV hφ)

theorem levelRecursiveOpenTruthBridge_var
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (v : Var Γ propTy) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W
      (.var v : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  simp [LevelRecursiveForcesOpen, Forces, Atom]

theorem levelRecursiveOpenTruthBridge_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (c : WithParams Const propTy) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W
      (.const c : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  simp [LevelRecursiveForcesOpen, Forces, Atom, subst]

theorem levelRecursiveOpenTruthBridge_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base}
    (f : Term (WithParams Const) Γ (σ ⇒ propTy)) (t : Term (WithParams Const) Γ σ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.app f t) := by
  intro V _hWV ρ
  simp [LevelRecursiveForcesOpen, Forces, Atom, subst]

theorem levelRecursiveOpenTruthBridge_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W
      (.top : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  constructor
  · intro _
    simpa [subst] using forces_top (Base := Base) (Const := Const) V
  · intro _
    simp [LevelRecursiveForcesOpen]

theorem levelRecursiveOpenTruthBridge_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W
      (.bot : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  constructor
  · intro h
    simp [LevelRecursiveForcesOpen] at h
  · intro h
    exact False.elim (forces_bot (Base := Base) (Const := Const) V
      (by simpa [subst] using h))

theorem levelRecursiveOpenTruthBridge_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} (s t : Term (WithParams Const) Γ τ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W
      (.eq s t : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  simp [LevelRecursiveForcesOpen, Forces, EqVal, subst]

theorem levelRecursiveOpenTruthBridge_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.and φ ψ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hPair :
        LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∧
          LevelRecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ := by
      simpa [LevelRecursiveForcesOpen] using h
    have hAnd : Forces (Base := Base) (Const := Const) V
        (.and (subst ρ φ) (subst ρ ψ)) :=
      (forces_and (Base := Base) (Const := Const)).mpr
        ⟨(hφ V hWV ρ).mp hPair.1, (hψ V hWV ρ).mp hPair.2⟩
    simpa [subst] using hAnd
  · intro h
    have hAnd : Forces (Base := Base) (Const := Const) V
        (.and (subst ρ φ) (subst ρ ψ)) := by
      simpa [subst] using h
    have hPair :
        LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∧
          LevelRecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ :=
      ⟨(hφ V hWV ρ).mpr ((forces_and (Base := Base) (Const := Const)).mp hAnd).1,
        (hψ V hWV ρ).mpr ((forces_and (Base := Base) (Const := Const)).mp hAnd).2⟩
    simpa [LevelRecursiveForcesOpen] using hPair

theorem levelRecursiveOpenTruthBridge_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hSupport :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
            SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)))
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hOr : Forces (Base := Base) (Const := Const) V
        (.or (subst ρ φ) (subst ρ ψ)) := by
      rcases (by simpa [LevelRecursiveForcesOpen] using h) with hφ' | hψ'
      · exact (forces_or_at (Base := Base) (Const := Const)
          (W := V) (by simpa [subst] using hSupport V hWV ρ)).mpr
          (Or.inl ((hφ V hWV ρ).mp hφ'))
      · exact (forces_or_at (Base := Base) (Const := Const)
          (W := V) (by simpa [subst] using hSupport V hWV ρ)).mpr
          (Or.inr ((hψ V hWV ρ).mp hψ'))
    simpa [subst] using hOr
  · intro h
    have hOr : Forces (Base := Base) (Const := Const) V
        (.or (subst ρ φ) (subst ρ ψ)) := by
      simpa [subst] using h
    rcases (forces_or_at (Base := Base) (Const := Const)
        (W := V) (by simpa [subst] using hSupport V hWV ρ)).mp hOr with hφ' | hψ'
    · simpa [LevelRecursiveForcesOpen] using
        (Or.inl ((hφ V hWV ρ).mpr hφ') :
          LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)
    · simpa [LevelRecursiveForcesOpen] using
        (Or.inr ((hψ V hWV ρ).mpr hψ') :
          LevelRecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)

theorem levelRecursiveOpenTruthBridge_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) V U →
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ := by
      simpa [LevelRecursiveForcesOpen] using h
    have hImp : Forces (Base := Base) (Const := Const) V
        (.imp (subst ρ φ) (subst ρ ψ)) := by
      apply (forces_imp_level_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU hφU
      exact (hψ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ).mp
        (hRec U hVU
          ((hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ).mpr hφU))
    simpa [subst] using hImp
  · intro h
    have hImp : Forces (Base := Base) (Const := Const) V
        (.imp (subst ρ φ) (subst ρ ψ)) := by
      simpa [subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) V U →
            LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ := by
      intro U hVU hφU
      exact (hψ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ).mpr
        ((forces_imp_level_provider (Base := Base) (Const := Const) P V).mp hImp U hVU
          ((hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ).mp hφU))
    simpa [LevelRecursiveForcesOpen] using hRec

theorem levelRecursiveOpenTruthBridge_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.not φ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) V U →
            ¬ LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ := by
      simpa [LevelRecursiveForcesOpen] using h
    have hNot : Forces (Base := Base) (Const := Const) V (.not (subst ρ φ)) := by
      apply (forces_not_level_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU hφU
      exact hRec U hVU
        ((hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ).mpr hφU)
    simpa [subst] using hNot
  · intro h
    have hNot : Forces (Base := Base) (Const := Const) V (.not (subst ρ φ)) := by
      simpa [subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) V U →
            ¬ LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ := by
      intro U hVU hφU
      exact (forces_not_level_provider (Base := Base) (Const := Const) P V).mp hNot U hVU
        ((hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ).mp hφU)
    simpa [LevelRecursiveForcesOpen] using hRec

theorem levelRecursiveOpenTruthBridge_all
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.all φ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) V U →
            ∀ t : ClosedTerm (WithParams Const) σ,
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
                (ClosedEnv.extend (Base := Base) ρ t) := by
      simpa [LevelRecursiveForcesOpen] using h
    have hAll : Forces (Base := Base) (Const := Const) V
        (.all (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      apply (forces_all_level_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU t
      have hBody :=
        (hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU)
          (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mp
          (hRec U hVU t)
      simpa [ClosedEnv.instantiate_subst_lift_extend] using hBody
    simpa [subst] using hAll
  · intro h
    have hAll : Forces (Base := Base) (Const := Const) V
        (.all (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      simpa [subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) V U →
            ∀ t : ClosedTerm (WithParams Const) σ,
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
                (ClosedEnv.extend (Base := Base) ρ t) := by
      intro U hVU t
      have hInst :=
        (forces_all_level_provider (Base := Base) (Const := Const) P V).mp hAll U hVU t
      exact (hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU)
        (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mpr
        (by simpa [ClosedEnv.instantiate_subst_lift_extend] using hInst)
    simpa [LevelRecursiveForcesOpen] using hRec

theorem levelRecursiveOpenTruthBridge_ex_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hSupport :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
            SupportedAt (Base := Base) (Const := Const) V
              (subst ρ (.ex φ : Formula (WithParams Const) Γ)))
    (hφ : LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.ex φ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) V U →
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
                (ClosedEnv.extend (Base := Base) ρ t) := by
      simpa [LevelRecursiveForcesOpen] using h
    have hEx : Forces (Base := Base) (Const := Const) V
        (.ex (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      rw [forces_ex_level_kripke_at (Base := Base) (Const := Const) (W := V)
        (by simpa [subst] using hSupport V hWV ρ)]
      rcases hRec with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      intro U hVU
      have hBody :=
        (hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU)
          (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mp
          (ht U hVU)
      simpa [ClosedEnv.instantiate_subst_lift_extend] using hBody
    simpa [subst] using hEx
  · intro h
    have hEx : Forces (Base := Base) (Const := Const) V
        (.ex (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      simpa [subst] using h
    have hRec :
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) V U →
              LevelRecursiveForcesOpen (Base := Base) (Const := Const) U φ
              (ClosedEnv.extend (Base := Base) ρ t) := by
      rw [forces_ex_level_kripke_at (Base := Base) (Const := Const) (W := V)
        (by simpa [subst] using hSupport V hWV ρ)] at hEx
      rcases hEx with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      intro U hVU
      exact (hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU)
        (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mpr
        (by simpa [ClosedEnv.instantiate_subst_lift_extend] using ht U hVU)
    simpa [LevelRecursiveForcesOpen] using hRec

theorem levelRecursiveClosedTruthAt_all
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody :
      LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_all,
    forces_all_level_provider (Base := Base) (Const := Const) P W]
  constructor
  · intro hRec V hWV t
    exact (hBody V hWV t).mp (hRec V hWV t)
  · intro hAll V hWV t
    exact (hBody V hWV t).mpr (hAll V hWV t)

theorem levelRecursiveClosedTruthAt_ex_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const)))
    (hBody :
      LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_ex,
    forces_ex_level_kripke_at (Base := Base) (Const := Const) (W := W) hSupport]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun V hWV => (hBody V hWV t).mp (ht V hWV)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, fun V hWV => (hBody V hWV t).mpr (ht V hWV)⟩

theorem levelRecursiveClosedTruthAt_atom_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (c : WithParams Const propTy) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.const c : ClosedFormula (WithParams Const)) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_atom_const,
    forces_atom_const (Base := Base) (Const := Const) W c]

theorem levelRecursiveClosedTruthAt_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ propTy))
    (t : ClosedTerm (WithParams Const) σ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.app f t : ClosedFormula (WithParams Const)) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_atom_app,
    forces_atom_app (Base := Base) (Const := Const) W f t]

theorem levelRecursiveClosedTruthAt_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.top : ClosedFormula (WithParams Const)) := by
  constructor
  · intro _h
    exact forces_top (Base := Base) (Const := Const) W
  · intro _h
    exact levelRecursiveForces_top (Base := Base) (Const := Const)

theorem levelRecursiveClosedTruthAt_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.bot : ClosedFormula (WithParams Const)) := by
  constructor
  · intro h
    exact False.elim (levelRecursiveForces_bot (Base := Base) (Const := Const) h)
  · intro h
    exact False.elim (forces_bot (Base := Base) (Const := Const) W h)

theorem levelRecursiveClosedTruthAt_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W (.and φ ψ) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_and, forces_and]
  constructor
  · intro h
    exact ⟨hφ.mp h.1, hψ.mp h.2⟩
  · intro h
    exact ⟨hφ.mpr h.1, hψ.mpr h.2⟩

theorem levelRecursiveClosedTruthAt_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W (.or φ ψ) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_or,
    forces_or_at (Base := Base) (Const := Const) (W := W) hSupport]
  constructor
  · intro h
    rcases h with hφ' | hψ'
    · exact Or.inl (hφ.mp hφ')
    · exact Or.inr (hψ.mp hψ')
  · intro h
    rcases h with hφ' | hψ'
    · exact Or.inl (hφ.mpr hφ')
    · exact Or.inr (hψ.mpr hψ')

theorem levelRecursiveClosedTruthAt_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {τ : Ty Base} (s t : ClosedTerm (WithParams Const) τ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.eq s t : ClosedFormula (WithParams Const)) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_eq,
    forces_eq (Base := Base) (Const := Const)]

theorem levelRecursiveClosedTruthAt_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W (.imp φ ψ) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_imp,
    forces_imp_level_provider (Base := Base) (Const := Const) P W]
  constructor
  · intro hRec V hWV hφF
    exact (hψ V hWV).mp (hRec V hWV ((hφ V hWV).mpr hφF))
  · intro hImp V hWV hφR
    exact (hψ V hWV).mpr (hImp V hWV ((hφ V hWV).mp hφR))

theorem levelRecursiveClosedTruthAt_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W (.not φ) := by
  rw [LevelRecursiveClosedTruthAt, levelRecursiveForces_not,
    forces_not_level_provider (Base := Base) (Const := Const) P W]
  constructor
  · intro hRec V hWV hφF
    exact hRec V hWV ((hφ V hWV).mpr hφF)
  · intro hNot V hWV hφR
    exact hNot V hWV ((hφ V hWV).mp hφR)

theorem levelRecursiveClosedTruthAbove_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.and φ ψ) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_and (Base := Base) (Const := Const)
    (hφ V hWV) (hψ V hWV)

theorem levelRecursiveClosedTruthAbove_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          SupportedAt (Base := Base) (Const := Const) V (.or φ ψ))
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV
  have hSupportV : SupportedAt (Base := Base) (Const := Const) V (.or φ ψ) :=
    hSupport V hWV
  exact levelRecursiveClosedTruthAt_or_supported (Base := Base) (Const := Const)
    hSupportV (hφ V hWV) (hψ V hWV)

theorem levelRecursiveClosedTruthAbove_or_supportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveClosedTruthAbove_or_supported (Base := Base) (Const := Const)
    (fun _ hWV => supportedAt_mono (Base := Base) (Const := Const) hWV hSupport)
    hφ hψ

theorem levelRecursiveClosedTruthAbove_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_imp (Base := Base) (Const := Const) P
    (levelRecursiveClosedTruthAbove_mono (Base := Base) (Const := Const) hWV hφ)
    (levelRecursiveClosedTruthAbove_mono (Base := Base) (Const := Const) hWV hψ)

theorem levelRecursiveClosedTruthAbove_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.not φ) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_not (Base := Base) (Const := Const) P
    (levelRecursiveClosedTruthAbove_mono (Base := Base) (Const := Const) hWV hφ)

theorem levelRecursiveClosedTruthAbove_all
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody :
      LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_all (Base := Base) (Const := Const) P
    (levelRecursiveBodyClosedTruthBridge_mono (Base := Base) (Const := Const) hWV hBody)

theorem levelRecursiveClosedTruthAbove_ex_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          SupportedAt (Base := Base) (Const := Const) V
            (.ex φ : ClosedFormula (WithParams Const)))
    (hBody :
      LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) := by
  intro V hWV
  have hSupportV : SupportedAt (Base := Base) (Const := Const) V
      (.ex φ : ClosedFormula (WithParams Const)) :=
    hSupport V hWV
  exact levelRecursiveClosedTruthAt_ex_supported (Base := Base) (Const := Const)
    hSupportV
    (levelRecursiveBodyClosedTruthBridge_mono (Base := Base) (Const := Const) hWV hBody)

theorem levelRecursiveClosedTruthAbove_ex_supportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)))
    (hBody :
      LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_ex_supported (Base := Base) (Const := Const)
    (fun _ hWV => supportedAt_mono (Base := Base) (Const := Const) hWV hSupport)
    hBody

theorem recursiveForces_atom_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (c : WithParams Const propTy) :
    RecursiveForces (Base := Base) (Const := Const) W
        (.const c : ClosedFormula (WithParams Const)) ↔
      Atom (Base := Base) (Const := Const) W (.const c : ClosedFormula (WithParams Const)) := by
  simp [RecursiveForces, RecursiveForcesOpen, ClosedEnv.subst_empty]

theorem recursiveForces_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ propTy))
    (t : ClosedTerm (WithParams Const) σ) :
    RecursiveForces (Base := Base) (Const := Const) W (.app f t : ClosedFormula (WithParams Const)) ↔
      Atom (Base := Base) (Const := Const) W (.app f t : ClosedFormula (WithParams Const)) := by
  simp [RecursiveForces, RecursiveForcesOpen, ClosedEnv.subst_empty]

theorem recursiveForces_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    RecursiveForces (Base := Base) (Const := Const) W (.top : ClosedFormula (WithParams Const)) := by
  simp [RecursiveForces, RecursiveForcesOpen]

theorem recursiveForces_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    ¬ RecursiveForces (Base := Base) (Const := Const) W (.bot : ClosedFormula (WithParams Const)) := by
  simp [RecursiveForces, RecursiveForcesOpen]

theorem recursiveForces_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)} :
    RecursiveForces (Base := Base) (Const := Const) W (.and φ ψ) ↔
      RecursiveForces (Base := Base) (Const := Const) W φ ∧
        RecursiveForces (Base := Base) (Const := Const) W ψ := by
  simp [RecursiveForces, RecursiveForcesOpen]

theorem recursiveForces_or
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)} :
    RecursiveForces (Base := Base) (Const := Const) W (.or φ ψ) ↔
      RecursiveForces (Base := Base) (Const := Const) W φ ∨
        RecursiveForces (Base := Base) (Const := Const) W ψ := by
  simp [RecursiveForces, RecursiveForcesOpen]

theorem recursiveForces_imp
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)} :
    RecursiveForces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          RecursiveForces (Base := Base) (Const := Const) V φ →
            RecursiveForces (Base := Base) (Const := Const) V ψ := by
  simp [RecursiveForces, RecursiveForcesOpen]

theorem recursiveForces_not
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)} :
    RecursiveForces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ¬ RecursiveForces (Base := Base) (Const := Const) V φ := by
  simp [RecursiveForces, RecursiveForcesOpen]

theorem recursiveForces_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {s t : ClosedTerm (WithParams Const) σ} :
    RecursiveForces (Base := Base) (Const := Const) W (.eq s t : ClosedFormula (WithParams Const)) ↔
      EqVal (Base := Base) (Const := Const) W s t := by
  simp [RecursiveForces, RecursiveForcesOpen, ClosedEnv.subst_empty]

theorem recursiveForces_all_open
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    RecursiveForces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            RecursiveForcesOpen (Base := Base) (Const := Const) V φ
              (ClosedEnv.extend (Base := Base)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
  simp [RecursiveForces, RecursiveForcesOpen]

theorem recursiveForces_ex_open
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    RecursiveForces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            RecursiveForcesOpen (Base := Base) (Const := Const) V φ
              (ClosedEnv.extend (Base := Base)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
  simp [RecursiveForces, RecursiveForcesOpen]

/-! ## Propositional-variable quantifier special cases -/

theorem recursiveForcesOpen_prop_var_extend_empty
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (t : ClosedFormula (WithParams Const)) :
    RecursiveForcesOpen (Base := Base) (Const := Const) W
        (.var .vz : Formula (WithParams Const) [propTy])
        (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
          (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ↔
      Forces (Base := Base) (Const := Const) W t := by
  simp [RecursiveForcesOpen, Forces, Atom, ClosedEnv.extend, subst]

theorem recursiveForces_instantiate_prop_var
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (t : ClosedFormula (WithParams Const)) :
    RecursiveForces (Base := Base) (Const := Const) W
        (instantiate (Base := Base) t
          (.var .vz : Formula (WithParams Const) [propTy])) ↔
      RecursiveForces (Base := Base) (Const := Const) W t := by
  simp [instantiate, subst, Subst.single]

theorem recursiveForces_all_prop_var_membership
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    RecursiveForces (Base := Base) (Const := Const) W
        (.all (.var .vz) : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedFormula (WithParams Const),
            Forces (Base := Base) (Const := Const) V t := by
  rw [recursiveForces_all_open]
  constructor
  · intro h V hWV t
    exact (recursiveForcesOpen_prop_var_extend_empty (Base := Base) (Const := Const)
      (W := V) t).mp (h V hWV t)
  · intro h V hWV t
    exact (recursiveForcesOpen_prop_var_extend_empty (Base := Base) (Const := Const)
      (W := V) t).mpr (h V hWV t)

theorem recursiveForces_all_prop_var_recursive_of_truth
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hTruth :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedFormula (WithParams Const),
            RecursiveForces (Base := Base) (Const := Const) V t ↔
              Forces (Base := Base) (Const := Const) V t) :
    RecursiveForces (Base := Base) (Const := Const) W
        (.all (.var .vz) : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedFormula (WithParams Const),
            RecursiveForces (Base := Base) (Const := Const) V
              (instantiate (Base := Base) t
                (.var .vz : Formula (WithParams Const) [propTy])) := by
  rw [recursiveForces_all_prop_var_membership]
  constructor
  · intro h V hWV t
    exact (recursiveForces_instantiate_prop_var (Base := Base) (Const := Const)
      (W := V) t).mpr ((hTruth V hWV t).mpr (h V hWV t))
  · intro h V hWV t
    exact (hTruth V hWV t).mp
      ((recursiveForces_instantiate_prop_var (Base := Base) (Const := Const)
        (W := V) t).mp (h V hWV t))

/-! ## Recursive-to-membership bridge clauses -/

theorem recursiveForces_iff_forces_atom_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (c : WithParams Const propTy) :
    RecursiveForces (Base := Base) (Const := Const) W
        (.const c : ClosedFormula (WithParams Const)) ↔
      Forces (Base := Base) (Const := Const) W (.const c : ClosedFormula (WithParams Const)) := by
  rw [recursiveForces_atom_const, forces_atom_const]

theorem recursiveForces_iff_forces_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ propTy))
    (t : ClosedTerm (WithParams Const) σ) :
    RecursiveForces (Base := Base) (Const := Const) W (.app f t : ClosedFormula (WithParams Const)) ↔
      Forces (Base := Base) (Const := Const) W (.app f t : ClosedFormula (WithParams Const)) := by
  rw [recursiveForces_atom_app, forces_atom_app]

theorem recursiveForces_iff_forces_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    RecursiveForces (Base := Base) (Const := Const) W (.top : ClosedFormula (WithParams Const)) ↔
      Forces (Base := Base) (Const := Const) W (.top : ClosedFormula (WithParams Const)) := by
  constructor
  · intro _
    exact forces_top (Base := Base) (Const := Const) W
  · intro _
    exact recursiveForces_top (Base := Base) (Const := Const)

theorem recursiveForces_iff_forces_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    RecursiveForces (Base := Base) (Const := Const) W (.bot : ClosedFormula (WithParams Const)) ↔
      Forces (Base := Base) (Const := Const) W (.bot : ClosedFormula (WithParams Const)) := by
  constructor
  · intro h
    exact False.elim (recursiveForces_bot (Base := Base) (Const := Const) h)
  · intro h
    exact False.elim (forces_bot (Base := Base) (Const := Const) W h)

theorem recursiveForces_iff_forces_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {s t : ClosedTerm (WithParams Const) σ} :
    RecursiveForces (Base := Base) (Const := Const) W (.eq s t : ClosedFormula (WithParams Const)) ↔
      Forces (Base := Base) (Const := Const) W (.eq s t : ClosedFormula (WithParams Const)) := by
  rw [recursiveForces_eq, forces_eq]

theorem recursiveForces_iff_forces_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : RecursiveForces (Base := Base) (Const := Const) W φ ↔
      Forces (Base := Base) (Const := Const) W φ)
    (hψ : RecursiveForces (Base := Base) (Const := Const) W ψ ↔
      Forces (Base := Base) (Const := Const) W ψ) :
    RecursiveForces (Base := Base) (Const := Const) W (.and φ ψ) ↔
      Forces (Base := Base) (Const := Const) W (.and φ ψ) := by
  rw [recursiveForces_and, forces_and, hφ, hψ]

theorem recursiveForces_iff_forces_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : RecursiveForces (Base := Base) (Const := Const) W φ ↔
      Forces (Base := Base) (Const := Const) W φ)
    (hψ : RecursiveForces (Base := Base) (Const := Const) W ψ ↔
      Forces (Base := Base) (Const := Const) W ψ) :
    RecursiveForces (Base := Base) (Const := Const) W (.or φ ψ) ↔
      Forces (Base := Base) (Const := Const) W (.or φ ψ) := by
  rw [recursiveForces_or, forces_or_at (Base := Base) (Const := Const) (W := W) hSupport, hφ, hψ]

theorem recursiveForces_iff_forces_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSucc :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          (RecursiveForces (Base := Base) (Const := Const) V φ ↔
            Forces (Base := Base) (Const := Const) V φ) ∧
          (RecursiveForces (Base := Base) (Const := Const) V ψ ↔
            Forces (Base := Base) (Const := Const) V ψ)) :
    RecursiveForces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      Forces (Base := Base) (Const := Const) W (.imp φ ψ) := by
  rw [recursiveForces_imp, forces_imp_provider (Base := Base) (Const := Const) P W]
  constructor
  · intro h V hWV hφV
    exact (hSucc V hWV).2.mp (h V hWV ((hSucc V hWV).1.mpr hφV))
  · intro h V hWV hφV
    exact (hSucc V hWV).2.mpr (h V hWV ((hSucc V hWV).1.mp hφV))

theorem recursiveForces_iff_forces_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hSucc :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          (RecursiveForces (Base := Base) (Const := Const) V φ ↔
            Forces (Base := Base) (Const := Const) V φ)) :
    RecursiveForces (Base := Base) (Const := Const) W (.not φ) ↔
      Forces (Base := Base) (Const := Const) W (.not φ) := by
  rw [recursiveForces_not, forces_not_provider (Base := Base) (Const := Const) P W]
  constructor
  · intro h V hWV hφV
    exact h V hWV ((hSucc V hWV).mpr hφV)
  · intro h V hWV hφV
    exact h V hWV ((hSucc V hWV).mp hφV)

theorem recursiveForces_iff_forces_all
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            RecursiveForcesOpen (Base := Base) (Const := Const) V φ
                (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                  (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ↔
              Forces (Base := Base) (Const := Const) V
                (instantiate (Base := Base) t φ)) :
    RecursiveForces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) := by
  rw [recursiveForces_all_open, forces_all_provider (Base := Base) (Const := Const) P W]
  constructor
  · intro h V hWV t
    exact (hBody V hWV t).mp (h V hWV t)
  · intro h V hWV t
    exact (hBody V hWV t).mpr (h V hWV t)

theorem recursiveForces_iff_forces_ex_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const)))
    (hBody :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            RecursiveForcesOpen (Base := Base) (Const := Const) V φ
                (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                  (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ↔
              Forces (Base := Base) (Const := Const) V
                (instantiate (Base := Base) t φ)) :
    RecursiveForces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) := by
  rw [recursiveForces_ex_open,
    forces_ex_kripke_at (Base := Base) (Const := Const) (W := W) hSupport]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun V hWV => (hBody V hWV t).mp (ht V hWV)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, fun V hWV => (hBody V hWV t).mpr (ht V hWV)⟩

/-! ## Closed recursive truth bridge interface -/

/-- Closed truth bridge between recursive canonical forcing and carrier
membership forcing at one supported presented world. -/
def ClosedTruthAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  RecursiveForces (Base := Base) (Const := Const) W φ ↔
    Forces (Base := Base) (Const := Const) W φ

/-- Closed truth bridge at every carrier-extension successor of a world. -/
def ClosedTruthAbove
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    Le (Base := Base) (Const := Const) W V →
      ClosedTruthAt (Base := Base) (Const := Const) V φ

/-- Closed truth bridge at every level-growing successor of a world.  This is
the support-preserving successor interface used by disjunction and existential
truth clauses. -/
def LevelClosedTruthAbove
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    LevelLe (Base := Base) (Const := Const) W V →
      ClosedTruthAt (Base := Base) (Const := Const) V φ

/-- Body truth bridge needed by substitutional quantifier clauses: recursive
open forcing under the one-variable closed environment agrees with membership
forcing of the syntactic instance.  This is deliberately separate from a naive
substitution theorem, since proposition-valued variables are interpreted
atomically by `RecursiveForcesOpen`. -/
def BodyClosedTruthBridge
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {σ : Ty Base} (φ : Formula (WithParams Const) [σ]) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    Le (Base := Base) (Const := Const) W V →
      ∀ t : ClosedTerm (WithParams Const) σ,
        RecursiveForcesOpen (Base := Base) (Const := Const) V φ
            (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
              (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ↔
          Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ)

/-- Open truth bridge for arbitrary closed-term environments.  This is the
higher-context form needed by nested quantifiers; the one-variable
`BodyClosedTruthBridge` is its empty-environment instance. -/
def OpenTruthBridge
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} (φ : Formula (WithParams Const) Γ) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    Le (Base := Base) (Const := Const) W V →
      ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
        RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ↔
          Forces (Base := Base) (Const := Const) V (subst ρ φ)

theorem closedTruthAbove_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (hφ : ClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    ClosedTruthAbove (Base := Base) (Const := Const) V φ := by
  intro U hVU
  exact hφ U (le_trans (Base := Base) (Const := Const) hWV hVU)

theorem levelClosedTruthAbove_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : LevelClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    LevelClosedTruthAbove (Base := Base) (Const := Const) V φ := by
  intro U hVU
  exact hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU)

theorem levelClosedTruthAbove_of_closedTruthAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    LevelClosedTruthAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV
  exact hφ V hWV.2

theorem bodyClosedTruthBridge_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (hφ : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) V φ := by
  intro U hVU t
  exact hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) t

theorem openTruthBridge_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ) :
    OpenTruthBridge (Base := Base) (Const := Const) V φ := by
  intro U hVU ρ
  exact hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ

theorem bodyClosedTruthBridge_of_openTruthBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W φ := by
  intro V hWV t
  simpa [ClosedEnv.subst_extend_empty] using
    hφ V hWV
      (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
        (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t)

theorem closedTruthAt_of_openTruthBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ) :
    ClosedTruthAt (Base := Base) (Const := Const) W φ := by
  simpa [ClosedTruthAt, RecursiveForces, ClosedEnv.subst_empty] using
    hφ W (le_refl (Base := Base) (Const := Const) W)
      (ClosedEnv.empty (Base := Base) (Const := WithParams Const))

theorem closedTruthAbove_of_openTruthBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV
  exact closedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (openTruthBridge_mono (Base := Base) (Const := Const) hWV hφ)

theorem openTruthBridge_var
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (v : Var Γ propTy) :
    OpenTruthBridge (Base := Base) (Const := Const) W
      (.var v : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  simp [RecursiveForcesOpen, Forces, Atom]

theorem openTruthBridge_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (c : WithParams Const propTy) :
    OpenTruthBridge (Base := Base) (Const := Const) W
      (.const c : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  simp [RecursiveForcesOpen, Forces, Atom, subst]

theorem openTruthBridge_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base}
    (f : Term (WithParams Const) Γ (σ ⇒ propTy)) (t : Term (WithParams Const) Γ σ) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.app f t) := by
  intro V _hWV ρ
  simp [RecursiveForcesOpen, Forces, Atom, subst]

theorem openTruthBridge_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    OpenTruthBridge (Base := Base) (Const := Const) W
      (.top : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  constructor
  · intro _
    simpa [subst] using forces_top (Base := Base) (Const := Const) V
  · intro _
    simp [RecursiveForcesOpen]

theorem openTruthBridge_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    OpenTruthBridge (Base := Base) (Const := Const) W
      (.bot : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  constructor
  · intro h
    simp [RecursiveForcesOpen] at h
  · intro h
    exact False.elim (forces_bot (Base := Base) (Const := Const) V
      (by simpa [subst] using h))

theorem openTruthBridge_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} (s t : Term (WithParams Const) Γ τ) :
    OpenTruthBridge (Base := Base) (Const := Const) W
      (.eq s t : Formula (WithParams Const) Γ) := by
  intro V _hWV ρ
  simp [RecursiveForcesOpen, Forces, EqVal, subst]

theorem openTruthBridge_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthBridge (Base := Base) (Const := Const) W ψ) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.and φ ψ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hPair :
        RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∧
          RecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ := by
      simpa [RecursiveForcesOpen] using h
    have hAnd : Forces (Base := Base) (Const := Const) V
        (.and (subst ρ φ) (subst ρ ψ)) :=
      (forces_and (Base := Base) (Const := Const)).mpr
        ⟨(hφ V hWV ρ).mp hPair.1, (hψ V hWV ρ).mp hPair.2⟩
    simpa [subst] using hAnd
  · intro h
    have hAnd : Forces (Base := Base) (Const := Const) V
        (.and (subst ρ φ) (subst ρ ψ)) := by
      simpa [subst] using h
    have hPair :
        RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∧
          RecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ :=
      ⟨(hφ V hWV ρ).mpr ((forces_and (Base := Base) (Const := Const)).mp hAnd).1,
        (hψ V hWV ρ).mpr ((forces_and (Base := Base) (Const := Const)).mp hAnd).2⟩
    simpa [RecursiveForcesOpen] using hPair

theorem openTruthBridge_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hSupport :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
            SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)))
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthBridge (Base := Base) (Const := Const) W ψ) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hOr : Forces (Base := Base) (Const := Const) V
        (.or (subst ρ φ) (subst ρ ψ)) := by
      rcases (by simpa [RecursiveForcesOpen] using h) with hφ' | hψ'
      · exact (forces_or_at (Base := Base) (Const := Const)
          (W := V) (by simpa [subst] using hSupport V hWV ρ)).mpr
          (Or.inl ((hφ V hWV ρ).mp hφ'))
      · exact (forces_or_at (Base := Base) (Const := Const)
          (W := V) (by simpa [subst] using hSupport V hWV ρ)).mpr
          (Or.inr ((hψ V hWV ρ).mp hψ'))
    simpa [subst] using hOr
  · intro h
    have hOr : Forces (Base := Base) (Const := Const) V
        (.or (subst ρ φ) (subst ρ ψ)) := by
      simpa [subst] using h
    rcases (forces_or_at (Base := Base) (Const := Const)
        (W := V) (by simpa [subst] using hSupport V hWV ρ)).mp hOr with hφ' | hψ'
    · simpa [RecursiveForcesOpen] using
        (Or.inl ((hφ V hWV ρ).mpr hφ') :
          RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
            RecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)
    · simpa [RecursiveForcesOpen] using
        (Or.inr ((hψ V hWV ρ).mpr hψ') :
          RecursiveForcesOpen (Base := Base) (Const := Const) V φ ρ ∨
            RecursiveForcesOpen (Base := Base) (Const := Const) V ψ ρ)

theorem openTruthBridge_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthBridge (Base := Base) (Const := Const) W ψ) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
              RecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ := by
      simpa [RecursiveForcesOpen] using h
    have hImp : Forces (Base := Base) (Const := Const) V
        (.imp (subst ρ φ) (subst ρ ψ)) := by
      apply (forces_imp_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU hφU
      exact (hψ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ).mp
        (hRec U hVU
          ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ).mpr hφU))
    simpa [subst] using hImp
  · intro h
    have hImp : Forces (Base := Base) (Const := Const) V
        (.imp (subst ρ φ) (subst ρ ψ)) := by
      simpa [subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ →
              RecursiveForcesOpen (Base := Base) (Const := Const) U ψ ρ := by
      intro U hVU hφU
      exact (hψ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ).mpr
        ((forces_imp_provider (Base := Base) (Const := Const) P V).mp hImp U hVU
          ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ).mp hφU))
    simpa [RecursiveForcesOpen] using hRec

theorem openTruthBridge_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.not φ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            ¬ RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ := by
      simpa [RecursiveForcesOpen] using h
    have hNot : Forces (Base := Base) (Const := Const) V (.not (subst ρ φ)) := by
      apply (forces_not_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU hφU
      exact hRec U hVU
        ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ).mpr hφU)
    simpa [subst] using hNot
  · intro h
    have hNot : Forces (Base := Base) (Const := Const) V (.not (subst ρ φ)) := by
      simpa [subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            ¬ RecursiveForcesOpen (Base := Base) (Const := Const) U φ ρ := by
      intro U hVU hφU
      exact (forces_not_provider (Base := Base) (Const := Const) P V).mp hNot U hVU
        ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ).mp hφU)
    simpa [RecursiveForcesOpen] using hRec

theorem openTruthBridge_all
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.all φ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            ∀ t : ClosedTerm (WithParams Const) σ,
              RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                (ClosedEnv.extend (Base := Base) ρ t) := by
      simpa [RecursiveForcesOpen] using h
    have hAll : Forces (Base := Base) (Const := Const) V
        (.all (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      apply (forces_all_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU t
      have hBody :=
        (hφ U (le_trans (Base := Base) (Const := Const) hWV hVU)
          (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mp
          (hRec U hVU t)
      simpa [ClosedEnv.instantiate_subst_lift_extend] using hBody
    simpa [subst] using hAll
  · intro h
    have hAll : Forces (Base := Base) (Const := Const) V
        (.all (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      simpa [subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            ∀ t : ClosedTerm (WithParams Const) σ,
              RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                (ClosedEnv.extend (Base := Base) ρ t) := by
      intro U hVU t
      have hInst :=
        (forces_all_provider (Base := Base) (Const := Const) P V).mp hAll U hVU t
      exact (hφ U (le_trans (Base := Base) (Const := Const) hWV hVU)
        (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mpr
        (by simpa [ClosedEnv.instantiate_subst_lift_extend] using hInst)
    simpa [RecursiveForcesOpen] using hRec

theorem openTruthBridge_ex_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hSupport :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
            SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ : Formula (WithParams Const) Γ)))
    (hφ : OpenTruthBridge (Base := Base) (Const := Const) W φ) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.ex φ) := by
  intro V hWV ρ
  constructor
  · intro h
    have hRec :
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) V U →
              RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                (ClosedEnv.extend (Base := Base) ρ t) := by
      simpa [RecursiveForcesOpen] using h
    have hEx : Forces (Base := Base) (Const := Const) V
        (.ex (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      rw [forces_ex_kripke_at (Base := Base) (Const := Const) (W := V)
        (by simpa [subst] using hSupport V hWV ρ)]
      rcases hRec with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      intro U hVU
      have hBody :=
        (hφ U (le_trans (Base := Base) (Const := Const) hWV hVU)
          (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mp
          (ht U hVU)
      simpa [ClosedEnv.instantiate_subst_lift_extend] using hBody
    simpa [subst] using hEx
  · intro h
    have hEx : Forces (Base := Base) (Const := Const) V
        (.ex (subst (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) ρ) φ) :
          ClosedFormula (WithParams Const)) := by
      simpa [subst] using h
    have hRec :
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) V U →
              RecursiveForcesOpen (Base := Base) (Const := Const) U φ
                (ClosedEnv.extend (Base := Base) ρ t) := by
      rw [forces_ex_kripke_at (Base := Base) (Const := Const) (W := V)
        (by simpa [subst] using hSupport V hWV ρ)] at hEx
      rcases hEx with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      intro U hVU
      exact (hφ U (le_trans (Base := Base) (Const := Const) hWV hVU)
        (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t)).mpr
        (by simpa [ClosedEnv.instantiate_subst_lift_extend] using ht U hVU)
    simpa [RecursiveForcesOpen] using hRec


end SupportedCanonicalFrame

end KripkeHenkin

end Mettapedia.Logic.HOL
