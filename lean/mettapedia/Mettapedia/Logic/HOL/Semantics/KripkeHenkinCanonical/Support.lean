import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical.Recursive

/-!
# Parameter-support tower for canonical truth bridges

Support predicates and structural lemmas for the open, level-open, body-closed,
and parameter-extended truth bridges used by the supported canonical packaging
layer.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin

namespace SupportedCanonicalFrame

open ClosedTheorySet

/-- Support obligations for the open truth bridge induction.  Atomic, boolean
negative, implication, and universal cases need no local support data; the
local disjunction and existential clauses require support after every
environmental closing at every successor world. -/
def OpenTruthSupport
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const) :
    {Γ : Ctx Base} → Formula (WithParams Const) Γ → Prop
  | _, .var _ => True
  | _, .const _ => True
  | _, .app _ _ => True
  | _, .top => True
  | _, .bot => True
  | _, .and φ ψ => OpenTruthSupport W φ ∧ OpenTruthSupport W ψ
  | _, .or φ ψ =>
      OpenTruthSupport W φ ∧ OpenTruthSupport W ψ ∧
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
              SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ))
  | _, .imp φ ψ => OpenTruthSupport W φ ∧ OpenTruthSupport W ψ
  | _, .not φ => OpenTruthSupport W φ
  | _, .eq _ _ => True
  | _, .all φ => OpenTruthSupport W φ
  | _, .ex φ =>
      OpenTruthSupport W φ ∧
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
              SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ))
termination_by _Γ φ => sizeOf φ

/-- Level-aware support obligations for the level-recursive open truth bridge.
This is the raw-world version of `OpenTruthSupport`: local disjunction and
existential support is required only along the level-aware preorder. -/
def LevelOpenTruthSupport
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const) :
    {Γ : Ctx Base} → Formula (WithParams Const) Γ → Prop
  | _, .var _ => True
  | _, .const _ => True
  | _, .app _ _ => True
  | _, .top => True
  | _, .bot => True
  | _, .and φ ψ => LevelOpenTruthSupport W φ ∧ LevelOpenTruthSupport W ψ
  | _, .or φ ψ =>
      LevelOpenTruthSupport W φ ∧ LevelOpenTruthSupport W ψ ∧
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
              SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ))
  | _, .imp φ ψ => LevelOpenTruthSupport W φ ∧ LevelOpenTruthSupport W ψ
  | _, .not φ => LevelOpenTruthSupport W φ
  | _, .eq _ _ => True
  | _, .all φ => LevelOpenTruthSupport W φ
  | _, .ex φ =>
      LevelOpenTruthSupport W φ ∧
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
              SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ))
termination_by _Γ φ => sizeOf φ

/-- Ordinary support obligations imply the level-aware ones by forgetting the
level component of accessibility. -/
theorem levelOpenTruthSupport_of_openTruthSupport
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    {Γ : Ctx Base} → (φ : Formula (WithParams Const) Γ) →
      OpenTruthSupport (Base := Base) (Const := Const) W φ →
        LevelOpenTruthSupport (Base := Base) (Const := Const) W φ
  | _, .var _, _ => by simp [LevelOpenTruthSupport]
  | _, .const _, _ => by simp [LevelOpenTruthSupport]
  | _, .app _ _, _ => by simp [LevelOpenTruthSupport]
  | _, .top, _ => by simp [LevelOpenTruthSupport]
  | _, .bot, _ => by simp [LevelOpenTruthSupport]
  | _, .and φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ :=
        ⟨levelOpenTruthSupport_of_openTruthSupport φ h'.1,
          levelOpenTruthSupport_of_openTruthSupport ψ h'.2⟩
      simpa [LevelOpenTruthSupport] using hPair
  | _, .or φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
            ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              Le (Base := Base) (Const := Const) W V →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)) := by
        simpa [OpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
            ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              LevelLe (Base := Base) (Const := Const) W V →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)) := by
        refine ⟨levelOpenTruthSupport_of_openTruthSupport φ h'.1,
          levelOpenTruthSupport_of_openTruthSupport ψ h'.2.1, ?_⟩
        intro V hWV ρ
        exact h'.2.2 V hWV.2 ρ
      simpa [LevelOpenTruthSupport] using hPair
  | _, .imp φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ :=
        ⟨levelOpenTruthSupport_of_openTruthSupport φ h'.1,
          levelOpenTruthSupport_of_openTruthSupport ψ h'.2⟩
      simpa [LevelOpenTruthSupport] using hPair
  | _, .not φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      simpa [LevelOpenTruthSupport] using levelOpenTruthSupport_of_openTruthSupport φ h'
  | _, .eq _ _, _ => by simp [LevelOpenTruthSupport]
  | _, .all φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      simpa [LevelOpenTruthSupport] using levelOpenTruthSupport_of_openTruthSupport φ h'
  | _, .ex φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W V →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ)) := by
        simpa [OpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W V →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ)) := by
        refine ⟨levelOpenTruthSupport_of_openTruthSupport φ h'.1, ?_⟩
        intro V hWV ρ
        exact h'.2 V hWV.2 ρ
      simpa [LevelOpenTruthSupport] using hPair
termination_by _Γ φ _ => sizeOf φ

/-- `LevelOpenTruthSupport` is monotone along level-aware successor worlds. -/
theorem levelOpenTruthSupport_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hWV : LevelLe (Base := Base) (Const := Const) W V) :
    {Γ : Ctx Base} → (φ : Formula (WithParams Const) Γ) →
      LevelOpenTruthSupport (Base := Base) (Const := Const) W φ →
        LevelOpenTruthSupport (Base := Base) (Const := Const) V φ
  | _, .var _, _ => by simp [LevelOpenTruthSupport]
  | _, .const _, _ => by simp [LevelOpenTruthSupport]
  | _, .app _ _, _ => by simp [LevelOpenTruthSupport]
  | _, .top, _ => by simp [LevelOpenTruthSupport]
  | _, .bot, _ => by simp [LevelOpenTruthSupport]
  | _, .and φ ψ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [LevelOpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) V ψ :=
        ⟨levelOpenTruthSupport_mono hWV φ h'.1,
          levelOpenTruthSupport_mono hWV ψ h'.2⟩
      simpa [LevelOpenTruthSupport] using hPair
  | _, .or φ ψ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              LevelLe (Base := Base) (Const := Const) W U →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) U (subst ρ (.or φ ψ)) := by
        simpa [LevelOpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) V ψ ∧
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              LevelLe (Base := Base) (Const := Const) V U →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) U (subst ρ (.or φ ψ)) := by
        refine ⟨levelOpenTruthSupport_mono hWV φ h'.1,
          levelOpenTruthSupport_mono hWV ψ h'.2.1, ?_⟩
        intro U hVU ρ
        exact h'.2.2 U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ
      simpa [LevelOpenTruthSupport] using hPair
  | _, .imp φ ψ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [LevelOpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) V ψ :=
        ⟨levelOpenTruthSupport_mono hWV φ h'.1,
          levelOpenTruthSupport_mono hWV ψ h'.2⟩
      simpa [LevelOpenTruthSupport] using hPair
  | _, .not φ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [LevelOpenTruthSupport] using h
      simpa [LevelOpenTruthSupport] using levelOpenTruthSupport_mono hWV φ h'
  | _, .eq _ _, _ => by simp [LevelOpenTruthSupport]
  | _, .all φ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [LevelOpenTruthSupport] using h
      simpa [LevelOpenTruthSupport] using levelOpenTruthSupport_mono hWV φ h'
  | _, .ex φ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W U →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) U (subst ρ (.ex φ)) := by
        simpa [LevelOpenTruthSupport] using h
      have hPair : LevelOpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) V U →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) U (subst ρ (.ex φ)) := by
        refine ⟨levelOpenTruthSupport_mono hWV φ h'.1, ?_⟩
        intro U hVU ρ
        exact h'.2 U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ
      simpa [LevelOpenTruthSupport] using hPair
termination_by _Γ φ _ => sizeOf φ

/-- A formula is supported above a world when every ordinary carrier-extension
successor supports every closed instance of it.  This is stronger than a
single `SupportedAt W (subst ρ φ)` fact, and matches the `Le` successors used
by implication and universal forcing. -/
def OpenSupportedAbove
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} (φ : Formula (WithParams Const) Γ) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    Le (Base := Base) (Const := Const) W V →
      ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
        SupportedAt (Base := Base) (Const := Const) V (subst ρ φ)

/-- Level-aware support above a world.  This is the support invariant supplied
by the raw level construction; turning it into `OpenSupportedAbove` for the
ordinary carrier preorder requires an additional theorem that ordinary
successors preserve or increase levels. -/
def LevelOpenSupportedAbove
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} (φ : Formula (WithParams Const) Γ) : Prop :=
  ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    LevelLe (Base := Base) (Const := Const) W V →
      ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
        SupportedAt (Base := Base) (Const := Const) V (subst ρ φ)

/-- A formula is open-supported at a world when every closed environment
instance is inside that world's current parameter budget. -/
def OpenSupportedAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} (φ : Formula (WithParams Const) Γ) : Prop :=
  ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
    SupportedAt (Base := Base) (Const := Const) W (subst ρ φ)

/-- Parameter-budget support for an open term before closing it by an
environment. -/
def TermSupportedAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term (WithParams Const) Γ τ) : Prop :=
  maxParam t ≤ W.level

/-- Renaming variables does not change the parameter constants occurring in a
term. -/
theorem maxParam_rename
    {Γ Δ : Ctx Base} {τ : Ty Base} (ρ : Rename Base Γ Δ)
    (t : Term (WithParams Const) Γ τ) :
    maxParam (rename (Base := Base) (Const := WithParams Const) ρ t) =
      maxParam t := by
  induction t generalizing Δ with
  | var v => rfl
  | const c => rfl
  | app f t hf ht =>
      simp [rename, maxParam, hf (ρ := ρ), ht (ρ := ρ)]
  | lam t ih =>
      simp [rename, maxParam, ih (ρ := Rename.lift (Base := Base) ρ)]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ =>
      simp [rename, maxParam, hφ (ρ := ρ), hψ (ρ := ρ)]
  | or φ ψ hφ hψ =>
      simp [rename, maxParam, hφ (ρ := ρ), hψ (ρ := ρ)]
  | imp φ ψ hφ hψ =>
      simp [rename, maxParam, hφ (ρ := ρ), hψ (ρ := ρ)]
  | not φ hφ =>
      simp [rename, maxParam, hφ (ρ := ρ)]
  | eq s t hs ht =>
      simp [rename, maxParam, hs (ρ := ρ), ht (ρ := ρ)]
  | all φ hφ =>
      simp [rename, maxParam, hφ (ρ := Rename.lift (Base := Base) ρ)]
  | ex φ hφ =>
      simp [rename, maxParam, hφ (ρ := Rename.lift (Base := Base) ρ)]

theorem maxParam_weaken
    {Γ : Ctx Base} {σ τ : Ty Base} (t : Term (WithParams Const) Γ τ) :
    maxParam (weaken (Base := Base) (Const := WithParams Const) (σ := σ) t) =
      maxParam t := by
  simpa [weaken] using
    (maxParam_rename (Base := Base) (Const := Const)
      (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t)

/-- A closed environment is supported at a world when every term it assigns to
a variable stays inside that world's current parameter budget. -/
def EnvSupportedAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} (ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ) : Prop :=
  ∀ {τ : Ty Base} (v : Var Γ τ),
    TermSupportedAt (Base := Base) (Const := Const) W (ρ v)

/-- A substitution is supported at a world when every image term stays inside
that world's current parameter budget.  Unlike `EnvSupportedAt`, this allows
nonempty codomains and is therefore the form needed under binders. -/
def SubstSupportedAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ Δ : Ctx Base} (σs : Subst (WithParams Const) Γ Δ) : Prop :=
  ∀ {τ : Ty Base} (v : Var Γ τ),
    TermSupportedAt (Base := Base) (Const := Const) W (σs v)

theorem substSupportedAt_of_envSupportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    (hρ : EnvSupportedAt (Base := Base) (Const := Const) W ρ) :
    SubstSupportedAt (Base := Base) (Const := Const) W ρ := hρ

theorem envSupportedAt_empty
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    EnvSupportedAt (Base := Base) (Const := Const) W
      (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) := by
  intro τ v
  cases v

theorem envSupportedAt_extend
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base}
    {ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    {t : ClosedTerm (WithParams Const) σ}
    (hρ : EnvSupportedAt (Base := Base) (Const := Const) W ρ)
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    EnvSupportedAt (Base := Base) (Const := Const) W
      (ClosedEnv.extend (Base := Base) (Const := WithParams Const) ρ t) := by
  intro τ v
  cases v with
  | vz =>
      simpa [ClosedEnv.extend] using ht
  | vs v =>
      simpa [ClosedEnv.extend] using hρ v

theorem substSupportedAt_lift
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ Δ : Ctx Base} {σ : Ty Base}
    {σs : Subst (WithParams Const) Γ Δ}
    (hσs : SubstSupportedAt (Base := Base) (Const := Const) W σs) :
    SubstSupportedAt (Base := Base) (Const := Const) W
      (Subst.lift (Base := Base) (Const := WithParams Const) (σ := σ) σs) := by
  intro τ v
  cases v with
  | vz =>
      simp [Subst.lift, TermSupportedAt, maxParam]
  | vs v =>
      simpa [Subst.lift, TermSupportedAt, maxParam_rename] using hσs v

/-- Substitution by supported image terms preserves the world's parameter
budget.  This is the binder-aware support theorem used by quantifier and
abstraction cases. -/
theorem termSupportedAt_subst
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ Δ : Ctx Base} {τ : Ty Base}
    {σs : Subst (WithParams Const) Γ Δ}
    (hσs : SubstSupportedAt (Base := Base) (Const := Const) W σs)
    (t : Term (WithParams Const) Γ τ)
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    TermSupportedAt (Base := Base) (Const := Const) W (subst σs t) := by
  induction t generalizing Δ with
  | var v =>
      simpa [TermSupportedAt, subst] using hσs v
  | const c =>
      simpa [TermSupportedAt, subst, maxParam] using ht
  | app f t hf ht' =>
      have hBound : maxParam f ≤ W.level ∧ maxParam t ≤ W.level := by
        exact (Nat.max_le).mp (by simpa [TermSupportedAt, maxParam] using ht)
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          (Nat.max_le).mpr
            ⟨hf hσs hBound.1, ht' hσs hBound.2⟩)
  | lam body ih =>
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          ih (substSupportedAt_lift (Base := Base) (Const := Const) hσs)
            (by simpa [TermSupportedAt, maxParam] using ht))
  | top =>
      simp [TermSupportedAt, subst, maxParam]
  | bot =>
      simp [TermSupportedAt, subst, maxParam]
  | and φ ψ hφ hψ =>
      have hBound : maxParam φ ≤ W.level ∧ maxParam ψ ≤ W.level := by
        exact (Nat.max_le).mp (by simpa [TermSupportedAt, maxParam] using ht)
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          (Nat.max_le).mpr
            ⟨hφ hσs hBound.1, hψ hσs hBound.2⟩)
  | or φ ψ hφ hψ =>
      have hBound : maxParam φ ≤ W.level ∧ maxParam ψ ≤ W.level := by
        exact (Nat.max_le).mp (by simpa [TermSupportedAt, maxParam] using ht)
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          (Nat.max_le).mpr
            ⟨hφ hσs hBound.1, hψ hσs hBound.2⟩)
  | imp φ ψ hφ hψ =>
      have hBound : maxParam φ ≤ W.level ∧ maxParam ψ ≤ W.level := by
        exact (Nat.max_le).mp (by simpa [TermSupportedAt, maxParam] using ht)
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          (Nat.max_le).mpr
            ⟨hφ hσs hBound.1, hψ hσs hBound.2⟩)
  | not φ hφ =>
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          hφ hσs (by simpa [TermSupportedAt, maxParam] using ht))
  | eq s t hs ht' =>
      have hBound : maxParam s ≤ W.level ∧ maxParam t ≤ W.level := by
        exact (Nat.max_le).mp (by simpa [TermSupportedAt, maxParam] using ht)
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          (Nat.max_le).mpr
            ⟨hs hσs hBound.1, ht' hσs hBound.2⟩)
  | all φ hφ =>
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          hφ (substSupportedAt_lift (Base := Base) (Const := Const) hσs)
            (by simpa [TermSupportedAt, maxParam] using ht))
  | ex φ hφ =>
      exact (by
        simpa [TermSupportedAt, subst, maxParam] using
          hφ (substSupportedAt_lift (Base := Base) (Const := Const) hσs)
            (by simpa [TermSupportedAt, maxParam] using ht))

/-- Bounded open support: every closing environment whose assigned terms are
supported at the world closes the term to a supported closed term. -/
def BoundedTermSupportedAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term (WithParams Const) Γ τ) : Prop :=
  ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
    EnvSupportedAt (Base := Base) (Const := Const) W ρ →
      TermSupportedAt (Base := Base) (Const := Const) W (subst ρ t)

/-- Bounded open support specialized to proposition-valued terms. -/
abbrev BoundedOpenSupportedAt
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const)
    {Γ : Ctx Base} (φ : Formula (WithParams Const) Γ) : Prop :=
  BoundedTermSupportedAt (Base := Base) (Const := Const) W φ

theorem boundedTermSupportedAt_of_termSupportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} {t : Term (WithParams Const) Γ τ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    BoundedTermSupportedAt (Base := Base) (Const := Const) W t := by
  intro ρ hρ
  exact termSupportedAt_subst (Base := Base) (Const := Const)
    (substSupportedAt_of_envSupportedAt (Base := Base) (Const := Const) hρ) t ht

theorem termSupportedAt_subst_of_bounded
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} {t : Term (WithParams Const) Γ τ}
    (ht : BoundedTermSupportedAt (Base := Base) (Const := Const) W t)
    {ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    (hρ : EnvSupportedAt (Base := Base) (Const := Const) W ρ) :
    TermSupportedAt (Base := Base) (Const := Const) W (subst ρ t) :=
  ht ρ hρ

theorem supportedAt_of_boundedOpenSupportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ)
    {ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    (hρ : EnvSupportedAt (Base := Base) (Const := Const) W ρ) :
    SupportedAt (Base := Base) (Const := Const) W (subst ρ φ) :=
  hφ ρ hρ

theorem supportedAt_instantiate_of_bounded_body
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ)
    {t : ClosedTerm (WithParams Const) σ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    SupportedAt (Base := Base) (Const := Const) W
      (instantiate (Base := Base) t φ) := by
  have hρ :
      EnvSupportedAt (Base := Base) (Const := Const) W
        (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
          (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) :=
    envSupportedAt_extend (Base := Base) (Const := Const)
      envSupportedAt_empty ht
  simpa [ClosedEnv.subst_extend_empty] using
    supportedAt_of_boundedOpenSupportedAt (Base := Base) (Const := Const)
      (W := W) (φ := φ) hφ hρ

theorem termSupportedAt_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} {t : Term (WithParams Const) Γ τ}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    TermSupportedAt (Base := Base) (Const := Const) V t :=
  Nat.le_trans ht hWV.1

theorem envSupportedAt_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hρ : EnvSupportedAt (Base := Base) (Const := Const) W ρ) :
    EnvSupportedAt (Base := Base) (Const := Const) V ρ := by
  intro τ v
  exact termSupportedAt_mono (Base := Base) (Const := Const) hWV (hρ v)

theorem termSupportedAt_subst_of_bounded_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} {t : Term (WithParams Const) Γ τ}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (ht : BoundedTermSupportedAt (Base := Base) (Const := Const) W t)
    {ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    (hρ : EnvSupportedAt (Base := Base) (Const := Const) W ρ) :
    TermSupportedAt (Base := Base) (Const := Const) V (subst ρ t) :=
  termSupportedAt_mono (Base := Base) (Const := Const) hWV
    (termSupportedAt_subst_of_bounded (Base := Base) (Const := Const) ht hρ)

theorem supportedAt_of_boundedOpenSupportedAt_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ)
    {ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ}
    (hρ : EnvSupportedAt (Base := Base) (Const := Const) W ρ) :
    SupportedAt (Base := Base) (Const := Const) V (subst ρ φ) :=
  termSupportedAt_subst_of_bounded_mono (Base := Base) (Const := Const)
    hWV hφ hρ

theorem supportedAt_instantiate_of_bounded_body_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ)
    {t : ClosedTerm (WithParams Const) σ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    SupportedAt (Base := Base) (Const := Const) V
      (instantiate (Base := Base) t φ) :=
  supportedAt_mono (Base := Base) (Const := Const) hWV
    (supportedAt_instantiate_of_bounded_body (Base := Base) (Const := Const)
      hφ ht)

theorem supportedAt_instantiate_of_termSupportedAt_body_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : TermSupportedAt (Base := Base) (Const := Const) W φ)
    {t : ClosedTerm (WithParams Const) σ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    SupportedAt (Base := Base) (Const := Const) V
      (instantiate (Base := Base) t φ) :=
  supportedAt_instantiate_of_bounded_body_mono (Base := Base) (Const := Const)
    hWV
    (boundedTermSupportedAt_of_termSupportedAt (Base := Base) (Const := Const) hφ)
    ht

theorem supportedAt_instantiate_of_supported_all
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hAll : SupportedAt (Base := Base) (Const := Const)
      W (.all φ : ClosedFormula (WithParams Const)))
    {t : ClosedTerm (WithParams Const) σ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    SupportedAt (Base := Base) (Const := Const) W
      (instantiate (Base := Base) t φ) :=
  supportedAt_instantiate_of_termSupportedAt_body_mono
    (Base := Base) (Const := Const)
    (levelLe_refl (Base := Base) (Const := Const) W)
    (supported_all_body (Base := Base) (Const := Const) (W := W) hAll)
    ht

theorem supportedAt_instantiate_of_supported_ex
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hEx : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const)))
    {t : ClosedTerm (WithParams Const) σ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) W t) :
    SupportedAt (Base := Base) (Const := Const) W
      (instantiate (Base := Base) t φ) :=
  supportedAt_instantiate_of_termSupportedAt_body_mono
    (Base := Base) (Const := Const)
    (levelLe_refl (Base := Base) (Const := Const) W)
    (supported_ex_body (Base := Base) (Const := Const) (W := W) hEx)
    ht

theorem supportedAt_instantiate_of_supported_all_above
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hAll : SupportedAt (Base := Base) (Const := Const)
      W (.all φ : ClosedFormula (WithParams Const)))
    {t : ClosedTerm (WithParams Const) σ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) V t) :
    SupportedAt (Base := Base) (Const := Const) V
      (instantiate (Base := Base) t φ) :=
  supportedAt_instantiate_of_supported_all (Base := Base) (Const := Const)
    (supportedAt_mono (Base := Base) (Const := Const) hWV hAll) ht

theorem supportedAt_instantiate_of_supported_ex_above
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hEx : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const)))
    {t : ClosedTerm (WithParams Const) σ}
    (ht : TermSupportedAt (Base := Base) (Const := Const) V t) :
    SupportedAt (Base := Base) (Const := Const) V
      (instantiate (Base := Base) t φ) :=
  supportedAt_instantiate_of_supported_ex (Base := Base) (Const := Const)
    (supportedAt_mono (Base := Base) (Const := Const) hWV hEx) ht

theorem boundedTermSupportedAt_var
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} (v : Var Γ τ) :
    BoundedTermSupportedAt (Base := Base) (Const := Const) W
      (.var v : Term (WithParams Const) Γ τ) := by
  intro ρ hρ
  simpa [BoundedTermSupportedAt, TermSupportedAt, subst] using hρ v

theorem boundedTermSupportedAt_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} (c : WithParams Const τ)
    (hc : TermSupportedAt (Base := Base) (Const := Const) W
      (.const c : Term (WithParams Const) Γ τ)) :
    BoundedTermSupportedAt (Base := Base) (Const := Const) W
      (.const c : Term (WithParams Const) Γ τ) := by
  intro ρ _hρ
  simpa [TermSupportedAt, subst, maxParam] using hc

theorem boundedTermSupportedAt_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ τ : Ty Base}
    {f : Term (WithParams Const) Γ (σ ⇒ τ)} {t : Term (WithParams Const) Γ σ}
    (hf : BoundedTermSupportedAt (Base := Base) (Const := Const) W f)
    (ht : BoundedTermSupportedAt (Base := Base) (Const := Const) W t) :
    BoundedTermSupportedAt (Base := Base) (Const := Const) W (.app f t) := by
  intro ρ hρ
  have hf' := hf ρ hρ
  have ht' := ht ρ hρ
  simpa [BoundedTermSupportedAt, TermSupportedAt, subst, maxParam] using
    (Nat.max_le).mpr ⟨hf', ht'⟩

theorem boundedOpenSupportedAt_var
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (v : Var Γ propTy) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W
      (.var v : Formula (WithParams Const) Γ) :=
  boundedTermSupportedAt_var (Base := Base) (Const := Const) v

theorem boundedOpenSupportedAt_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (c : WithParams Const propTy)
    (hc : TermSupportedAt (Base := Base) (Const := Const) W
      (.const c : Formula (WithParams Const) Γ)) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W
      (.const c : Formula (WithParams Const) Γ) :=
  boundedTermSupportedAt_const (Base := Base) (Const := Const) c hc

theorem boundedOpenSupportedAt_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base}
    {f : Term (WithParams Const) Γ (σ ⇒ propTy)} {t : Term (WithParams Const) Γ σ}
    (hf : BoundedTermSupportedAt (Base := Base) (Const := Const) W f)
    (ht : BoundedTermSupportedAt (Base := Base) (Const := Const) W t) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W (.app f t) :=
  boundedTermSupportedAt_app (Base := Base) (Const := Const) hf ht

theorem boundedOpenSupportedAt_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W
      (.top : Formula (WithParams Const) Γ) := by
  intro ρ _hρ
  simp [TermSupportedAt, subst, maxParam]

theorem boundedOpenSupportedAt_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W
      (.bot : Formula (WithParams Const) Γ) := by
  intro ρ _hρ
  simp [TermSupportedAt, subst, maxParam]

theorem boundedOpenSupportedAt_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ)
    (hψ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W ψ) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W (.and φ ψ) := by
  intro ρ hρ
  have hφ' := hφ ρ hρ
  have hψ' := hψ ρ hρ
  simpa [BoundedTermSupportedAt, TermSupportedAt, subst, maxParam] using
    (Nat.max_le).mpr ⟨hφ', hψ'⟩

theorem boundedOpenSupportedAt_or
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ)
    (hψ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W ψ) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro ρ hρ
  have hφ' := hφ ρ hρ
  have hψ' := hψ ρ hρ
  simpa [BoundedTermSupportedAt, TermSupportedAt, subst, maxParam] using
    (Nat.max_le).mpr ⟨hφ', hψ'⟩

theorem boundedOpenSupportedAt_imp
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ)
    (hψ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W ψ) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro ρ hρ
  have hφ' := hφ ρ hρ
  have hψ' := hψ ρ hρ
  simpa [BoundedTermSupportedAt, TermSupportedAt, subst, maxParam] using
    (Nat.max_le).mpr ⟨hφ', hψ'⟩

theorem boundedOpenSupportedAt_not
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hφ : BoundedOpenSupportedAt (Base := Base) (Const := Const) W φ) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W (.not φ) := by
  intro ρ hρ
  simpa [BoundedTermSupportedAt, TermSupportedAt, subst, maxParam] using hφ ρ hρ

theorem boundedOpenSupportedAt_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} {s t : Term (WithParams Const) Γ τ}
    (hs : BoundedTermSupportedAt (Base := Base) (Const := Const) W s)
    (ht : BoundedTermSupportedAt (Base := Base) (Const := Const) W t) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W
      (.eq s t : Formula (WithParams Const) Γ) := by
  intro ρ hρ
  have hs' := hs ρ hρ
  have ht' := ht ρ hρ
  simpa [BoundedTermSupportedAt, TermSupportedAt, subst, maxParam] using
    (Nat.max_le).mpr ⟨hs', ht'⟩

theorem termSupportedAt_lam
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ τ : Ty Base} {body : Term (WithParams Const) (σ :: Γ) τ}
    (hbody : TermSupportedAt (Base := Base) (Const := Const) W body) :
    TermSupportedAt (Base := Base) (Const := Const) W (.lam body) := by
  simpa [TermSupportedAt, maxParam] using hbody

theorem termSupportedAt_all
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : TermSupportedAt (Base := Base) (Const := Const) W φ) :
    TermSupportedAt (Base := Base) (Const := Const) W (.all φ : Formula (WithParams Const) Γ) := by
  simpa [TermSupportedAt, maxParam] using hφ

theorem termSupportedAt_ex
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : TermSupportedAt (Base := Base) (Const := Const) W φ) :
    TermSupportedAt (Base := Base) (Const := Const) W (.ex φ : Formula (WithParams Const) Γ) := by
  simpa [TermSupportedAt, maxParam] using hφ

theorem boundedTermSupportedAt_lam_of_termSupportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ τ : Ty Base} {body : Term (WithParams Const) (σ :: Γ) τ}
    (hbody : TermSupportedAt (Base := Base) (Const := Const) W body) :
    BoundedTermSupportedAt (Base := Base) (Const := Const) W (.lam body) :=
  boundedTermSupportedAt_of_termSupportedAt (Base := Base) (Const := Const)
    (termSupportedAt_lam (Base := Base) (Const := Const) hbody)

theorem boundedOpenSupportedAt_all_of_termSupportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : TermSupportedAt (Base := Base) (Const := Const) W φ) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W
      (.all φ : Formula (WithParams Const) Γ) :=
  boundedTermSupportedAt_of_termSupportedAt (Base := Base) (Const := Const)
    (termSupportedAt_all (Base := Base) (Const := Const) hφ)

theorem boundedOpenSupportedAt_ex_of_termSupportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : TermSupportedAt (Base := Base) (Const := Const) W φ) :
    BoundedOpenSupportedAt (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) :=
  boundedTermSupportedAt_of_termSupportedAt (Base := Base) (Const := Const)
    (termSupportedAt_ex (Base := Base) (Const := Const) hφ)

theorem openSupportedAbove_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (hφ : OpenSupportedAbove (Base := Base) (Const := Const) W φ) :
    OpenSupportedAbove (Base := Base) (Const := Const) V φ := by
  intro U hVU ρ
  exact hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ

theorem levelOpenSupportedAbove_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : LevelOpenSupportedAbove (Base := Base) (Const := Const) W φ) :
    LevelOpenSupportedAbove (Base := Base) (Const := Const) V φ := by
  intro U hVU ρ
  exact hφ U (levelLe_trans (Base := Base) (Const := Const) hWV hVU) ρ

theorem openSupportedAt_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : OpenSupportedAt (Base := Base) (Const := Const) W φ) :
    OpenSupportedAt (Base := Base) (Const := Const) V φ := by
  intro ρ
  exact supportedAt_mono (Base := Base) (Const := Const) hWV (hφ ρ)

theorem levelOpenSupportedAbove_of_openSupportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hφ : OpenSupportedAt (Base := Base) (Const := Const) W φ) :
    LevelOpenSupportedAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV ρ
  exact openSupportedAt_mono (Base := Base) (Const := Const) hWV hφ ρ

theorem levelOpenSupportedAbove_of_openSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hφ : OpenSupportedAbove (Base := Base) (Const := Const) W φ) :
    LevelOpenSupportedAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV ρ
  exact hφ V hWV.2 ρ

theorem openSupportedAbove_of_levelOpenSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hφ : LevelOpenSupportedAbove (Base := Base) (Const := Const) W φ) :
    OpenSupportedAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV ρ
  exact hφ V ⟨hLevel V hWV, hWV⟩ ρ

theorem openSupportedAt_of_closed_supportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : SupportedAt (Base := Base) (Const := Const) W φ) :
    OpenSupportedAt (Base := Base) (Const := Const) W φ := by
  intro ρ
  simpa [ClosedEnv.subst_empty] using hφ

theorem levelOpenSupportedAbove_of_closed_supportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : SupportedAt (Base := Base) (Const := Const) W φ) :
    LevelOpenSupportedAbove (Base := Base) (Const := Const) W φ :=
  levelOpenSupportedAbove_of_openSupportedAt (Base := Base) (Const := Const)
    (openSupportedAt_of_closed_supportedAt (Base := Base) (Const := Const) hφ)

theorem levelOpenTruthSupport_var
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (v : Var Γ propTy) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.var v : Formula (WithParams Const) Γ) := by
  simp [LevelOpenTruthSupport]

theorem levelOpenTruthSupport_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} (c : WithParams Const propTy) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.const c : Formula (WithParams Const) Γ) := by
  simp [LevelOpenTruthSupport]

theorem levelOpenTruthSupport_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base}
    (f : Term (WithParams Const) Γ (σ ⇒ propTy)) (t : Term (WithParams Const) Γ σ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W (.app f t) := by
  simp [LevelOpenTruthSupport]

theorem levelOpenTruthSupport_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.top : Formula (WithParams Const) Γ) := by
  simp [LevelOpenTruthSupport]

theorem levelOpenTruthSupport_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.bot : Formula (WithParams Const) Γ) := by
  simp [LevelOpenTruthSupport]

theorem levelOpenTruthSupport_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W (.and φ ψ) := by
  simpa [LevelOpenTruthSupport] using And.intro hφ hψ

theorem levelOpenTruthSupport_or_of_levelOpenSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W (.or φ ψ) := by
  have h : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
      LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
              SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)) :=
    ⟨hφ, hψ, hOr⟩
  simpa [LevelOpenTruthSupport] using h

theorem levelOpenTruthSupport_ex_of_levelOpenSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ)) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) := by
  have h : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
            SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ)) :=
    ⟨hφ, hEx⟩
  simpa [LevelOpenTruthSupport] using h

theorem levelOpenTruthSupport_or_of_supportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelOpenTruthSupport_or_of_levelOpenSupportedAbove
    (Base := Base) (Const := Const) hφ hψ
    (levelOpenSupportedAbove_of_closed_supportedAt
      (Base := Base) (Const := Const) hSupport)

theorem levelOpenTruthSupport_imp
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W (.imp φ ψ) := by
  simpa [LevelOpenTruthSupport] using And.intro hφ hψ

theorem levelOpenTruthSupport_not
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W (.not φ) := by
  simpa [LevelOpenTruthSupport] using hφ

theorem levelOpenTruthSupport_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {τ : Ty Base} (s t : Term (WithParams Const) Γ τ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.eq s t : Formula (WithParams Const) Γ) := by
  simp [LevelOpenTruthSupport]

theorem levelOpenTruthSupport_all
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.all φ : Formula (WithParams Const) Γ) := by
  simpa [LevelOpenTruthSupport] using hφ

theorem levelOpenTruthSupport_ex_of_supportedAt
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)))
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelOpenTruthSupport (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelOpenTruthSupport_ex_of_levelOpenSupportedAbove
    (Base := Base) (Const := Const) hφ
    (levelOpenSupportedAbove_of_closed_supportedAt
      (Base := Base) (Const := Const) hSupport)

theorem openTruthSupport_or_of_openSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : OpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    OpenTruthSupport (Base := Base) (Const := Const) W (.or φ ψ) := by
  have h : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
      OpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
              SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)) :=
    ⟨hφ, hψ, hOr⟩
  simpa [OpenTruthSupport] using h

theorem openTruthSupport_or_of_levelOpenSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    OpenTruthSupport (Base := Base) (Const := Const) W (.or φ ψ) :=
  openTruthSupport_or_of_openSupportedAbove (Base := Base) (Const := Const) hφ hψ
    (openSupportedAbove_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) hLevel hOr)

theorem openTruthSupport_ex_of_openSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : OpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ)) :
    OpenTruthSupport (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) := by
  have h : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) Γ,
            SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ)) :=
    ⟨hφ, hEx⟩
  simpa [OpenTruthSupport] using h

theorem openTruthSupport_ex_of_levelOpenSupportedAbove
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ)) :
    OpenTruthSupport (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) :=
  openTruthSupport_ex_of_openSupportedAbove (Base := Base) (Const := Const) hφ
    (openSupportedAbove_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) hLevel hEx)

/-- Structural open truth bridge induction, conditional exactly on the local
support obligations for disjunctions and existentials. -/
theorem openTruthBridge_of_support
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const) :
    {Γ : Ctx Base} → (φ : Formula (WithParams Const) Γ) →
      OpenTruthSupport (Base := Base) (Const := Const) W φ →
        OpenTruthBridge (Base := Base) (Const := Const) W φ
  | _, .var v, _ => openTruthBridge_var (Base := Base) (Const := Const) v
  | _, .const c, _ => openTruthBridge_const (Base := Base) (Const := Const) c
  | _, .app f t, _ => openTruthBridge_atom_app (Base := Base) (Const := Const) f t
  | _, .top, _ => openTruthBridge_top (Base := Base) (Const := Const)
  | _, .bot, _ => openTruthBridge_bot (Base := Base) (Const := Const)
  | _, .and φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      exact openTruthBridge_and (Base := Base) (Const := Const)
        (openTruthBridge_of_support P W φ h'.1)
        (openTruthBridge_of_support P W ψ h'.2)
  | _, .or φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
            ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              Le (Base := Base) (Const := Const) W V →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)) := by
        simpa [OpenTruthSupport] using h
      exact openTruthBridge_or_supported (Base := Base) (Const := Const)
        (by intro V hWV ρ; exact h'.2.2 V hWV ρ)
        (openTruthBridge_of_support P W φ h'.1)
        (openTruthBridge_of_support P W ψ h'.2.1)
  | _, .imp φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      exact openTruthBridge_imp (Base := Base) (Const := Const) P
        (openTruthBridge_of_support P W φ h'.1)
        (openTruthBridge_of_support P W ψ h'.2)
  | _, .not φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      exact openTruthBridge_not (Base := Base) (Const := Const) P
        (openTruthBridge_of_support P W φ h')
  | _, .eq s t, _ => openTruthBridge_eq (Base := Base) (Const := Const) s t
  | _, .all φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      exact openTruthBridge_all (Base := Base) (Const := Const) P
        (openTruthBridge_of_support P W φ h')
  | _, .ex φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W V →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ)) := by
        simpa [OpenTruthSupport] using h
      exact openTruthBridge_ex_supported (Base := Base) (Const := Const)
        (by intro V hWV ρ; exact h'.2 V hWV ρ)
        (openTruthBridge_of_support P W φ h'.1)
termination_by _Γ φ _ => sizeOf φ

/-- Level-recursive structural open truth bridge induction, conditional on the
same support obligations as `openTruthBridge_of_support`.  The local
disjunction and existential support hypotheses are read along the carrier
component of the level-aware preorder. -/
theorem levelRecursiveOpenTruthBridge_of_support
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const) :
    {Γ : Ctx Base} → (φ : Formula (WithParams Const) Γ) →
      OpenTruthSupport (Base := Base) (Const := Const) W φ →
        LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ
  | _, .var v, _ => levelRecursiveOpenTruthBridge_var (Base := Base) (Const := Const) v
  | _, .const c, _ => levelRecursiveOpenTruthBridge_const (Base := Base) (Const := Const) c
  | _, .app f t, _ => levelRecursiveOpenTruthBridge_atom_app (Base := Base) (Const := Const) f t
  | _, .top, _ => levelRecursiveOpenTruthBridge_top (Base := Base) (Const := Const)
  | _, .bot, _ => levelRecursiveOpenTruthBridge_bot (Base := Base) (Const := Const)
  | _, .and φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_and (Base := Base) (Const := Const)
        (levelRecursiveOpenTruthBridge_of_support P W φ h'.1)
        (levelRecursiveOpenTruthBridge_of_support P W ψ h'.2)
  | _, .or φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
            ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              Le (Base := Base) (Const := Const) W V →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)) := by
        simpa [OpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_or_supported (Base := Base) (Const := Const)
        (by intro V hWV ρ; exact h'.2.2 V hWV.2 ρ)
        (levelRecursiveOpenTruthBridge_of_support P W φ h'.1)
        (levelRecursiveOpenTruthBridge_of_support P W ψ h'.2.1)
  | _, .imp φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_imp (Base := Base) (Const := Const) P
        (levelRecursiveOpenTruthBridge_of_support P W φ h'.1)
        (levelRecursiveOpenTruthBridge_of_support P W ψ h'.2)
  | _, .not φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_not (Base := Base) (Const := Const) P
        (levelRecursiveOpenTruthBridge_of_support P W φ h')
  | _, .eq s t, _ => levelRecursiveOpenTruthBridge_eq (Base := Base) (Const := Const) s t
  | _, .all φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_all (Base := Base) (Const := Const) P
        (levelRecursiveOpenTruthBridge_of_support P W φ h')
  | _, .ex φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W V →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ)) := by
        simpa [OpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_ex_supported (Base := Base) (Const := Const)
        (by intro V hWV ρ; exact h'.2 V hWV.2 ρ)
        (levelRecursiveOpenTruthBridge_of_support P W φ h'.1)
termination_by _Γ φ _ => sizeOf φ

theorem levelRecursiveBodyClosedTruthBridge_of_support
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ :=
  levelRecursiveBodyClosedTruthBridge_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)

theorem levelRecursiveClosedTruthAt_of_support
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W φ :=
  levelRecursiveClosedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)

/-- Level-recursive structural open truth bridge induction using the
level-native support predicate.  This is the preferred raw-world bridge: it
does not require ordinary carrier successors to preserve levels. -/
theorem levelRecursiveOpenTruthBridge_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const) :
    {Γ : Ctx Base} → (φ : Formula (WithParams Const) Γ) →
      LevelOpenTruthSupport (Base := Base) (Const := Const) W φ →
        LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W φ
  | _, .var v, _ => levelRecursiveOpenTruthBridge_var (Base := Base) (Const := Const) v
  | _, .const c, _ => levelRecursiveOpenTruthBridge_const (Base := Base) (Const := Const) c
  | _, .app f t, _ => levelRecursiveOpenTruthBridge_atom_app (Base := Base) (Const := Const) f t
  | _, .top, _ => levelRecursiveOpenTruthBridge_top (Base := Base) (Const := Const)
  | _, .bot, _ => levelRecursiveOpenTruthBridge_bot (Base := Base) (Const := Const)
  | _, .and φ ψ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [LevelOpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_and (Base := Base) (Const := Const)
        (levelRecursiveOpenTruthBridge_of_levelSupport P W φ h'.1)
        (levelRecursiveOpenTruthBridge_of_levelSupport P W ψ h'.2)
  | _, .or φ ψ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
            ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              LevelLe (Base := Base) (Const := Const) W V →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) V (subst ρ (.or φ ψ)) := by
        simpa [LevelOpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_or_supported (Base := Base) (Const := Const)
        (by intro V hWV ρ; exact h'.2.2 V hWV ρ)
        (levelRecursiveOpenTruthBridge_of_levelSupport P W φ h'.1)
        (levelRecursiveOpenTruthBridge_of_levelSupport P W ψ h'.2.1)
  | _, .imp φ ψ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [LevelOpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_imp (Base := Base) (Const := Const) P
        (levelRecursiveOpenTruthBridge_of_levelSupport P W φ h'.1)
        (levelRecursiveOpenTruthBridge_of_levelSupport P W ψ h'.2)
  | _, .not φ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [LevelOpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_not (Base := Base) (Const := Const) P
        (levelRecursiveOpenTruthBridge_of_levelSupport P W φ h')
  | _, .eq s t, _ => levelRecursiveOpenTruthBridge_eq (Base := Base) (Const := Const) s t
  | _, .all φ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [LevelOpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_all (Base := Base) (Const := Const) P
        (levelRecursiveOpenTruthBridge_of_levelSupport P W φ h')
  | _, .ex φ, h => by
      have h' : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W V →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) V (subst ρ (.ex φ)) := by
        simpa [LevelOpenTruthSupport] using h
      exact levelRecursiveOpenTruthBridge_ex_supported (Base := Base) (Const := Const)
        (by intro V hWV ρ; exact h'.2 V hWV ρ)
        (levelRecursiveOpenTruthBridge_of_levelSupport P W φ h'.1)
termination_by _Γ φ _ => sizeOf φ

theorem levelRecursiveBodyClosedTruthBridge_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveBodyClosedTruthBridge (Base := Base) (Const := Const) W φ :=
  levelRecursiveBodyClosedTruthBridge_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_of_levelSupport
      (Base := Base) (Const := Const) P W φ hφ)

theorem levelRecursiveClosedTruthAt_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W φ :=
  levelRecursiveClosedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_of_levelSupport
      (Base := Base) (Const := Const) P W φ hφ)

theorem levelRecursiveClosedTruthAbove_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_mono (Base := Base) (Const := Const) hWV φ hφ)

theorem levelRecursiveClosedTruthAbove_atom_const_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (c : WithParams Const propTy) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.const c : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_const (Base := Base) (Const := Const) c)

theorem levelRecursiveClosedTruthAbove_atom_app_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ propTy))
    (t : ClosedTerm (WithParams Const) σ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.app f t : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_atom_app (Base := Base) (Const := Const) f t)

theorem levelRecursiveClosedTruthAbove_top_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.top : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_top (Base := Base) (Const := Const))

theorem levelRecursiveClosedTruthAbove_bot_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.bot : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_bot (Base := Base) (Const := Const))

theorem levelRecursiveClosedTruthAbove_and_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.and φ ψ) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_and (Base := Base) (Const := Const) hφ hψ)

theorem levelRecursiveClosedTruthAbove_or_of_levelSupportAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_or_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) hφ hψ hOr)

theorem levelRecursiveClosedTruthAbove_ex_of_levelSupportAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_ex_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) hφ hEx)

theorem levelRecursiveClosedTruthAbove_or_of_levelSupport_supportedAt
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_or_of_supportedAt
      (Base := Base) (Const := Const) hSupport hφ hψ)

theorem levelRecursiveClosedTruthAbove_imp_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : LevelOpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.imp φ ψ) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_imp (Base := Base) (Const := Const) hφ hψ)

theorem levelRecursiveClosedTruthAbove_not_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.not φ) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_not (Base := Base) (Const := Const) hφ)

theorem levelRecursiveClosedTruthAbove_eq_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {τ : Ty Base} (s t : ClosedTerm (WithParams Const) τ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.eq s t : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_eq (Base := Base) (Const := Const) s t)

theorem levelRecursiveClosedTruthAbove_all_of_levelSupport
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_all (Base := Base) (Const := Const) hφ)

theorem levelRecursiveClosedTruthAbove_ex_of_levelSupport_supportedAt
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)))
    (hφ : LevelOpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_of_levelSupport (Base := Base) (Const := Const) P
    (levelOpenTruthSupport_ex_of_supportedAt
      (Base := Base) (Const := Const) hSupport hφ)

theorem openTruthBridge_or_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : OpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.or φ ψ) :=
  openTruthBridge_of_support (Base := Base) (Const := Const) P W (.or φ ψ)
    (openTruthSupport_or_of_openSupportedAbove
      (Base := Base) (Const := Const) hφ hψ hOr)

theorem openTruthBridge_or_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    OpenTruthBridge (Base := Base) (Const := Const) W (.or φ ψ) :=
  openTruthBridge_of_support (Base := Base) (Const := Const) P W (.or φ ψ)
    (openTruthSupport_or_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) hLevel hφ hψ hOr)

theorem openTruthBridge_ex_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : OpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ)) :
    OpenTruthBridge (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) :=
  openTruthBridge_of_support (Base := Base) (Const := Const) P W (.ex φ)
    (openTruthSupport_ex_of_openSupportedAbove
      (Base := Base) (Const := Const) hφ hEx)

theorem openTruthBridge_ex_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ)) :
    OpenTruthBridge (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) :=
  openTruthBridge_of_support (Base := Base) (Const := Const) P W (.ex φ)
    (openTruthSupport_ex_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) hLevel hφ hEx)

theorem closedTruthAt_or_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : OpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.or φ ψ) :=
  closedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (openTruthBridge_or_of_openSupportedAbove
      (Base := Base) (Const := Const) P hφ hψ hOr)

theorem closedTruthAt_or_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.or φ ψ) :=
  closedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (openTruthBridge_or_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) P hLevel hφ hψ hOr)

theorem closedTruthAt_ex_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : OpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  closedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (openTruthBridge_ex_of_openSupportedAbove
      (Base := Base) (Const := Const) P hφ hEx)

theorem closedTruthAt_ex_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  closedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (openTruthBridge_ex_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) P hLevel hφ hEx)

/-- `OpenTruthSupport` is monotone along ordinary carrier extension.  This is
the support invariant needed by implication and universal clauses, whose
successors are ordered by `Le`, not only by the level-aware preorder. -/
theorem openTruthSupport_mono
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hWV : Le (Base := Base) (Const := Const) W V) :
    {Γ : Ctx Base} → (φ : Formula (WithParams Const) Γ) →
      OpenTruthSupport (Base := Base) (Const := Const) W φ →
        OpenTruthSupport (Base := Base) (Const := Const) V φ
  | _, .var _, _ => by simp [OpenTruthSupport]
  | _, .const _, _ => by simp [OpenTruthSupport]
  | _, .app _ _, _ => by simp [OpenTruthSupport]
  | _, .top, _ => by simp [OpenTruthSupport]
  | _, .bot, _ => by simp [OpenTruthSupport]
  | _, .and φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      have hV : OpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) V ψ :=
        ⟨openTruthSupport_mono hWV φ h'.1, openTruthSupport_mono hWV ψ h'.2⟩
      simpa [OpenTruthSupport] using hV
  | _, .or φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ ∧
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              Le (Base := Base) (Const := Const) W U →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) U (subst ρ (.or φ ψ)) := by
        simpa [OpenTruthSupport] using h
      have hV : OpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) V ψ ∧
            ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              Le (Base := Base) (Const := Const) V U →
                ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                  SupportedAt (Base := Base) (Const := Const) U (subst ρ (.or φ ψ)) := by
        refine ⟨openTruthSupport_mono hWV φ h'.1,
          openTruthSupport_mono hWV ψ h'.2.1, ?_⟩
        intro U hVU ρ
        exact h'.2.2 U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ
      simpa [OpenTruthSupport] using hV
  | _, .imp φ ψ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) W ψ := by
        simpa [OpenTruthSupport] using h
      have hV : OpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          OpenTruthSupport (Base := Base) (Const := Const) V ψ :=
        ⟨openTruthSupport_mono hWV φ h'.1, openTruthSupport_mono hWV ψ h'.2⟩
      simpa [OpenTruthSupport] using hV
  | _, .not φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      simpa [OpenTruthSupport] using openTruthSupport_mono hWV φ h'
  | _, .eq _ _, _ => by simp [OpenTruthSupport]
  | _, .all φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ := by
        simpa [OpenTruthSupport] using h
      simpa [OpenTruthSupport] using openTruthSupport_mono hWV φ h'
  | _, .ex φ, h => by
      have h' : OpenTruthSupport (Base := Base) (Const := Const) W φ ∧
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W U →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) U (subst ρ (.ex φ)) := by
        simpa [OpenTruthSupport] using h
      have hV : OpenTruthSupport (Base := Base) (Const := Const) V φ ∧
          ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) V U →
              ∀ ρ : ClosedEnv (Base := Base) (Const := WithParams Const) _,
                SupportedAt (Base := Base) (Const := Const) U (subst ρ (.ex φ)) := by
        refine ⟨openTruthSupport_mono hWV φ h'.1, ?_⟩
        intro U hVU ρ
        exact h'.2 U (le_trans (Base := Base) (Const := Const) hWV hVU) ρ
      simpa [OpenTruthSupport] using hV
termination_by _Γ φ _ => sizeOf φ

theorem bodyClosedTruthBridge_of_support
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W φ :=
  bodyClosedTruthBridge_of_openTruthBridge (Base := Base) (Const := Const)
    (openTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)

theorem closedTruthAt_of_support
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    ClosedTruthAt (Base := Base) (Const := Const) W φ :=
  closedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (openTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)

theorem closedTruthAbove_of_support
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV
  exact closedTruthAt_of_support (Base := Base) (Const := Const) P
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV φ hφ)

theorem levelClosedTruthAbove_of_support
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelClosedTruthAbove (Base := Base) (Const := Const) W φ :=
  levelClosedTruthAbove_of_closedTruthAbove (Base := Base) (Const := Const)
    (closedTruthAbove_of_support (Base := Base) (Const := Const) P hφ)

theorem levelRecursiveClosedTruthAbove_of_support
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W φ := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_of_support (Base := Base) (Const := Const) P
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV.2 φ hφ)

theorem levelRecursiveClosedTruthAbove_or_of_supportedAt
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveClosedTruthAbove_or_supportedAt (Base := Base) (Const := Const)
    hSupport
    (levelRecursiveClosedTruthAbove_of_support (Base := Base) (Const := Const) P hφ)
    (levelRecursiveClosedTruthAbove_of_support (Base := Base) (Const := Const) P hψ)

theorem levelRecursiveClosedTruthAbove_ex_of_supportedAt
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)))
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAbove_ex_supportedAt (Base := Base) (Const := Const)
    hSupport
    (levelRecursiveBodyClosedTruthBridge_of_support
      (Base := Base) (Const := Const) P hφ)

theorem levelRecursiveOpenTruthBridge_or_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : OpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveOpenTruthBridge_or_supported (Base := Base) (Const := Const)
    (by intro V hWV ρ; exact hOr V hWV.2 ρ)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W ψ hψ)

theorem levelRecursiveOpenTruthBridge_or_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {φ ψ : Formula (WithParams Const) Γ}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveOpenTruthBridge_or_supported (Base := Base) (Const := Const)
    (by intro V hWV ρ; exact hOr V hWV ρ)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W ψ hψ)

theorem levelRecursiveOpenTruthBridge_ex_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : OpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ)) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) :=
  levelRecursiveOpenTruthBridge_ex_supported (Base := Base) (Const := Const)
    (by intro V hWV ρ; exact hEx V hWV.2 ρ)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)

theorem levelRecursiveOpenTruthBridge_ex_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {Γ : Ctx Base} {σ : Ty Base} {φ : Formula (WithParams Const) (σ :: Γ)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ)) :
    LevelRecursiveOpenTruthBridge (Base := Base) (Const := Const) W
      (.ex φ : Formula (WithParams Const) Γ) :=
  levelRecursiveOpenTruthBridge_ex_supported (Base := Base) (Const := Const)
    (by intro V hWV ρ; exact hEx V hWV ρ)
    (levelRecursiveOpenTruthBridge_of_support (Base := Base) (Const := Const) P W φ hφ)

theorem levelRecursiveClosedTruthAt_or_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : OpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveClosedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_or_of_openSupportedAbove
      (Base := Base) (Const := Const) P hφ hψ hOr)

theorem levelRecursiveClosedTruthAt_or_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W (.or φ ψ) :=
  levelRecursiveClosedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_or_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) P hφ hψ hOr)

theorem levelRecursiveClosedTruthAt_ex_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : OpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_ex_of_openSupportedAbove
      (Base := Base) (Const := Const) P hφ hEx)

theorem levelRecursiveClosedTruthAt_ex_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    LevelRecursiveClosedTruthAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelRecursiveClosedTruthAt_of_openTruthBridge (Base := Base) (Const := Const)
    (levelRecursiveOpenTruthBridge_ex_of_levelOpenSupportedAbove
      (Base := Base) (Const := Const) P hφ hEx)

theorem levelRecursiveClosedTruthAbove_or_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : OpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_or_of_openSupportedAbove
    (Base := Base) (Const := Const) P
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV.2 φ hφ)
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV.2 ψ hψ)
    (openSupportedAbove_mono (Base := Base) (Const := Const) hWV.2 hOr)

theorem levelRecursiveClosedTruthAbove_or_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_or_of_levelOpenSupportedAbove
    (Base := Base) (Const := Const) P
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV.2 φ hφ)
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV.2 ψ hψ)
    (levelOpenSupportedAbove_mono (Base := Base) (Const := Const) hWV hOr)

theorem levelRecursiveClosedTruthAbove_ex_of_openSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : OpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_ex_of_openSupportedAbove
    (Base := Base) (Const := Const) P
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV.2 φ hφ)
    (openSupportedAbove_mono (Base := Base) (Const := Const) hWV.2 hEx)

theorem levelRecursiveClosedTruthAbove_ex_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    LevelRecursiveClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) := by
  intro V hWV
  exact levelRecursiveClosedTruthAt_ex_of_levelOpenSupportedAbove
    (Base := Base) (Const := Const) P
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV.2 φ hφ)
    (levelOpenSupportedAbove_mono (Base := Base) (Const := Const) hWV hEx)

theorem bodyClosedTruthBridge_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} (c : WithParams Const propTy) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W
      (.const c : Formula (WithParams Const) [σ]) := by
  intro V _hWV t
  simp [RecursiveForcesOpen, Forces, Atom, instantiate, subst]

theorem bodyClosedTruthBridge_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ τ : Ty Base} (f : Term (WithParams Const) [σ] (τ ⇒ propTy))
    (a : Term (WithParams Const) [σ] τ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W
      (.app f a : Formula (WithParams Const) [σ]) := by
  intro V _hWV t
  simp [RecursiveForcesOpen, Forces, Atom, instantiate, subst]

theorem bodyClosedTruthBridge_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W
      (.top : Formula (WithParams Const) [σ]) := by
  intro V _hWV t
  constructor
  · intro _
    simpa [instantiate, subst] using
      (forces_top (Base := Base) (Const := Const) V)
  · intro _
    simp [RecursiveForcesOpen]

theorem bodyClosedTruthBridge_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W
      (.bot : Formula (WithParams Const) [σ]) := by
  intro V _hWV t
  constructor
  · intro h
    simp [RecursiveForcesOpen] at h
  · intro h
    exact False.elim (forces_bot (Base := Base) (Const := Const) V
      (by simpa [instantiate, subst] using h))

theorem bodyClosedTruthBridge_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ τ : Ty Base} (s t : Term (WithParams Const) [σ] τ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W
      (.eq s t : Formula (WithParams Const) [σ]) := by
  intro V _hWV a
  simp [RecursiveForcesOpen, Forces, EqVal, instantiate, subst]

theorem bodyClosedTruthBridge_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ ψ : Formula (WithParams Const) [σ]}
    (hφ : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : BodyClosedTruthBridge (Base := Base) (Const := Const) W ψ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W (.and φ ψ) := by
  intro V hWV t
  constructor
  · intro h
    have hPair :
        RecursiveForcesOpen (Base := Base) (Const := Const) V φ
            (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
              (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ∧
          RecursiveForcesOpen (Base := Base) (Const := Const) V ψ
            (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
              (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
      simpa [RecursiveForcesOpen] using h
    have hAnd : Forces (Base := Base) (Const := Const) V
        (.and (instantiate (Base := Base) t φ) (instantiate (Base := Base) t ψ)) :=
      (forces_and (Base := Base) (Const := Const)).mpr
        ⟨(hφ V hWV t).mp hPair.1, (hψ V hWV t).mp hPair.2⟩
    simpa [instantiate, subst] using hAnd
  · intro h
    have hAnd : Forces (Base := Base) (Const := Const) V
        (.and (instantiate (Base := Base) t φ) (instantiate (Base := Base) t ψ)) := by
      simpa [instantiate, subst] using h
    have hPair :
        RecursiveForcesOpen (Base := Base) (Const := Const) V φ
            (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
              (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ∧
          RecursiveForcesOpen (Base := Base) (Const := Const) V ψ
            (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
              (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) :=
      ⟨(hφ V hWV t).mpr ((forces_and (Base := Base) (Const := Const)).mp hAnd).1,
        (hψ V hWV t).mpr ((forces_and (Base := Base) (Const := Const)).mp hAnd).2⟩
    simpa [RecursiveForcesOpen] using hPair

theorem bodyClosedTruthBridge_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ ψ : Formula (WithParams Const) [σ]}
    (hSupport :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            SupportedAt (Base := Base) (Const := Const) V
              (instantiate (Base := Base) t (.or φ ψ : Formula (WithParams Const) [σ])))
    (hφ : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : BodyClosedTruthBridge (Base := Base) (Const := Const) W ψ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV t
  constructor
  · intro h
    have hOr : Forces (Base := Base) (Const := Const) V
        (.or (instantiate (Base := Base) t φ) (instantiate (Base := Base) t ψ)) := by
      rcases (by simpa [RecursiveForcesOpen] using h) with hφ' | hψ'
      · exact (forces_or_at (Base := Base) (Const := Const)
          (W := V) (by simpa [instantiate, subst] using hSupport V hWV t)).mpr
          (Or.inl ((hφ V hWV t).mp hφ'))
      · exact (forces_or_at (Base := Base) (Const := Const)
          (W := V) (by simpa [instantiate, subst] using hSupport V hWV t)).mpr
          (Or.inr ((hψ V hWV t).mp hψ'))
    simpa [instantiate, subst] using hOr
  · intro h
    have hOr : Forces (Base := Base) (Const := Const) V
        (.or (instantiate (Base := Base) t φ) (instantiate (Base := Base) t ψ)) := by
      simpa [instantiate, subst] using h
    rcases (forces_or_at (Base := Base) (Const := Const)
        (W := V) (by simpa [instantiate, subst] using hSupport V hWV t)).mp hOr with hφ' | hψ'
    · simpa [RecursiveForcesOpen] using
        (Or.inl ((hφ V hWV t).mpr hφ') :
          RecursiveForcesOpen (Base := Base) (Const := Const) V φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ∨
            RecursiveForcesOpen (Base := Base) (Const := Const) V ψ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t))
    · simpa [RecursiveForcesOpen] using
        (Or.inr ((hψ V hWV t).mpr hψ') :
          RecursiveForcesOpen (Base := Base) (Const := Const) V φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ∨
            RecursiveForcesOpen (Base := Base) (Const := Const) V ψ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t))

theorem bodyClosedTruthBridge_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ ψ : Formula (WithParams Const) [σ]}
    (hφ : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ)
    (hψ : BodyClosedTruthBridge (Base := Base) (Const := Const) W ψ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro V hWV t
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            RecursiveForcesOpen (Base := Base) (Const := Const) U φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) →
              RecursiveForcesOpen (Base := Base) (Const := Const) U ψ
                (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                  (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
      simpa [RecursiveForcesOpen] using h
    have hImp : Forces (Base := Base) (Const := Const) V
        (.imp (instantiate (Base := Base) t φ) (instantiate (Base := Base) t ψ)) := by
      apply (forces_imp_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU hφU
      exact (hψ U (le_trans (Base := Base) (Const := Const) hWV hVU) t).mp
        (hRec U hVU
          ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) t).mpr hφU))
    simpa [instantiate, subst] using hImp
  · intro h
    have hImp : Forces (Base := Base) (Const := Const) V
        (.imp (instantiate (Base := Base) t φ) (instantiate (Base := Base) t ψ)) := by
      simpa [instantiate, subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            RecursiveForcesOpen (Base := Base) (Const := Const) U φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) →
              RecursiveForcesOpen (Base := Base) (Const := Const) U ψ
                (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                  (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
      intro U hVU hφU
      exact (hψ U (le_trans (Base := Base) (Const := Const) hWV hVU) t).mpr
        ((forces_imp_provider (Base := Base) (Const := Const) P V).mp hImp U hVU
          ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) t).mp hφU))
    simpa [RecursiveForcesOpen] using hRec

theorem bodyClosedTruthBridge_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W (.not φ) := by
  intro V hWV t
  constructor
  · intro h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            ¬ RecursiveForcesOpen (Base := Base) (Const := Const) U φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
      simpa [RecursiveForcesOpen] using h
    have hNot : Forces (Base := Base) (Const := Const) V
        (.not (instantiate (Base := Base) t φ)) := by
      apply (forces_not_provider (Base := Base) (Const := Const) P V).mpr
      intro U hVU hφU
      exact hRec U hVU
        ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) t).mpr hφU)
    simpa [instantiate, subst] using hNot
  · intro h
    have hNot : Forces (Base := Base) (Const := Const) V
        (.not (instantiate (Base := Base) t φ)) := by
      simpa [instantiate, subst] using h
    have hRec :
        ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) V U →
            ¬ RecursiveForcesOpen (Base := Base) (Const := Const) U φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
      intro U hVU hφU
      exact (forces_not_provider (Base := Base) (Const := Const) P V).mp hNot U hVU
        ((hφ U (le_trans (Base := Base) (Const := Const) hWV hVU) t).mp hφU)
    simpa [RecursiveForcesOpen] using hRec

theorem closedTruthAt_atom_const
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (c : WithParams Const propTy) :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.const c : ClosedFormula (WithParams Const)) :=
  recursiveForces_iff_forces_atom_const (Base := Base) (Const := Const) c

theorem closedTruthAt_atom_app
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ propTy))
    (t : ClosedTerm (WithParams Const) σ) :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.app f t : ClosedFormula (WithParams Const)) :=
  recursiveForces_iff_forces_atom_app (Base := Base) (Const := Const) f t

theorem closedTruthAt_top
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.top : ClosedFormula (WithParams Const)) :=
  recursiveForces_iff_forces_top (Base := Base) (Const := Const)

theorem closedTruthAt_bot
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.bot : ClosedFormula (WithParams Const)) :=
  recursiveForces_iff_forces_bot (Base := Base) (Const := Const)

theorem closedTruthAt_eq
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {s t : ClosedTerm (WithParams Const) σ} :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.eq s t : ClosedFormula (WithParams Const)) :=
  recursiveForces_iff_forces_eq (Base := Base) (Const := Const)

theorem closedTruthAt_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTruthAt (Base := Base) (Const := Const) W φ)
    (hψ : ClosedTruthAt (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.and φ ψ) :=
  recursiveForces_iff_forces_and (Base := Base) (Const := Const) hφ hψ

theorem closedTruthAbove_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : ClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W (.and φ ψ) := by
  intro V hWV
  exact closedTruthAt_and (Base := Base) (Const := Const) (hφ V hWV) (hψ V hWV)

theorem levelClosedTruthAbove_and
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : LevelClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : LevelClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    LevelClosedTruthAbove (Base := Base) (Const := Const) W (.and φ ψ) := by
  intro V hWV
  exact closedTruthAt_and (Base := Base) (Const := Const) (hφ V hWV) (hψ V hWV)

theorem closedTruthAt_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : ClosedTruthAt (Base := Base) (Const := Const) W φ)
    (hψ : ClosedTruthAt (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.or φ ψ) :=
  recursiveForces_iff_forces_or_supported
    (Base := Base) (Const := Const) hSupport hφ hψ

theorem levelClosedTruthAbove_or_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ))
    (hφ : LevelClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : LevelClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    LevelClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV
  exact closedTruthAt_or_supported (Base := Base) (Const := Const)
    (supportedAt_mono (Base := Base) (Const := Const) hWV hSupport)
    (hφ V hWV) (hψ V hWV)

theorem closedTruthAt_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSucc :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ClosedTruthAt (Base := Base) (Const := Const) V φ ∧
            ClosedTruthAt (Base := Base) (Const := Const) V ψ) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.imp φ ψ) :=
  recursiveForces_iff_forces_imp (Base := Base) (Const := Const) P hSucc

theorem closedTruthAt_imp_of_above
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : ClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.imp φ ψ) := by
  exact closedTruthAt_imp (Base := Base) (Const := Const) P
    (fun V hWV => ⟨hφ V hWV, hψ V hWV⟩)

theorem closedTruthAbove_imp
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψ : ClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro V hWV
  exact closedTruthAt_imp_of_above (Base := Base) (Const := Const) P
    (closedTruthAbove_mono (Base := Base) (Const := Const) hWV hφ)
    (closedTruthAbove_mono (Base := Base) (Const := Const) hWV hψ)

/-- Negative implication truth step, level-aware form.  If `φ → ψ` is absent
from the carrier, the supported successor construction produces a level-growing
counterworld; truth for the two subformulas at that counterworld refutes
recursive forcing of the implication. -/
theorem not_recursiveForces_imp_of_not_mem
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφAvoid :
      ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ)
    (hψAvoid :
      ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level ψ)
    (hφTruth : LevelClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψTruth : LevelClosedTruthAbove (Base := Base) (Const := Const) W ψ)
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ RecursiveForces (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro hRec
  obtain ⟨V, _hLevelEq, hWV, hφV, hψNotV⟩ :=
    exists_level_successor_for_imp (Base := Base) (Const := Const)
      W S hφAvoid hψAvoid hNotImp
  have hRecImp :
      ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W U →
          RecursiveForces (Base := Base) (Const := Const) U φ →
            RecursiveForces (Base := Base) (Const := Const) U ψ := by
    simpa [RecursiveForces, RecursiveForcesOpen] using hRec
  have hφRec : RecursiveForces (Base := Base) (Const := Const) V φ :=
    (hφTruth V hWV).mpr hφV
  have hψRec : RecursiveForces (Base := Base) (Const := Const) V ψ :=
    hRecImp V hWV.2 hφRec
  exact hψNotV ((hψTruth V hWV).mp hψRec)

/-- Local implication truth step assembled from the raw successor
construction.  The forward direction uses the level-growing counterworld; the
reverse direction is ordinary carrier monotonicity plus modus ponens. -/
theorem closedTruthAt_imp_of_raw_refutation
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφAvoid :
      ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ)
    (hψAvoid :
      ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level ψ)
    (hφTruth : ClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψTruth : ClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.imp φ ψ) := by
  constructor
  · intro hRec
    by_contra hNotImp
    exact not_recursiveForces_imp_of_not_mem (Base := Base) (Const := Const)
      S hφAvoid hψAvoid
      (levelClosedTruthAbove_of_closedTruthAbove (Base := Base) (Const := Const) hφTruth)
      (levelClosedTruthAbove_of_closedTruthAbove (Base := Base) (Const := Const) hψTruth)
      hNotImp hRec
  · intro hImp
    have hRecImp :
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            RecursiveForces (Base := Base) (Const := Const) V φ →
              RecursiveForces (Base := Base) (Const := Const) V ψ := by
      intro V hWV hφRec
      have hφMem : Forces (Base := Base) (Const := Const) V φ :=
        (hφTruth V hWV).mp hφRec
      have hψMem : Forces (Base := Base) (Const := Const) V ψ :=
        SupportedCanonicalMembership.imp_mp_mem (Base := Base) (Const := Const)
          (W := V) (hWV hImp) hφMem
      exact (hψTruth V hWV).mpr hψMem
    simpa [RecursiveForces, RecursiveForcesOpen] using hRecImp

/-- Implication truth above a world, using the raw successor construction at
each ordinary successor whose level is known not to decrease. -/
theorem closedTruthAbove_imp_of_raw_refutation
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.imp φ ψ))
    (hφTruth : ClosedTruthAbove (Base := Base) (Const := Const) W φ)
    (hψTruth : ClosedTruthAbove (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W (.imp φ ψ) := by
  intro V hWV
  have hWVLevel : LevelLe (Base := Base) (Const := Const) W V :=
    ⟨hLevel V hWV, hWV⟩
  have hSupportV : SupportedAt (Base := Base) (Const := Const) V (.imp φ ψ) :=
    supportedAt_mono (Base := Base) (Const := Const) hWVLevel hSupport
  have hφAvoid :
      ClosedTheorySet.FormulaAvoidsParamLayersFrom
        (Base := Base) (Const := Const) V.level φ :=
    ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const)
      (supported_imp_left (Base := Base) (Const := Const) (W := V) hSupportV)
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) φ)
  have hψAvoid :
      ClosedTheorySet.FormulaAvoidsParamLayersFrom
        (Base := Base) (Const := Const) V.level ψ :=
    ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const)
      (supported_imp_right (Base := Base) (Const := Const) (W := V) hSupportV)
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) ψ)
  exact closedTruthAt_imp_of_raw_refutation (Base := Base) (Const := Const)
    (P.scheduler V.level) hφAvoid hψAvoid
    (closedTruthAbove_mono (Base := Base) (Const := Const) hWV hφTruth)
    (closedTruthAbove_mono (Base := Base) (Const := Const) hWV hψTruth)

theorem closedTruthAt_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hSucc : ClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    ClosedTruthAt (Base := Base) (Const := Const) W (.not φ) :=
  recursiveForces_iff_forces_not (Base := Base) (Const := Const) P hSucc

theorem closedTruthAbove_not
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTruthAbove (Base := Base) (Const := Const) W φ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W (.not φ) := by
  intro V hWV
  exact closedTruthAt_not (Base := Base) (Const := Const) P
    (closedTruthAbove_mono (Base := Base) (Const := Const) hWV hφ)

theorem closedTruthAt_all
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
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) :=
  recursiveForces_iff_forces_all (Base := Base) (Const := Const) P hBody

/-- Negative universal truth step, level-aware form.  If `∀x.φ` is absent from
the carrier, the supported successor construction omits one fresh parameter
instance; a body truth bridge at that level-growing successor refutes recursive
forcing of the universal. -/
theorem not_recursiveForces_all_of_not_mem
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {m k : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), m + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ)
    (hBody :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            RecursiveForcesOpen (Base := Base) (Const := Const) V φ
                (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                  (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) ↔
              Forces (Base := Base) (Const := Const) V
                (instantiate (Base := Base) t φ))
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ RecursiveForces (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) := by
  intro hRec
  let c : ClosedTerm (WithParams Const) σ := .const (param σ (Nat.pair m k))
  obtain ⟨V, _hLevelEq, hWV, hInstNot⟩ :=
    exists_level_successor_for_all (Base := Base) (Const := Const)
      W (m := m) (k := k) S hm hφfresh hφfuture hNotAll
  have hRecAll :
      ∀ U : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W U →
          ∀ t : ClosedTerm (WithParams Const) σ,
            RecursiveForcesOpen (Base := Base) (Const := Const) U φ
              (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
    simpa [RecursiveForces, RecursiveForcesOpen] using hRec
  have hOpen :=
    hRecAll V hWV.2 c
  have hForces :=
    (hBody V hWV c).mp hOpen
  exact hInstNot hForces

/-- Local universal truth step assembled from the raw successor construction.
The same body bridge handles ordinary recursive successors and the
level-growing counterworld used for refutation. -/
theorem closedTruthAt_all_of_raw_refutation
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {m k : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), m + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ)
    (hBody : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) := by
  constructor
  · intro hRec
    by_contra hNotAll
    exact not_recursiveForces_all_of_not_mem (Base := Base) (Const := Const)
      S hm hφfresh hφfuture
      (fun V hWV t => hBody V hWV.2 t) hNotAll hRec
  · intro hAll
    have hRecAll :
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            ∀ t : ClosedTerm (WithParams Const) σ,
              RecursiveForcesOpen (Base := Base) (Const := Const) V φ
                (ClosedEnv.extend (Base := Base) (Const := WithParams Const)
                  (ClosedEnv.empty (Base := Base) (Const := WithParams Const)) t) := by
      intro V hWV t
      have hInstMem : Forces (Base := Base) (Const := Const) V
          (instantiate (Base := Base) t φ) :=
        SupportedCanonicalMembership.all_elim_mem (Base := Base) (Const := Const)
          (W := V) t (hWV hAll)
      exact (hBody V hWV t).mpr hInstMem
    simpa [RecursiveForces, RecursiveForcesOpen] using hRecAll

/-- Universal truth above a world, using the raw successor construction at
each ordinary successor whose level is known not to decrease. -/
theorem closedTruthAbove_all_of_raw_refutation
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hLevel :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V → W.level ≤ V.level)
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.all φ : ClosedFormula (WithParams Const)))
    (hBody : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) := by
  intro V hWV
  have hWVLevel : LevelLe (Base := Base) (Const := Const) W V :=
    ⟨hLevel V hWV, hWV⟩
  have hSupportV : SupportedAt (Base := Base) (Const := Const) V
      (.all φ : ClosedFormula (WithParams Const)) :=
    supportedAt_mono (Base := Base) (Const := Const) hWVLevel hSupport
  have hφLevel : maxParam φ ≤ V.level :=
    supported_all_body (Base := Base) (Const := Const) (W := V) hSupportV
  have hφfresh :
      NoConstOccurrence (param σ (Nat.pair V.level 0) : WithParams Const σ) φ :=
    noConstOccurrence_param_of_ge (Nat.pair V.level 0) φ
      (Nat.le_trans hφLevel (Nat.left_le_pair V.level 0))
  have hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), V.level + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ := by
    intro τ r j hVr
    have hφr : maxParam φ ≤ r := by
      omega
    exact noConstOccurrence_param_of_ge (Nat.pair r j) φ
      (Nat.le_trans hφr (Nat.left_le_pair r j))
  exact closedTruthAt_all_of_raw_refutation (Base := Base) (Const := Const)
    (P.scheduler (V.level + 1)) (m := V.level) (k := 0) (Nat.le_refl V.level)
    hφfresh hφfuture
    (bodyClosedTruthBridge_mono (Base := Base) (Const := Const) hWV hBody)

/-- The global invariant needed to use level-supported local clauses along the
ordinary carrier preorder.  Canonical frames are expected to supply this once,
rather than every connective reproving it. -/
def CarrierLevelMonotone : Prop :=
  ∀ {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const},
    Le (Base := Base) (Const := Const) W V → W.level ≤ V.level

/-- Disjunction truth above a world from level support and global level
monotonicity. -/
theorem closedTruthAbove_or_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    (hLeLevel : CarrierLevelMonotone (Base := Base) (Const := Const))
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ)
    (hOr : LevelOpenSupportedAbove (Base := Base) (Const := Const) W (.or φ ψ)) :
    ClosedTruthAbove (Base := Base) (Const := Const) W (.or φ ψ) := by
  intro V hWV
  have hWVLevel : LevelLe (Base := Base) (Const := Const) W V :=
    ⟨hLeLevel hWV, hWV⟩
  exact closedTruthAt_or_of_levelOpenSupportedAbove (Base := Base) (Const := Const) P
    (fun U hVU => hLeLevel hVU)
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV φ hφ)
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV ψ hψ)
    (levelOpenSupportedAbove_mono (Base := Base) (Const := Const) hWVLevel hOr)

/-- Existential truth above a world from level support and global level
monotonicity. -/
theorem closedTruthAbove_ex_of_levelOpenSupportedAbove
    (P : SchedulerProvider (Base := Base) Const)
    (hLeLevel : CarrierLevelMonotone (Base := Base) (Const := Const))
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hEx : LevelOpenSupportedAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const))) :
    ClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) := by
  intro V hWV
  have hWVLevel : LevelLe (Base := Base) (Const := Const) W V :=
    ⟨hLeLevel hWV, hWV⟩
  exact closedTruthAt_ex_of_levelOpenSupportedAbove (Base := Base) (Const := Const) P
    (fun U hVU => hLeLevel hVU)
    (openTruthSupport_mono (Base := Base) (Const := Const) hWV φ hφ)
    (levelOpenSupportedAbove_mono (Base := Base) (Const := Const) hWVLevel hEx)

/-- Supported implication truth above a world, packaged for the closed truth
induction interface. -/
theorem closedTruthAbove_imp_of_support_raw_refutation
    (P : SchedulerProvider (Base := Base) Const)
    (hLeLevel : CarrierLevelMonotone (Base := Base) (Const := Const))
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.imp φ ψ))
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ)
    (hψ : OpenTruthSupport (Base := Base) (Const := Const) W ψ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W (.imp φ ψ) :=
  closedTruthAbove_imp_of_raw_refutation (Base := Base) (Const := Const) P
    (fun _ hWV => hLeLevel hWV) hSupport
    (closedTruthAbove_of_support (Base := Base) (Const := Const) P hφ)
    (closedTruthAbove_of_support (Base := Base) (Const := Const) P hψ)

/-- Supported universal truth above a world, packaged for the closed truth
induction interface. -/
theorem closedTruthAbove_all_of_support_raw_refutation
    (P : SchedulerProvider (Base := Base) Const)
    (hLeLevel : CarrierLevelMonotone (Base := Base) (Const := Const))
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.all φ : ClosedFormula (WithParams Const)))
    (hφ : OpenTruthSupport (Base := Base) (Const := Const) W φ) :
    ClosedTruthAbove (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) :=
  closedTruthAbove_all_of_raw_refutation (Base := Base) (Const := Const) P
    (fun _ hWV => hLeLevel hWV) hSupport
    (bodyClosedTruthBridge_of_support (Base := Base) (Const := Const) P hφ)

theorem closedTruthAt_ex_supported
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
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  recursiveForces_iff_forces_ex_supported
    (Base := Base) (Const := Const) hSupport hBody

theorem levelClosedTruthAbove_ex_supported
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
    LevelClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) := by
  intro V hWV
  exact closedTruthAt_ex_supported (Base := Base) (Const := Const)
    (supportedAt_mono (Base := Base) (Const := Const) hWV hSupport)
    (fun U hVU t =>
      hBody U (le_trans (Base := Base) (Const := Const) hWV.2 hVU) t)

theorem closedTruthAt_all_of_bodyBridge
    (P : SchedulerProvider (Base := Base) Const)
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.all φ : ClosedFormula (WithParams Const)) :=
  closedTruthAt_all (Base := Base) (Const := Const) P hBody

theorem closedTruthAt_ex_supported_of_bodyBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const)))
    (hBody : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    ClosedTruthAt (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  closedTruthAt_ex_supported (Base := Base) (Const := Const) hSupport hBody

theorem levelClosedTruthAbove_ex_supported_of_bodyBridge
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const)))
    (hBody : BodyClosedTruthBridge (Base := Base) (Const := Const) W φ) :
    LevelClosedTruthAbove (Base := Base) (Const := Const) W
      (.ex φ : ClosedFormula (WithParams Const)) :=
  levelClosedTruthAbove_ex_supported (Base := Base) (Const := Const) hSupport hBody

theorem closedTruthAt_all_prop_var_recursive
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const}
    (hTruth :
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedFormula (WithParams Const),
            ClosedTruthAt (Base := Base) (Const := Const) V t) :
    RecursiveForces (Base := Base) (Const := Const) W
        (.all (.var .vz) : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedFormula (WithParams Const),
            RecursiveForces (Base := Base) (Const := Const) V
              (instantiate (Base := Base) t
                (.var .vz : Formula (WithParams Const) [propTy])) :=
  recursiveForces_all_prop_var_recursive_of_truth
    (Base := Base) (Const := Const) hTruth

theorem bodyClosedTruthBridge_prop_var
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const} :
    BodyClosedTruthBridge (Base := Base) (Const := Const) W
      (.var .vz : Formula (WithParams Const) [propTy]) := by
  intro V _hWV t
  simpa [instantiate, subst, Subst.single] using
    (recursiveForcesOpen_prop_var_extend_empty
      (Base := Base) (Const := Const) (W := V) t)


end SupportedCanonicalFrame

end KripkeHenkin

end Mettapedia.Logic.HOL
