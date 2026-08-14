import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical.Membership

/-!
# Supported canonical frame atoms

The supported canonical preorder, scheduler provider interface, atomic forcing,
and level-local truth-clause interfaces used by the recursive canonical forcing
construction.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin
/-! ## Supported canonical frame atoms -/

namespace SupportedCanonicalFrame

open ClosedTheorySet

/-- A supply of fair raw alternating schedulers at every parameter layer.  This
packages the fairness/enumeration data needed by the canonical implication,
negation, and universal clauses without hiding it inside the independent
`KripkeHenkin` interface. -/
structure SchedulerProvider (Const : Ty Base → Type v) where
  scheduler :
    ∀ ℓ : Nat, ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ

/-- The canonical preorder on supported presented worlds: carrier inclusion. -/
def Le (W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) : Prop :=
  ∀ {φ : ClosedFormula (WithParams Const)}, φ ∈ W.carrier → φ ∈ V.carrier

/-- The level-aware canonical preorder used by total recursive canonical
forcing: worlds grow both their language budget and their closed carrier. -/
def LevelLe (W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) : Prop :=
  W.level ≤ V.level ∧ Le (Base := Base) (Const := Const) W V

theorem le_refl (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    Le (Base := Base) (Const := Const) W W := by
  intro φ hφ
  exact hφ

theorem le_trans {U V W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    (hUV : Le (Base := Base) (Const := Const) U V)
    (hVW : Le (Base := Base) (Const := Const) V W) :
    Le (Base := Base) (Const := Const) U W := by
  intro φ hφ
  exact hVW (hUV hφ)

theorem levelLe_refl (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    LevelLe (Base := Base) (Const := Const) W W :=
  ⟨Nat.le_refl W.level, le_refl (Base := Base) (Const := Const) W⟩

theorem levelLe_trans {U V W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    (hUV : LevelLe (Base := Base) (Const := Const) U V)
    (hVW : LevelLe (Base := Base) (Const := Const) V W) :
    LevelLe (Base := Base) (Const := Const) U W :=
  ⟨Nat.le_trans hUV.1 hVW.1, le_trans (Base := Base) (Const := Const) hUV.2 hVW.2⟩

/-- Canonical atomic valuation: atomic formulas are read as carrier membership. -/
def Atom (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  φ ∈ W.carrier

theorem atom_mono {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ : ClosedFormula (WithParams Const)}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (hφ : Atom (Base := Base) (Const := Const) W φ) :
    Atom (Base := Base) (Const := Const) V φ :=
  hWV hφ

/-- Canonical equality valuation: equality formulas are read as carrier membership. -/
def EqVal {τ : Ty Base} (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (s t : ClosedTerm (WithParams Const) τ) : Prop :=
  (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier

theorem eqVal_mono {τ : Ty Base}
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {s t : ClosedTerm (WithParams Const) τ}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (hst : EqVal (Base := Base) (Const := Const) W s t) :
    EqVal (Base := Base) (Const := Const) V s t :=
  hWV hst

/-- Canonical forcing readout for the membership frame.  The full
`KripkeHenkin` instance additionally needs the implication and universal
successor clauses. -/
def Forces (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  φ ∈ W.carrier

/-- A formula is inside a supported world's current parameter layer budget. -/
def SupportedAt (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (φ : ClosedFormula (WithParams Const)) : Prop :=
  maxParam φ ≤ W.level

theorem supportedAt_mono {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ : ClosedFormula (WithParams Const)}
    (hWV : LevelLe (Base := Base) (Const := Const) W V)
    (hφ : SupportedAt (Base := Base) (Const := Const) W φ) :
    SupportedAt (Base := Base) (Const := Const) V φ :=
  Nat.le_trans hφ hWV.1

theorem forces_mono {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ : ClosedFormula (WithParams Const)}
    (hWV : Le (Base := Base) (Const := Const) W V)
    (hφ : Forces (Base := Base) (Const := Const) W φ) :
    Forces (Base := Base) (Const := Const) V φ :=
  hWV hφ

theorem supported_or_left {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (h : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ)) :
    SupportedAt (Base := Base) (Const := Const) W φ := by
  exact Nat.le_trans (le_max_left (maxParam φ) (maxParam ψ))
    (by simpa [SupportedAt, maxParam] using h)

theorem supported_or_right {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (h : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ)) :
    SupportedAt (Base := Base) (Const := Const) W ψ := by
  exact Nat.le_trans (le_max_right (maxParam φ) (maxParam ψ))
    (by simpa [SupportedAt, maxParam] using h)

theorem supported_imp_left {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (h : SupportedAt (Base := Base) (Const := Const) W (.imp φ ψ)) :
    SupportedAt (Base := Base) (Const := Const) W φ := by
  exact Nat.le_trans (le_max_left (maxParam φ) (maxParam ψ))
    (by simpa [SupportedAt, maxParam] using h)

theorem supported_imp_right {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (h : SupportedAt (Base := Base) (Const := Const) W (.imp φ ψ)) :
    SupportedAt (Base := Base) (Const := Const) W ψ := by
  exact Nat.le_trans (le_max_right (maxParam φ) (maxParam ψ))
    (by simpa [SupportedAt, maxParam] using h)

theorem supported_not {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ : ClosedFormula (WithParams Const)}
    (h : SupportedAt (Base := Base) (Const := Const) W (.not φ)) :
    SupportedAt (Base := Base) (Const := Const) W φ := by
  simpa [SupportedAt, maxParam] using h

theorem supported_all_body {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (h : SupportedAt (Base := Base) (Const := Const)
      W (.all φ : ClosedFormula (WithParams Const))) :
    maxParam φ ≤ W.level := by
  simpa [SupportedAt, maxParam] using h

theorem supported_ex_body {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (h : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const))) :
    maxParam φ ≤ W.level := by
  simpa [SupportedAt, maxParam] using h

theorem le_of_raw_subset
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    (hRaw : ∀ {φ : ClosedFormula (WithParams Const)}, φ ∈ W.raw → φ ∈ V.carrier) :
    Le (Base := Base) (Const := Const) W V := by
  intro φ hφ
  apply V.closed
  exact ClosedTheorySet.provable_mono (Const := WithParams Const)
    (T := W.raw) (U := V.carrier)
    (by intro ψ hψ; exact hRaw hψ) hφ

theorem levelLe_of_raw_subset
    {W V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    (hLevel : W.level ≤ V.level)
    (hRaw : ∀ {φ : ClosedFormula (WithParams Const)}, φ ∈ W.raw → φ ∈ V.carrier) :
    LevelLe (Base := Base) (Const := Const) W V :=
  ⟨hLevel, le_of_raw_subset (Base := Base) (Const := Const) hRaw⟩

/-- Semantic-frame wrapper for the supported implication successor
construction: a failed implication has a level-growing successor that forces
the antecedent and refutes the consequent. -/
theorem exists_level_successor_for_imp
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ)
    (hψ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level ψ)
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      V.level = W.level + 1 ∧
        LevelLe (Base := Base) (Const := Const) W V ∧
          Forces (Base := Base) (Const := Const) V φ ∧
            ¬ Forces (Base := Base) (Const := Const) V ψ := by
  obtain ⟨V, hLevelEq, hRaw, hφMem, hψNot⟩ :=
    ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp
      (Base := Base) (Const := Const) W S hφ hψ hNotImp
  refine ⟨V, hLevelEq, ?_, hφMem, hψNot⟩
  apply levelLe_of_raw_subset (Base := Base) (Const := Const)
  · omega
  · exact hRaw

/-- Semantic-frame wrapper for the high-bound implication successor.  This is
the form used when the failed implication mentions parameters above the
current world's level. -/
theorem exists_level_successor_for_imp_at_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) m)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hm : W.level ≤ m)
    (hφMax : maxParam φ ≤ m)
    (hψMax : maxParam ψ ≤ m)
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      V.level = m + 1 ∧
        LevelLe (Base := Base) (Const := Const) W V ∧
          Forces (Base := Base) (Const := Const) V φ ∧
            ¬ Forces (Base := Base) (Const := Const) V ψ := by
  obtain ⟨V, hLevelEq, hRaw, hφMem, hψNot⟩ :=
    ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp_at_bound
      (Base := Base) (Const := Const) W S hm hφMax hψMax hNotImp
  refine ⟨V, hLevelEq, ?_, hφMem, hψNot⟩
  apply levelLe_of_raw_subset (Base := Base) (Const := Const)
  · omega
  · exact hRaw

/-- Semantic-frame wrapper for the supported universal successor
construction: a failed universal has a level-growing successor omitting a fresh
parameter instance. -/
theorem exists_level_successor_for_all
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m k : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), m + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      V.level = (m + 1) + 1 ∧
        LevelLe (Base := Base) (Const := Const) W V ∧
          ¬ Forces (Base := Base) (Const := Const) V
            (instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ) := by
  obtain ⟨V, hLevelEq, hRaw, hInstNot⟩ :=
    ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_all
      (Base := Base) (Const := Const) W S hm hφfresh hφfuture hNotAll
  refine ⟨V, hLevelEq, ?_, hInstNot⟩
  apply levelLe_of_raw_subset (Base := Base) (Const := Const)
  · omega
  · exact hRaw

theorem forces_atom_const (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (c : WithParams Const propTy) :
    Forces (Base := Base) (Const := Const) W (.const c : ClosedFormula (WithParams Const)) ↔
      Atom (Base := Base) (Const := Const) W (.const c : ClosedFormula (WithParams Const)) := by
  rfl

theorem forces_atom_app (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {σ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ propTy))
    (t : ClosedTerm (WithParams Const) σ) :
    Forces (Base := Base) (Const := Const) W (.app f t : ClosedFormula (WithParams Const)) ↔
      Atom (Base := Base) (Const := Const) W (.app f t : ClosedFormula (WithParams Const)) := by
  rfl

theorem forces_top (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    Forces (Base := Base) (Const := Const) W (.top : ClosedFormula (WithParams Const)) :=
  SupportedCanonicalMembership.top_mem W

theorem forces_bot (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    ¬ Forces (Base := Base) (Const := Const) W (.bot : ClosedFormula (WithParams Const)) :=
  SupportedCanonicalMembership.bot_not_mem W

theorem forces_and {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)} :
    Forces (Base := Base) (Const := Const) W (.and φ ψ) ↔
      Forces (Base := Base) (Const := Const) W φ ∧
        Forces (Base := Base) (Const := Const) W ψ :=
  SupportedCanonicalMembership.and_iff (W := W)

theorem forces_or_supported {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hPair :
      ClosedTheorySet.FormulaPairAvoidsParamLayersFromAt
        (Base := Base) (Const := Const) W.level (φ, ψ)) :
    Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
      Forces (Base := Base) (Const := Const) W φ ∨
        Forces (Base := Base) (Const := Const) W ψ :=
  SupportedCanonicalMembership.or_iff (W := W) hPair

theorem forces_or_of_level_bound {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hLevel : max (maxParam φ) (maxParam ψ) ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
      Forces (Base := Base) (Const := Const) W φ ∨
        Forces (Base := Base) (Const := Const) W ψ := by
  exact forces_or_supported (Base := Base) (Const := Const) (W := W)
    (ClosedTheorySet.FormulaPairAvoidsParamLayersFromAt.mono
      (Base := Base) (Const := Const) hLevel
      (ClosedTheorySet.FormulaPairAvoidsParamLayersFromAt.of_maxParam
        (Base := Base) (Const := Const) (φ, ψ)))

theorem forces_or_at {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.or φ ψ)) :
    Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
      Forces (Base := Base) (Const := Const) W φ ∨
        Forces (Base := Base) (Const := Const) W ψ := by
  have hLevel : max (maxParam φ) (maxParam ψ) ≤ W.level := by
    simpa [SupportedAt, maxParam] using hSupport
  exact forces_or_of_level_bound (Base := Base) (Const := Const) (W := W) hLevel

theorem forces_ex_supported {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody :
      ClosedTheorySet.BodyAvoidsParamLayersFromAt
        (Base := Base) (Const := Const) W.level (⟨σ, φ⟩ : Body Const)) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        Forces (Base := Base) (Const := Const) W (instantiate (Base := Base) t φ) :=
  SupportedCanonicalMembership.ex_iff (W := W) hBody

theorem forces_ex_of_level_bound {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hLevel : maxParam φ ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        Forces (Base := Base) (Const := Const) W (instantiate (Base := Base) t φ) := by
  exact forces_ex_supported (Base := Base) (Const := Const) (W := W)
    (ClosedTheorySet.BodyAvoidsParamLayersFromAt.mono
      (Base := Base) (Const := Const) hLevel
      (ClosedTheorySet.BodyAvoidsParamLayersFromAt.of_maxParam
        (Base := Base) (Const := Const) (⟨σ, φ⟩ : Body Const)))

theorem forces_ex_at {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const))) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        Forces (Base := Base) (Const := Const) W (instantiate (Base := Base) t φ) := by
  exact forces_ex_of_level_bound (Base := Base) (Const := Const) (W := W)
    (supported_ex_body (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_ex_kripke_supported {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody :
      ClosedTheorySet.BodyAvoidsParamLayersFromAt
        (Base := Base) (Const := Const) W.level (⟨σ, φ⟩ : Body Const)) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  constructor
  · intro hEx
    obtain ⟨t, ht⟩ :=
      (forces_ex_supported (Base := Base) (Const := Const) (W := W) hBody).mp hEx
    refine ⟨t, ?_⟩
    intro V hWV
    exact forces_mono (Base := Base) (Const := Const) hWV ht
  · rintro ⟨t, ht⟩
    exact (forces_ex_supported (Base := Base) (Const := Const) (W := W) hBody).mpr
      ⟨t, ht W (le_refl (Base := Base) (Const := Const) W)⟩

theorem forces_ex_kripke_of_level_bound
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hLevel : maxParam φ ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_ex_kripke_supported (Base := Base) (Const := Const) (W := W)
    (ClosedTheorySet.BodyAvoidsParamLayersFromAt.mono
      (Base := Base) (Const := Const) hLevel
      (ClosedTheorySet.BodyAvoidsParamLayersFromAt.of_maxParam
        (Base := Base) (Const := Const) (⟨σ, φ⟩ : Body Const)))

theorem forces_ex_kripke_at
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const))) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_ex_kripke_of_level_bound (Base := Base) (Const := Const) (W := W)
    (supported_ex_body (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_ex_level_kripke_supported
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody :
      ClosedTheorySet.BodyAvoidsParamLayersFromAt
        (Base := Base) (Const := Const) W.level (⟨σ, φ⟩ : Body Const)) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  constructor
  · intro hEx
    obtain ⟨t, ht⟩ :=
      (forces_ex_supported (Base := Base) (Const := Const) (W := W) hBody).mp hEx
    refine ⟨t, ?_⟩
    intro V hWV
    exact forces_mono (Base := Base) (Const := Const) hWV.2 ht
  · rintro ⟨t, ht⟩
    exact (forces_ex_supported (Base := Base) (Const := Const) (W := W) hBody).mpr
      ⟨t, ht W (levelLe_refl (Base := Base) (Const := Const) W)⟩

theorem forces_ex_level_kripke_of_level_bound
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hLevel : maxParam φ ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_ex_level_kripke_supported (Base := Base) (Const := Const) (W := W)
    (ClosedTheorySet.BodyAvoidsParamLayersFromAt.mono
      (Base := Base) (Const := Const) hLevel
      (ClosedTheorySet.BodyAvoidsParamLayersFromAt.of_maxParam
        (Base := Base) (Const := Const) (⟨σ, φ⟩ : Body Const)))

theorem forces_ex_level_kripke_at
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.ex φ : ClosedFormula (WithParams Const))) :
    Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          LevelLe (Base := Base) (Const := Const) W V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_ex_level_kripke_of_level_bound (Base := Base) (Const := Const) (W := W)
    (supported_ex_body (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_eq {τ : Ty Base}
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {s t : ClosedTerm (WithParams Const) τ} :
    Forces (Base := Base) (Const := Const) W (.eq s t : ClosedFormula (WithParams Const)) ↔
      EqVal (Base := Base) (Const := Const) W s t := by
  rfl

theorem forces_imp_supported
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ)
    (hψ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level ψ) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  constructor
  · intro hImp V hWV hφV
    exact SupportedCanonicalMembership.imp_mp_mem (W := V) (hWV hImp) hφV
  · intro hKripke
    by_contra hNotMem
    obtain ⟨W', _hLevel, hRaw, hφMem, hψNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp
        (Base := Base) (Const := Const) W S hφ hψ hNotMem
    exact hψNot (hKripke W' (le_of_raw_subset (Base := Base) (Const := Const) hRaw) hφMem)

theorem forces_imp_level_supported
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ)
    (hψ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level ψ) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  constructor
  · intro hImp V hWV hφV
    exact SupportedCanonicalMembership.imp_mp_mem (W := V) (hWV.2 hImp) hφV
  · intro hKripke
    by_contra hNotMem
    obtain ⟨W', hLevel, hRaw, hφMem, hψNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp
        (Base := Base) (Const := Const) W S hφ hψ hNotMem
    have hLevelLe : W.level ≤ W'.level := by
      omega
    exact hψNot
      (hKripke W'
        (levelLe_of_raw_subset (Base := Base) (Const := Const) hLevelLe hRaw)
        hφMem)

theorem forces_imp_of_level_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφLevel : maxParam φ ≤ W.level)
    (hψLevel : maxParam ψ ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_supported (Base := Base) (Const := Const) W S
    (ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hφLevel
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) φ))
    (ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hψLevel
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) ψ))

theorem forces_imp_at
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.imp φ ψ)) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_of_level_bound (Base := Base) (Const := Const) W S
    (supported_imp_left (Base := Base) (Const := Const) (W := W) hSupport)
    (supported_imp_right (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_imp_level_of_level_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφLevel : maxParam φ ≤ W.level)
    (hψLevel : maxParam ψ ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_level_supported (Base := Base) (Const := Const) W S
    (ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hφLevel
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) φ))
    (ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hψLevel
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) ψ))

theorem forces_imp_level_at
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.imp φ ψ)) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_level_of_level_bound (Base := Base) (Const := Const) W S
    (supported_imp_left (Base := Base) (Const := Const) (W := W) hSupport)
    (supported_imp_right (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_imp_at_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) m)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hm : W.level ≤ m)
    (hφMax : maxParam φ ≤ m)
    (hψMax : maxParam ψ ≤ m) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  constructor
  · intro hImp V hWV hφV
    exact SupportedCanonicalMembership.imp_mp_mem (W := V) (hWV hImp) hφV
  · intro hKripke
    by_contra hNotMem
    obtain ⟨W', _hLevel, hRaw, hφMem, hψNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp_at_bound
        (Base := Base) (Const := Const) W S hm hφMax hψMax hNotMem
    exact hψNot (hKripke W' (le_of_raw_subset (Base := Base) (Const := Const) hRaw) hφMem)

theorem forces_imp_level_at_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) m)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hm : W.level ≤ m)
    (hφMax : maxParam φ ≤ m)
    (hψMax : maxParam ψ ≤ m) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  constructor
  · intro hImp V hWV hφV
    exact SupportedCanonicalMembership.imp_mp_mem (W := V) (hWV.2 hImp) hφV
  · intro hKripke
    by_contra hNotMem
    obtain ⟨W', hLevel, hRaw, hφMem, hψNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp_at_bound
        (Base := Base) (Const := Const) W S hm hφMax hψMax hNotMem
    have hLevelLe : W.level ≤ W'.level := by
      omega
    exact hψNot
      (hKripke W'
        (levelLe_of_raw_subset (Base := Base) (Const := Const) hLevelLe hRaw)
        hφMem)

theorem forces_imp_at_max_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)}
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (max W.level (max (maxParam φ) (maxParam ψ)))) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_at_bound (Base := Base) (Const := Const) W S
    (le_max_left W.level (max (maxParam φ) (maxParam ψ)))
    (by
      exact Nat.le_trans (le_max_left (maxParam φ) (maxParam ψ))
        (le_max_right W.level (max (maxParam φ) (maxParam ψ))))
    (by
      exact Nat.le_trans (le_max_right (maxParam φ) (maxParam ψ))
        (le_max_right W.level (max (maxParam φ) (maxParam ψ))))

theorem forces_imp_level_at_max_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)}
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (max W.level (max (maxParam φ) (maxParam ψ)))) :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_level_at_bound (Base := Base) (Const := Const) W S
    (le_max_left W.level (max (maxParam φ) (maxParam ψ)))
    (by
      exact Nat.le_trans (le_max_left (maxParam φ) (maxParam ψ))
        (le_max_right W.level (max (maxParam φ) (maxParam ψ))))
    (by
      exact Nat.le_trans (le_max_right (maxParam φ) (maxParam ψ))
        (le_max_right W.level (max (maxParam φ) (maxParam ψ))))

theorem forces_imp_provider
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)} :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_at_max_bound (Base := Base) (Const := Const) W
    (P.scheduler (max W.level (max (maxParam φ) (maxParam ψ))))

theorem forces_imp_level_provider
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)} :
    Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          Forces (Base := Base) (Const := Const) V φ →
            Forces (Base := Base) (Const := Const) V ψ := by
  exact forces_imp_level_at_max_bound (Base := Base) (Const := Const) W
    (P.scheduler (max W.level (max (maxParam φ) (maxParam ψ))))

theorem forces_not_supported
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  constructor
  · intro hNot V hWV hφV
    have hNotV : Forces (Base := Base) (Const := Const) V (.not φ) := hWV hNot
    have hBotV : Forces (Base := Base) (Const := Const) V (.bot : ClosedFormula (WithParams Const)) := by
      apply V.closed
      exact ClosedTheorySet.provable_bot_of_not (Const := WithParams Const)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hNotV)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφV)
    exact forces_bot (Base := Base) (Const := Const) V hBotV
  · intro hKripke
    by_contra hNotMem
    have hBot : ClosedTheorySet.FormulaAvoidsParamLayersFrom
        (Base := Base) (Const := Const) W.level (.bot : ClosedFormula (WithParams Const)) := by
      intro σ m k hm
      exact NoConstOccurrence.bot
    have hNotImp : (.imp φ (.bot : ClosedFormula (WithParams Const)) : ClosedFormula (WithParams Const)) ∉
        W.carrier := by
      intro hImp
      have hNotRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ) :=
        (by
          change ClosedTheorySet.Provable (Const := WithParams Const) W.raw
            (.imp φ (.bot : ClosedFormula (WithParams Const))) at hImp
          rcases hImp with ⟨Γ, hΓ, dImp⟩
          refine ⟨Γ, hΓ, ?_⟩
          have dImp' : ExtDerivation (WithParams Const) (φ :: Γ)
              (.imp φ (.bot : ClosedFormula (WithParams Const))) :=
            ExtDerivation.mono
              (Δ := Γ) (Δ' := φ :: Γ)
              (φ := (.imp φ (.bot : ClosedFormula (WithParams Const))))
              (by
                intro ξ hξ
                exact List.mem_cons_of_mem φ hξ)
              dImp
          have dφ : ExtDerivation (WithParams Const) (φ :: Γ) φ :=
            ExtDerivation.hyp (by simp)
          exact ExtDerivation.notI (ExtDerivation.impE dImp' dφ))
      exact hNotMem (by
        change ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ)
        exact hNotRaw)
    obtain ⟨W', _hLevel, hRaw, hφMem, _hBotNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp
        (Base := Base) (Const := Const) W S hφ hBot hNotImp
    exact hKripke W' (le_of_raw_subset (Base := Base) (Const := Const) hRaw) hφMem

theorem forces_not_level_supported
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ : ClosedFormula (WithParams Const)}
    (hφ : ClosedTheorySet.FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  constructor
  · intro hNot V hWV hφV
    have hNotV : Forces (Base := Base) (Const := Const) V (.not φ) := hWV.2 hNot
    have hBotV : Forces (Base := Base) (Const := Const) V (.bot : ClosedFormula (WithParams Const)) := by
      apply V.closed
      exact ClosedTheorySet.provable_bot_of_not (Const := WithParams Const)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hNotV)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφV)
    exact forces_bot (Base := Base) (Const := Const) V hBotV
  · intro hKripke
    by_contra hNotMem
    have hBot : ClosedTheorySet.FormulaAvoidsParamLayersFrom
        (Base := Base) (Const := Const) W.level (.bot : ClosedFormula (WithParams Const)) := by
      intro σ m k hm
      exact NoConstOccurrence.bot
    have hNotImp : (.imp φ (.bot : ClosedFormula (WithParams Const)) : ClosedFormula (WithParams Const)) ∉
        W.carrier := by
      intro hImp
      have hNotRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ) :=
        (by
          change ClosedTheorySet.Provable (Const := WithParams Const) W.raw
            (.imp φ (.bot : ClosedFormula (WithParams Const))) at hImp
          rcases hImp with ⟨Γ, hΓ, dImp⟩
          refine ⟨Γ, hΓ, ?_⟩
          have dImp' : ExtDerivation (WithParams Const) (φ :: Γ)
              (.imp φ (.bot : ClosedFormula (WithParams Const))) :=
            ExtDerivation.mono
              (Δ := Γ) (Δ' := φ :: Γ)
              (φ := (.imp φ (.bot : ClosedFormula (WithParams Const))))
              (by
                intro ξ hξ
                exact List.mem_cons_of_mem φ hξ)
              dImp
          have dφ : ExtDerivation (WithParams Const) (φ :: Γ) φ :=
            ExtDerivation.hyp (by simp)
          exact ExtDerivation.notI (ExtDerivation.impE dImp' dφ))
      exact hNotMem (by
        change ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ)
        exact hNotRaw)
    obtain ⟨W', hLevel, hRaw, hφMem, _hBotNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp
        (Base := Base) (Const := Const) W S hφ hBot hNotImp
    have hLevelLe : W.level ≤ W'.level := by
      omega
    exact hKripke W'
      (levelLe_of_raw_subset (Base := Base) (Const := Const) hLevelLe hRaw)
      hφMem

theorem forces_not_of_level_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ : ClosedFormula (WithParams Const)}
    (hLevel : maxParam φ ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_supported (Base := Base) (Const := Const) W S
    (ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hLevel
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) φ))

theorem forces_not_at
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.not φ)) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_of_level_bound (Base := Base) (Const := Const) W S
    (supported_not (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_not_level_of_level_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ : ClosedFormula (WithParams Const)}
    (hLevel : maxParam φ ≤ W.level) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_level_supported (Base := Base) (Const := Const) W S
    (ClosedTheorySet.FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hLevel
      (ClosedTheorySet.FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) φ))

theorem forces_not_level_at
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ : ClosedFormula (WithParams Const)}
    (hSupport : SupportedAt (Base := Base) (Const := Const) W (.not φ)) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_level_of_level_bound (Base := Base) (Const := Const) W S
    (supported_not (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_not_at_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) m)
    {φ : ClosedFormula (WithParams Const)}
    (hm : W.level ≤ m)
    (hφMax : maxParam φ ≤ m) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  constructor
  · intro hNot V hWV hφV
    have hNotV : Forces (Base := Base) (Const := Const) V (.not φ) := hWV hNot
    have hBotV : Forces (Base := Base) (Const := Const) V (.bot : ClosedFormula (WithParams Const)) := by
      apply V.closed
      exact ClosedTheorySet.provable_bot_of_not (Const := WithParams Const)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hNotV)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφV)
    exact forces_bot (Base := Base) (Const := Const) V hBotV
  · intro hKripke
    by_contra hNotMem
    have hNotImp : (.imp φ (.bot : ClosedFormula (WithParams Const)) : ClosedFormula (WithParams Const)) ∉
        W.carrier := by
      intro hImp
      have hNotRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ) :=
        (by
          change ClosedTheorySet.Provable (Const := WithParams Const) W.raw
            (.imp φ (.bot : ClosedFormula (WithParams Const))) at hImp
          rcases hImp with ⟨Γ, hΓ, dImp⟩
          refine ⟨Γ, hΓ, ?_⟩
          have dImp' : ExtDerivation (WithParams Const) (φ :: Γ)
              (.imp φ (.bot : ClosedFormula (WithParams Const))) :=
            ExtDerivation.mono
              (Δ := Γ) (Δ' := φ :: Γ)
              (φ := (.imp φ (.bot : ClosedFormula (WithParams Const))))
              (by
                intro ξ hξ
                exact List.mem_cons_of_mem φ hξ)
              dImp
          have dφ : ExtDerivation (WithParams Const) (φ :: Γ) φ :=
            ExtDerivation.hyp (by simp)
          exact ExtDerivation.notI (ExtDerivation.impE dImp' dφ))
      exact hNotMem (by
        change ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ)
        exact hNotRaw)
    obtain ⟨W', _hLevel, hRaw, hφMem, _hBotNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp_at_bound
        (Base := Base) (Const := Const) W S hm hφMax (by simp [maxParam]) hNotImp
    exact hKripke W' (le_of_raw_subset (Base := Base) (Const := Const) hRaw) hφMem

theorem forces_not_level_at_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) m)
    {φ : ClosedFormula (WithParams Const)}
    (hm : W.level ≤ m)
    (hφMax : maxParam φ ≤ m) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  constructor
  · intro hNot V hWV hφV
    have hNotV : Forces (Base := Base) (Const := Const) V (.not φ) := hWV.2 hNot
    have hBotV : Forces (Base := Base) (Const := Const) V (.bot : ClosedFormula (WithParams Const)) := by
      apply V.closed
      exact ClosedTheorySet.provable_bot_of_not (Const := WithParams Const)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hNotV)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφV)
    exact forces_bot (Base := Base) (Const := Const) V hBotV
  · intro hKripke
    by_contra hNotMem
    have hNotImp : (.imp φ (.bot : ClosedFormula (WithParams Const)) : ClosedFormula (WithParams Const)) ∉
        W.carrier := by
      intro hImp
      have hNotRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ) :=
        (by
          change ClosedTheorySet.Provable (Const := WithParams Const) W.raw
            (.imp φ (.bot : ClosedFormula (WithParams Const))) at hImp
          rcases hImp with ⟨Γ, hΓ, dImp⟩
          refine ⟨Γ, hΓ, ?_⟩
          have dImp' : ExtDerivation (WithParams Const) (φ :: Γ)
              (.imp φ (.bot : ClosedFormula (WithParams Const))) :=
            ExtDerivation.mono
              (Δ := Γ) (Δ' := φ :: Γ)
              (φ := (.imp φ (.bot : ClosedFormula (WithParams Const))))
              (by
                intro ξ hξ
                exact List.mem_cons_of_mem φ hξ)
              dImp
          have dφ : ExtDerivation (WithParams Const) (φ :: Γ) φ :=
            ExtDerivation.hyp (by simp)
          exact ExtDerivation.notI (ExtDerivation.impE dImp' dφ))
      exact hNotMem (by
        change ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.not φ)
        exact hNotRaw)
    obtain ⟨W', hLevel, hRaw, hφMem, _hBotNot⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp_at_bound
        (Base := Base) (Const := Const) W S hm hφMax (by simp [maxParam]) hNotImp
    have hLevelLe : W.level ≤ W'.level := by
      omega
    exact hKripke W'
      (levelLe_of_raw_subset (Base := Base) (Const := Const) hLevelLe hRaw)
      hφMem

theorem forces_not_at_max_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ : ClosedFormula (WithParams Const)}
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (max W.level (maxParam φ))) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_at_bound (Base := Base) (Const := Const) W S
    (le_max_left W.level (maxParam φ))
    (le_max_right W.level (maxParam φ))

theorem forces_not_level_at_max_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ : ClosedFormula (WithParams Const)}
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (max W.level (maxParam φ))) :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_level_at_bound (Base := Base) (Const := Const) W S
    (le_max_left W.level (maxParam φ))
    (le_max_right W.level (maxParam φ))

theorem forces_not_provider
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ : ClosedFormula (WithParams Const)} :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_at_max_bound (Base := Base) (Const := Const) W
    (P.scheduler (max W.level (maxParam φ)))

theorem forces_not_level_provider
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {φ : ClosedFormula (WithParams Const)} :
    Forces (Base := Base) (Const := Const) W (.not φ) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ¬ Forces (Base := Base) (Const := Const) V φ := by
  exact forces_not_level_at_max_bound (Base := Base) (Const := Const) W
    (P.scheduler (max W.level (maxParam φ)))

theorem forces_all_supported
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m k : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), m + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  constructor
  · intro hAll V hWV t
    exact SupportedCanonicalMembership.all_elim_mem (W := V) t (hWV hAll)
  · intro hKripke
    by_contra hNotAll
    obtain ⟨W', _hLevel, hRaw, hOmit⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_all
        (Base := Base) (Const := Const) W (m := m) (k := k) S hm hφfresh hφfuture hNotAll
    exact hOmit
      (hKripke W' (le_of_raw_subset (Base := Base) (Const := Const) hRaw)
        (.const (param σ (Nat.pair m k))))

theorem forces_all_level_supported
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m k : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), m + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  constructor
  · intro hAll V hWV t
    exact SupportedCanonicalMembership.all_elim_mem (W := V) t (hWV.2 hAll)
  · intro hKripke
    by_contra hNotAll
    obtain ⟨W', hLevel, hRaw, hOmit⟩ :=
      ClosedTheorySet.SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_all
        (Base := Base) (Const := Const) W (m := m) (k := k) S hm hφfresh hφfuture hNotAll
    have hLevelLe : W.level ≤ W'.level := by
      omega
    exact hOmit
      (hKripke W'
        (levelLe_of_raw_subset (Base := Base) (Const := Const) hLevelLe hRaw)
        (.const (param σ (Nat.pair m k))))

theorem forces_all_of_fresh_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m k : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hmW : W.level ≤ m)
    (hφMax : maxParam φ ≤ m) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  apply forces_all_supported (Base := Base) (Const := Const) W (m := m) (k := k) S hmW
  · exact noConstOccurrence_param_of_ge (Nat.pair m k) φ
      (Nat.le_trans hφMax (Nat.left_le_pair m k))
  · intro τ r j hmr
    have hφr : maxParam φ ≤ r := by
      omega
    exact noConstOccurrence_param_of_ge (Nat.pair r j) φ
      (Nat.le_trans hφr (Nat.left_le_pair r j))

theorem forces_all_at_max_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (max W.level (maxParam φ) + 1)) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_all_of_fresh_bound (Base := Base) (Const := Const) W
    (m := max W.level (maxParam φ)) (k := 0) S
    (le_max_left W.level (maxParam φ))
    (le_max_right W.level (maxParam φ))

theorem forces_all_level_of_fresh_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {m k : Nat}
    (S : ClosedTheorySet.RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hmW : W.level ≤ m)
    (hφMax : maxParam φ ≤ m) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  apply forces_all_level_supported (Base := Base) (Const := Const) W (m := m) (k := k) S hmW
  · exact noConstOccurrence_param_of_ge (Nat.pair m k) φ
      (Nat.le_trans hφMax (Nat.left_le_pair m k))
  · intro τ r j hmr
    have hφr : maxParam φ ≤ r := by
      omega
    exact noConstOccurrence_param_of_ge (Nat.pair r j) φ
      (Nat.le_trans hφr (Nat.left_le_pair r j))

theorem forces_all_level_at_max_bound
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (max W.level (maxParam φ) + 1)) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_all_level_of_fresh_bound (Base := Base) (Const := Const) W
    (m := max W.level (maxParam φ)) (k := 0) S
    (le_max_left W.level (maxParam φ))
    (le_max_right W.level (maxParam φ))

theorem forces_all_at
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (W.level + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.all φ : ClosedFormula (WithParams Const))) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_all_of_fresh_bound (Base := Base) (Const := Const) W
    (m := W.level) (k := 0) S (Nat.le_refl W.level)
    (supported_all_body (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_all_level_at
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (S : ClosedTheorySet.RawAlternatingStageScheduler
      (Base := Base) (Const := Const) (W.level + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hSupport : SupportedAt (Base := Base) (Const := Const)
      W (.all φ : ClosedFormula (WithParams Const))) :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_all_level_of_fresh_bound (Base := Base) (Const := Const) W
    (m := W.level) (k := 0) S (Nat.le_refl W.level)
    (supported_all_body (Base := Base) (Const := Const) (W := W) hSupport)

theorem forces_all_provider
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        Le (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_all_at_max_bound (Base := Base) (Const := Const) W
    (P.scheduler (max W.level (maxParam φ) + 1))

theorem forces_all_level_provider
    (P : SchedulerProvider (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
      ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
        LevelLe (Base := Base) (Const := Const) W V →
          ∀ t : ClosedTerm (WithParams Const) σ,
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  exact forces_all_level_at_max_bound (Base := Base) (Const := Const) W
    (P.scheduler (max W.level (maxParam φ) + 1))

/-- The honest level-aware canonical truth-lemma interface for supported
presented worlds.  Local disjunction and existential clauses require the
formula to be supported by the current world's level; implication, negation,
and universal clauses quantify over level-growing successors. -/
structure LevelSupportedTruthClauses
    (P : SchedulerProvider (Base := Base) Const) where
  or_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {φ ψ : ClosedFormula (WithParams Const)},
      SupportedAt (Base := Base) (Const := Const) W (.or φ ψ) →
        (Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
          Forces (Base := Base) (Const := Const) W φ ∨
            Forces (Base := Base) (Const := Const) W ψ)
  ex_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      SupportedAt (Base := Base) (Const := Const) W
        (.ex φ : ClosedFormula (WithParams Const)) →
        (Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
          ∃ t : ClosedTerm (WithParams Const) σ,
            ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
              LevelLe (Base := Base) (Const := Const) W V →
                Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ))
  imp_clause :
    ∀ (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
      {φ ψ : ClosedFormula (WithParams Const)},
      SupportedAt (Base := Base) (Const := Const) W (.imp φ ψ) →
        (Forces (Base := Base) (Const := Const) W (.imp φ ψ) ↔
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W V →
              Forces (Base := Base) (Const := Const) V φ →
                Forces (Base := Base) (Const := Const) V ψ)
  not_clause :
    ∀ (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
      {φ : ClosedFormula (WithParams Const)},
      SupportedAt (Base := Base) (Const := Const) W (.not φ) →
        (Forces (Base := Base) (Const := Const) W (.not φ) ↔
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W V →
              ¬ Forces (Base := Base) (Const := Const) V φ)
  all_clause :
    ∀ (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
      {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      SupportedAt (Base := Base) (Const := Const) W
        (.all φ : ClosedFormula (WithParams Const)) →
        (Forces (Base := Base) (Const := Const) W (.all φ : ClosedFormula (WithParams Const)) ↔
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W V →
              ∀ t : ClosedTerm (WithParams Const) σ,
                Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ))

/-- The level-aware supported truth clauses are already available from the raw
successor machinery and a scheduler provider. -/
def levelSupportedTruthClauses
    (P : SchedulerProvider (Base := Base) Const) :
    LevelSupportedTruthClauses (Base := Base) (Const := Const) P where
  or_clause := by
    intro W φ ψ hSupport
    exact forces_or_at (Base := Base) (Const := Const) (W := W) hSupport
  ex_clause := by
    intro W σ φ hSupport
    exact forces_ex_level_kripke_at (Base := Base) (Const := Const) (W := W) hSupport
  imp_clause := by
    intro W φ ψ _hSupport
    exact forces_imp_level_provider (Base := Base) (Const := Const) P W
  not_clause := by
    intro W φ _hSupport
    exact forces_not_level_provider (Base := Base) (Const := Const) P W
  all_clause := by
    intro W σ φ _hSupport
    exact forces_all_level_provider (Base := Base) (Const := Const) P W

theorem eq_refl {τ : Ty Base}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (t : ClosedTerm (WithParams Const) τ) :
    EqVal (Base := Base) (Const := Const) W t t :=
  SupportedCanonicalMembership.eq_refl_mem (W := W) t

theorem eq_symm {τ : Ty Base}
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {s t : ClosedTerm (WithParams Const) τ}
    (hst : EqVal (Base := Base) (Const := Const) W s t) :
    EqVal (Base := Base) (Const := Const) W t s :=
  SupportedCanonicalMembership.eq_symm_mem (W := W) hst

theorem eq_trans {τ : Ty Base}
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {r s t : ClosedTerm (WithParams Const) τ}
    (hrs : EqVal (Base := Base) (Const := Const) W r s)
    (hst : EqVal (Base := Base) (Const := Const) W s t) :
    EqVal (Base := Base) (Const := Const) W r t :=
  SupportedCanonicalMembership.eq_trans_mem (W := W) hrs hst

theorem eq_app_congr {σ τ : Ty Base}
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    {s t : ClosedTerm (WithParams Const) σ}
    (hfg : EqVal (Base := Base) (Const := Const) W f g)
    (hst : EqVal (Base := Base) (Const := Const) W s t) :
    EqVal (Base := Base) (Const := Const) W (.app f s) (.app g t) :=
  SupportedCanonicalMembership.eq_app_congr_mem (W := W) hfg hst

theorem eq_funext {σ τ : Ty Base}
    {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    (hpoint :
      ∀ t : ClosedTerm (WithParams Const) σ,
        EqVal (Base := Base) (Const := Const) W (.app f t) (.app g t)) :
    EqVal (Base := Base) (Const := Const) W f g :=
  SupportedCanonicalMembership.eq_funext_mem (W := W) hpoint

theorem eq_beta {σ τ : Ty Base}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (t : ClosedTerm (WithParams Const) σ) (u : Term (WithParams Const) [σ] τ) :
    EqVal (Base := Base) (Const := Const) W (.app (.lam u) t) (instantiate (Base := Base) t u) :=
  SupportedCanonicalMembership.eq_beta_mem (W := W) t u

theorem eq_eta {σ τ : Ty Base}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (f : ClosedTerm (WithParams Const) (σ ⇒ τ)) :
    EqVal (Base := Base) (Const := Const) W
      (.lam (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f) (.var .vz)))
      f :=
  SupportedCanonicalMembership.eq_eta_mem (W := W) f

end SupportedCanonicalFrame

end KripkeHenkin

end Mettapedia.Logic.HOL
