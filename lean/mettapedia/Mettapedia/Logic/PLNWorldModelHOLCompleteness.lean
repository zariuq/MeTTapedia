import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.HOL.WorldModelCompleteness
import Mettapedia.Logic.HOL.TermModel.HenkinCompleteness
import Mettapedia.Logic.HOL.Soundness

/-!
# HOL WM Consequence-Closure Wrappers

Public PLN-facing aliases for the real Church-style HOL consequence bridge.

Despite the legacy filename, "completeness" here means WM-side
consequence closure/transport, not a separate HOL metatheoretic completeness
theorem.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLCompleteness

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Public HOL query alias. -/
abbrev HOLQuery := @Mettapedia.Logic.HOL.WorldModelCompleteness.HOLQuery

/-- Public pointed HOL model alias. -/
abbrev PointedHOL := @Mettapedia.Logic.HOL.HenkinModel

/-- Public HOL state alias. -/
abbrev HOLState := @Mettapedia.Logic.HOL.WorldModelCompleteness.HOLState

/-- Public categorical endpoint alias for HOL world-model states. -/
abbrev WMCategoricalEndpointSurface :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.WMCategoricalEndpointSurface

/-- Public pointwise implication relation for closed HOL formulas. -/
abbrev pointwiseImplies (φ ψ : HOLQuery (Base := Base) Const) : Prop :=
  ∀ M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const,
    Mettapedia.Logic.HOL.WorldModel.holSatisfies (Base := Base) (Const := Const) M φ →
      Mettapedia.Logic.HOL.WorldModel.holSatisfies (Base := Base) (Const := Const) M ψ

/-- Public singleton-strength relation for closed HOL formulas. -/
abbrev singletonStrengthLE (φ ψ : HOLQuery (Base := Base) Const) : Prop :=
  ∀ M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const,
    BinaryWorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) φ ≤
      BinaryWorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) ψ

/-- Naming alias for the singleton-strength consequence relation. -/
abbrev singletonConsequence (φ ψ : HOLQuery (Base := Base) Const) : Prop :=
  ∀ M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const,
    BinaryWorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) φ ≤
      BinaryWorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) ψ

abbrev pointwiseImplies_iff_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.pointwiseImplies_iff_singletonStrengthLE

abbrev pointwiseImplies_iff_singletonConsequence :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.pointwiseImplies_iff_singletonConsequence

abbrev pointwiseIff_iff_queryEq :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.pointwiseIff_iff_queryEq

abbrev multiset_strength_le_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_pointwise

abbrev multiset_consequence_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_consequence_of_pointwise

abbrev multiset_strength_le_of_pointwise_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_pointwise_categorical

abbrev multiset_strength_le_of_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_singletonStrengthLE

abbrev multiset_consequence_of_singletonConsequence :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_consequence_of_singletonConsequence

abbrev externalImplication_iff_singletonConsequence_of_sound_complete :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.externalImplication_iff_singletonConsequence_of_sound_complete

abbrev multiset_consequence_of_externalImplication_sound :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_consequence_of_externalImplication_sound

abbrev multiset_strength_le_of_singletonStrengthLE_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_singletonStrengthLE_categorical

abbrev wmConsequenceRule_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRule_of_pointwise

abbrev wmConsequenceRule_of_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRule_of_singletonStrengthLE

noncomputable abbrev wmConsequenceRuleOn_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_pointwise

noncomputable abbrev wmConsequenceRuleOn_of_pointwise_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_pointwise_categorical

noncomputable abbrev wmConsequenceRuleOn_of_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_singletonStrengthLE

noncomputable abbrev wmConsequenceRuleOn_of_singletonStrengthLE_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_singletonStrengthLE_categorical

/-!
## Classical theory-model states for HO WM-PLN

The higher-order WM layer now exposes the actual classical Henkin footing as a
theory-model abstraction:

- theories are closed HOL theories over `WithParams Const`,
- states are multisets of pointed Henkin models satisfying such a theory,
- pointwise implication on those theory-model states transports to WM strength
  inequalities, and
- classical consistency yields a concrete singleton WM state by Henkin
  completeness.

This makes the landed completeness theorem load-bearing for WM-PLN at the
model-class grounding layer, even before the stronger proof-theoretic
`provable ↔ consequence` bridge is finished for the public no-assumptions
surface.
-/

/-- The actual classical Henkin theory surface used by HO WM-PLN. -/
abbrev ClassicalHOLTheory := ClosedTheorySet (WithParams Const)

/-- Closed HOL queries over the parameter-extended classical surface. -/
abbrev ClassicalHOLQuery := HOLQuery (Base := Base) (WithParams Const)

/-- Pointed Henkin models over the parameter-extended classical surface. -/
abbrev ClassicalHOLPointed := Mettapedia.Logic.HOL.HenkinModel.{u, v, v} Base (WithParams Const)

/-- WM states built from classical Henkin models of a higher-order theory. -/
abbrev ClassicalHOLState := Multiset (Mettapedia.Logic.HOL.HenkinModel.{u, v, v} Base (WithParams Const))

/-- State-side condition: every pointed Henkin model in `W` satisfies `T`. -/
def stateModelsTheory
    (T : ClosedTheorySet (WithParams Const))
    (W : ClassicalHOLState (Base := Base) (Const := Const)) : Prop :=
  ∀ M ∈ W, ∀ ψ ∈ T, HenkinModel.models M ψ

/-- Pointwise HOL implication restricted to pointed models of a classical theory. -/
def pointwiseImpliesOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) : Prop :=
  ∀ M : ClassicalHOLPointed (Base := Base) (Const := Const),
    (∀ χ ∈ T, HenkinModel.models M χ) →
      HenkinModel.models M φ →
        HenkinModel.models M ψ

/-- Singleton-strength consequence restricted to pointed models of a classical theory. -/
def singletonStrengthLEOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) : Prop :=
  ∀ M : ClassicalHOLPointed (Base := Base) (Const := Const),
    (∀ χ ∈ T, HenkinModel.models M χ) →
      BinaryWorldModel.queryStrength
          (State := ClassicalHOLState (Base := Base) (Const := Const))
          (Query := HOLQuery (Base := Base) (WithParams Const))
          ({M} : ClassicalHOLState (Base := Base) (Const := Const)) φ ≤
        BinaryWorldModel.queryStrength
          (State := ClassicalHOLState (Base := Base) (Const := Const))
          (Query := HOLQuery (Base := Base) (WithParams Const))
          ({M} : ClassicalHOLState (Base := Base) (Const := Const)) ψ

/-- Fixed-structure singleton WM consequence is equivalent to semantic implication there. -/
theorem singletonStrengthLE_singleton_iff_imp
    (M : ClassicalHOLPointed (Base := Base) (Const := Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) :
    (BinaryWorldModel.queryStrength
        (State := ClassicalHOLState (Base := Base) (Const := Const))
        (Query := HOLQuery (Base := Base) (WithParams Const))
        ({M} : ClassicalHOLState (Base := Base) (Const := Const)) φ ≤
      BinaryWorldModel.queryStrength
        (State := ClassicalHOLState (Base := Base) (Const := Const))
        (Query := HOLQuery (Base := Base) (WithParams Const))
        ({M} : ClassicalHOLState (Base := Base) (Const := Const)) ψ) ↔
      (HenkinModel.models M φ → HenkinModel.models M ψ) := by
  constructor
  · intro hle hφ
    by_contra hψ
    have h1 :
        BinaryWorldModel.queryStrength
            (State := ClassicalHOLState (Base := Base) (Const := Const))
            (Query := HOLQuery (Base := Base) (WithParams Const))
            ({M} : ClassicalHOLState (Base := Base) (Const := Const)) φ = 1 :=
      Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_satisfies
        (Base := Base) (Const := WithParams Const) M φ hφ
    have h0 :
        BinaryWorldModel.queryStrength
            (State := ClassicalHOLState (Base := Base) (Const := Const))
            (Query := HOLQuery (Base := Base) (WithParams Const))
            ({M} : ClassicalHOLState (Base := Base) (Const := Const)) ψ = 0 :=
      Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_not_satisfies
        (Base := Base) (Const := WithParams Const) M ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have h10' := hle
      rw [h1, h0] at h10'
      exact h10'
    exact (not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1)) h10
  · intro himp
    by_cases hφ : HenkinModel.models M φ
    · have hψ : HenkinModel.models M ψ := himp hφ
      rw [Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_satisfies
            (Base := Base) (Const := WithParams Const) M φ hφ]
      rw [Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_satisfies
            (Base := Base) (Const := WithParams Const) M ψ hψ]
    · rw [Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_not_satisfies
            (Base := Base) (Const := WithParams Const) M φ hφ]
      exact zero_le

/-- Naming alias: singleton consequence on models of a classical HOL theory. -/
abbrev singletonConsequenceOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) : Prop :=
  singletonStrengthLEOnTheory T φ ψ

/-- Model-restricted pointwise implication iff model-restricted singleton WM consequence. -/
theorem pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) :
    pointwiseImpliesOnTheory T φ ψ ↔
      singletonStrengthLEOnTheory T φ ψ := by
  constructor
  · intro himp M hT
    exact
      (singletonStrengthLE_singleton_iff_imp
        (Base := Base) (Const := Const) (M := M) (φ := φ) (ψ := ψ)).2
        (himp M hT)
  · intro hsing M hT hφ
    exact
      (singletonStrengthLE_singleton_iff_imp
        (Base := Base) (Const := Const) (M := M) (φ := φ) (ψ := ψ)).1
        (hsing M hT) hφ

/-- Naming alias for the same bridge with `singletonConsequence` terminology. -/
theorem pointwiseImpliesOnTheory_iff_singletonConsequenceOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) :
    pointwiseImpliesOnTheory T φ ψ ↔
      singletonConsequenceOnTheory T φ ψ :=
  pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
    T φ ψ

/-- Sound theory-relative implication surface for HO WM-PLN:
a finite higher-order derivation of `φ → ψ` from assumptions drawn from `T`. -/
def derivableImpOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const)) : Prop :=
  ∃ Γ : ClosedTheory (WithParams Const),
    (∀ χ, χ ∈ Γ → χ ∈ T) ∧
      Derivation (WithParams Const) Γ (.imp φ ψ)

/-- Finite theory-relative HOL derivability transports to pointwise implication
on classical theory-model states. -/
theorem derivableImpOnTheory_implies_pointwiseImpliesOnTheory
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (hprov : derivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    pointwiseImpliesOnTheory T φ ψ := by
  rcases hprov with ⟨Γ, hΓ, d⟩
  intro M hT hφ
  have hImp : HenkinModel.models M (.imp φ ψ) := by
    exact
      Mettapedia.Logic.HOL.Soundness.derivation_sound
        (Base := Base) (Const := WithParams Const) (d := d)
        (M := M) (ρ := fun v => nomatch v)
        (by
          intro τ v
          nomatch v)
        (by
          intro χ hχ
          exact hT χ (hΓ χ hχ))
  exact (HenkinModel.models_imp M).mp hImp hφ

/-- Finite theory-relative HOL derivability transports directly to singleton WM
consequence on classical theory-model states. -/
theorem derivableImpOnTheory_implies_singletonStrengthLEOnTheory
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (hprov : derivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    singletonStrengthLEOnTheory T φ ψ :=
  (pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
    (Base := Base) (Const := Const) T φ ψ).mp
    (derivableImpOnTheory_implies_pointwiseImpliesOnTheory
      (Base := Base) (Const := Const) hprov)

private theorem provable_of_provable_notnot_closed_em
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hnn : ClosedTheorySet.Provable (Const := WithParams Const) T (.not (.not χ))) :
    ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  have hem :
      ClosedTheorySet.Provable (Const := WithParams Const) T (.or χ (.not χ)) :=
    ClosedTheorySet.provable_of_mem
      (Const := WithParams Const)
      (T := T)
      (hEM _ (emClosed_mem (Const := Const) χ))
  have hswap :
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.imp (.or χ (.not χ)) (.or (.not χ) χ)) :=
    ClosedTheorySet.Provable.or_elim
      (Const := WithParams Const)
      (T := T)
      (φ := χ)
      (ψ := .not χ)
      (χ := .or (.not χ) χ)
      (ClosedTheorySet.Provable.or_intro_right
        (Const := WithParams Const) (T := T) (.not χ) χ)
      (ClosedTheorySet.Provable.or_intro_left
        (Const := WithParams Const) (T := T) (.not χ) χ)
  have hemSwap :
      ClosedTheorySet.Provable (Const := WithParams Const) T (.or (.not χ) χ) :=
    ClosedTheorySet.Provable.imp_mp hswap hem
  exact
    provable_or_elim_left
      (Const := WithParams Const)
      (T := T)
      (φ := .not χ)
      (ψ := χ)
      hemSwap
      hnn

/-- If a classical EM-closed theory does not prove `χ`, adjoining `¬χ`
remains consistent. This is the public countermodel-preparation lemma used by
the completeness-tight HO-PLN credal envelope. -/
theorem consistent_insert_not_of_not_provable_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hNotProv : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ) :
    ClosedTheorySet.Consistent (Const := WithParams Const) (insert (.not χ) T) := by
  intro hIncon
  apply hNotProv
  exact
    provable_of_provable_notnot_closed_em
      (Base := Base)
      (Const := Const)
      hEM
      (provable_not_of_imp_bot
        (Const := WithParams Const)
        (T := T)
        (χ := .not χ)
        (provable_imp_of_insert
          (Const := WithParams Const)
          (T := T)
          (χ := .not χ)
          (ψ := .bot)
          hIncon))

/-- Classical Henkin completeness gives an actual `T`-model refuting any
param-free query that `T` does not prove. -/
theorem exists_model_not_models_of_not_provable_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProv : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧ ¬ HenkinModel.models M χ := by
  have hInsertCons :
      ClosedTheorySet.Consistent (Const := WithParams Const)
        (insert (.not χ) T) :=
    consistent_insert_not_of_not_provable_classical
      (Base := Base) (Const := Const) (T := T) (χ := χ) hEM hNotProv
  obtain ⟨M, hM⟩ :=
    ClosedTheorySet.henkin_model_exists_of_consistent_classical
      (Base := Base)
      (Const := Const)
      (T := insert (.not χ) T)
      enum
      henum
      hInsertCons
      (by
        intro ψ hψ σ k
        rcases Set.mem_insert_iff.mp hψ with rfl | hψT
        · exact NoConstOccurrence.not (hχ0 σ k)
        · exact hT0 ψ hψT σ k)
      (by
        intro ψ hψ
        exact Set.mem_insert_iff.mpr (.inr (hEM ψ hψ)))
  refine ⟨M, ?_, ?_⟩
  · intro ψ hψ
    exact hM ψ (Set.mem_insert_iff.mpr (.inr hψ))
  · have hNotχ : HenkinModel.models M (.not χ) :=
      hM (.not χ) (Set.mem_insert_iff.mpr (.inl rfl))
    exact (HenkinModel.models_not M).mp hNotχ

/-- Extensional classical Henkin completeness gives an actual `T`-model
refuting any param-free query that `T` does not prove, together with the
semantic congruence law needed for `ExtDerivation` soundness. -/
theorem exists_extensional_model_not_models_of_not_provable_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProv : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧
        ¬ HenkinModel.models M χ ∧
          HenkinModel.FunctionsRespectEqv M := by
  have hInsertCons :
      ClosedTheorySet.Consistent (Const := WithParams Const)
        (insert (.not χ) T) :=
    consistent_insert_not_of_not_provable_classical
      (Base := Base) (Const := Const) (T := T) (χ := χ) hEM hNotProv
  obtain ⟨M, hM, hExt⟩ :=
    ClosedTheorySet.henkin_extensional_model_exists_of_consistent_classical
      (Base := Base)
      (Const := Const)
      (T := insert (.not χ) T)
      enum
      henum
      hInsertCons
      (by
        intro ψ hψ σ k
        rcases Set.mem_insert_iff.mp hψ with rfl | hψT
        · exact NoConstOccurrence.not (hχ0 σ k)
        · exact hT0 ψ hψT σ k)
      (by
        intro ψ hψ
        exact Set.mem_insert_iff.mpr (.inr (hEM ψ hψ)))
  refine ⟨M, ?_, ?_, hExt⟩
  · intro ψ hψ
    exact hM ψ (Set.mem_insert_iff.mpr (.inr hψ))
  · have hNotχ : HenkinModel.models M (.not χ) :=
      hM (.not χ) (Set.mem_insert_iff.mpr (.inl rfl))
    exact (HenkinModel.models_not M).mp hNotχ

/-- Classical Henkin completeness gives an actual `T`-model satisfying `χ`
whenever `T` does not prove `¬χ`. -/
theorem exists_model_models_of_not_provable_not_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProvNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ)) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧ HenkinModel.models M χ := by
  obtain ⟨M, hMT, hNotNotχ⟩ :=
    exists_model_not_models_of_not_provable_classical
      (Base := Base)
      (Const := Const)
      (T := T)
      (χ := .not χ)
      enum
      henum
      hT0
      hEM
      (by
        intro σ k
        exact NoConstOccurrence.not (hχ0 σ k))
      hNotProvNot
  refine ⟨M, hMT, ?_⟩
  by_contra hχ
  exact hNotNotχ ((HenkinModel.models_not M).mpr hχ)

/-- Extensional classical Henkin completeness gives an actual `T`-model
satisfying `χ` whenever `T` does not prove `¬χ`, together with the semantic
congruence law needed for `ExtDerivation` soundness. -/
theorem exists_extensional_model_models_of_not_provable_not_classical
    {T : ClosedTheorySet (WithParams Const)}
    {χ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hχ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hNotProvNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ)) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧
        HenkinModel.models M χ ∧
          HenkinModel.FunctionsRespectEqv M := by
  obtain ⟨M, hMT, hNotNotχ, hExt⟩ :=
    exists_extensional_model_not_models_of_not_provable_classical
      (Base := Base)
      (Const := Const)
      (T := T)
      (χ := .not χ)
      enum
      henum
      hT0
      hEM
      (by
        intro σ k
        exact NoConstOccurrence.not (hχ0 σ k))
      hNotProvNot
  refine ⟨M, hMT, ?_, hExt⟩
  by_contra hχ
  exact hNotNotχ ((HenkinModel.models_not M).mpr hχ)

/-- Classical completeness closes the theory-relative higher-order
provability/consequence bridge for implication queries over `T`-models. -/
theorem provable_imp_onTheory_of_pointwiseImpliesOnTheory_classical
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ χ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hEM : ∀ χ ∈ EMSchema Const, χ ∈ T)
    (hImp0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) (.imp φ ψ))
    (himp : pointwiseImpliesOnTheory T φ ψ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) := by
  by_cases hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T
  · by_contra hNotProv
    have hInsertCons :
      ClosedTheorySet.Consistent (Const := WithParams Const)
        (insert (.not (.imp φ ψ)) T) :=
      consistent_insert_not_of_not_provable_classical
        (Base := Base)
        (Const := Const)
        (T := T)
        (χ := .imp φ ψ)
        hEM
        hNotProv
    obtain ⟨M, hM⟩ :=
      ClosedTheorySet.henkin_model_exists_of_consistent_classical
        (Base := Base)
        (Const := Const)
        (T := insert (.not (.imp φ ψ)) T)
        enum
        henum
        hInsertCons
        (by
          intro χ hχ σ k
          rcases Set.mem_insert_iff.mp hχ with rfl | hχT
          · exact NoConstOccurrence.not (hImp0 σ k)
          · exact hT0 χ hχT σ k)
        (by
          intro χ hχ
          exact Set.mem_insert_iff.mpr (.inr (hEM χ hχ)))
    have hMT : ∀ χ ∈ T, HenkinModel.models M χ := by
      intro χ hχ
      exact hM χ (Set.mem_insert_iff.mpr (.inr hχ))
    have hNotImp : HenkinModel.models M (.not (.imp φ ψ)) :=
      hM (.not (.imp φ ψ)) (Set.mem_insert_iff.mpr (.inl rfl))
    have hImp : HenkinModel.models M (.imp φ ψ) := by
      exact (HenkinModel.models_imp M).2 (himp M hMT)
    exact ((HenkinModel.models_not M).mp hNotImp) hImp
  · have hBot : ClosedTheorySet.Inconsistent (Const := WithParams Const) T := by
      exact not_not.mp hCons
    exact
      ClosedTheorySet.provable_mp
        (Const := WithParams Const)
        (T := T)
        (φ := (.bot : ClosedFormula (WithParams Const)))
        (ψ := (.imp φ ψ))
        (ClosedTheorySet.Provable.bot_imp
          (Const := WithParams Const)
          (T := T)
          (.imp φ ψ))
        hBot

/-- Classical completeness closes the semantic-to-proof direction for the
extensional closed-theory proof surface used by HOL completeness. -/
theorem provable_imp_onTheory_of_singletonStrengthLEOnTheory_classical
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ χ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hEM : ∀ χ ∈ EMSchema Const, χ ∈ T)
    (hImp0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) (.imp φ ψ)) :
    singletonStrengthLEOnTheory T φ ψ →
      ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) := by
  intro hsing
  exact
    provable_imp_onTheory_of_pointwiseImpliesOnTheory_classical
      (Base := Base)
      (Const := Const)
      enum
      henum
      hT0
      hEM
      hImp0
      ((pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
        (Base := Base)
        (Const := Const)
        T
        φ
        ψ).mpr hsing)

/-- Naming alias: classical singleton consequence implies provability in the
extensional closed-theory proof surface used by HOL completeness. -/
theorem provable_imp_onTheory_of_singletonConsequenceOnTheory_classical
    {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hT0 : ∀ χ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) χ)
    (hEM : ∀ χ ∈ EMSchema Const, χ ∈ T)
    (hImp0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) (.imp φ ψ)) :
    singletonConsequenceOnTheory T φ ψ →
      ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) :=
  provable_imp_onTheory_of_singletonStrengthLEOnTheory_classical
    (Base := Base)
    (Const := Const)
    enum
    henum
    hT0
    hEM
    hImp0

private theorem countP_le_countP_of_imp_on
    (W : HOLState (Base := Base) (WithParams Const))
    {p q : HenkinModel Base (WithParams Const) → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ M ∈ W, p M → q M) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      have himp_tail : ∀ M ∈ W, p M → q M := by
        intro M hmem hp
        exact himp M (by simp [hmem]) hp
      by_cases hp : p a
      · have hq : q a := himp a (by simp) hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ (ih himp_tail)
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans (ih himp_tail) (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq]
            using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih himp_tail

private theorem holEvidence_total
    (W : ClassicalHOLState (Base := Base) (Const := Const))
    (φ : HOLQuery (Base := Base) (WithParams Const)) :
    (Mettapedia.Logic.HOL.WorldModel.holEvidence
      (Base := Base) (Const := WithParams Const) W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP
            (fun M : HenkinModel Base (WithParams Const) =>
              Mettapedia.Logic.HOL.WorldModel.holSatisfies
                (Base := Base) (Const := WithParams Const) M φ) W +
          Multiset.countP
            (fun M : HenkinModel Base (WithParams Const) =>
              ¬ Mettapedia.Logic.HOL.WorldModel.holSatisfies
                (Base := Base) (Const := WithParams Const) M φ) W := by
    simpa using
      (Multiset.card_eq_countP_add_countP
        (p := fun M : HenkinModel Base (WithParams Const) =>
          Mettapedia.Logic.HOL.WorldModel.holSatisfies
            (Base := Base) (Const := WithParams Const) M φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP
            (fun M : HenkinModel Base (WithParams Const) =>
              Mettapedia.Logic.HOL.WorldModel.holSatisfies
                (Base := Base) (Const := WithParams Const) M φ) W : ℝ≥0∞) +
          (Multiset.countP
            (fun M : HenkinModel Base (WithParams Const) =>
              ¬ Mettapedia.Logic.HOL.WorldModel.holSatisfies
                (Base := Base) (Const := WithParams Const) M φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold Mettapedia.Logic.HOL.WorldModel.holEvidence
  unfold Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.total
  simpa using hcard.symm

/-- Multiset WM strength inequality from pointwise implication on models of a classical theory. -/
theorem queryStrength_le_of_pointwise_onTheory
    (T : ClosedTheorySet (WithParams Const))
    (W : ClassicalHOLState (Base := Base) (Const := Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const))
    (hW : stateModelsTheory T W)
    (himp : pointwiseImpliesOnTheory T φ ψ) :
    BinaryWorldModel.queryStrength
        (State := ClassicalHOLState (Base := Base) (Const := Const))
        (Query := HOLQuery (Base := Base) (WithParams Const))
        W φ ≤
      BinaryWorldModel.queryStrength
        (State := ClassicalHOLState (Base := Base) (Const := Const))
        (Query := HOLQuery (Base := Base) (WithParams Const))
        W ψ := by
  let pφ : HenkinModel Base (WithParams Const) → Prop :=
    fun M => Mettapedia.Logic.HOL.WorldModel.holSatisfies
      (Base := Base) (Const := WithParams Const) M φ
  let pψ : HenkinModel Base (WithParams Const) → Prop :=
    fun M => Mettapedia.Logic.HOL.WorldModel.holSatisfies
      (Base := Base) (Const := WithParams Const) M ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      BinaryWorldModel.queryStrength
          (State := ClassicalHOLState (Base := Base) (Const := Const))
          (Query := HOLQuery (Base := Base) (WithParams Const))
          W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength
    unfold Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength
    change (if (Mettapedia.Logic.HOL.WorldModel.holEvidence
        (Base := Base) (Const := WithParams Const) W φ).total = 0 then 0
      else (Mettapedia.Logic.HOL.WorldModel.holEvidence
        (Base := Base) (Const := WithParams Const) W φ).pos /
        (Mettapedia.Logic.HOL.WorldModel.holEvidence
          (Base := Base) (Const := WithParams Const) W φ).total) =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [holEvidence_total (W := W) (φ := φ)]
    simp [Mettapedia.Logic.HOL.WorldModel.holEvidence, pφ]
  have hψ :
      BinaryWorldModel.queryStrength
          (State := ClassicalHOLState (Base := Base) (Const := Const))
          (Query := HOLQuery (Base := Base) (WithParams Const))
          W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength
    unfold Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength
    change (if (Mettapedia.Logic.HOL.WorldModel.holEvidence
        (Base := Base) (Const := WithParams Const) W ψ).total = 0 then 0
      else (Mettapedia.Logic.HOL.WorldModel.holEvidence
        (Base := Base) (Const := WithParams Const) W ψ).pos /
        (Mettapedia.Logic.HOL.WorldModel.holEvidence
          (Base := Base) (Const := WithParams Const) W ψ).total) =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [holEvidence_total (W := W) (φ := ψ)]
    simp [Mettapedia.Logic.HOL.WorldModel.holEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp_on (W := W) (p := pφ) (q := pψ) (by
        intro M hmem hp
        exact himp M (hW M hmem) hp)
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Package sound finite theory-relative HOL derivability as a state-indexed WM
consequence rule on classical theory-model states. -/
def wmConsequenceRuleOn_of_derivableImpOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const))
    (hprov : derivableImpOnTheory (Base := Base) (Const := Const) T φ ψ) :
    WMConsequenceRuleOn
      (ClassicalHOLState (Base := Base) (Const := Const))
      (HOLQuery (Base := Base) (WithParams Const)) where
  side := stateModelsTheory T
  premise := φ
  conclusion := ψ
  sound := by
    intro W hW
    exact
      queryStrength_le_of_pointwise_onTheory
        T W φ ψ hW
        (derivableImpOnTheory_implies_pointwiseImpliesOnTheory
          (Base := Base)
          (Const := Const)
          hprov)

/-- Package theory-restricted semantic implication as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_pointwiseOnTheory
    (T : ClosedTheorySet (WithParams Const))
    (φ ψ : HOLQuery (Base := Base) (WithParams Const))
    (himp : pointwiseImpliesOnTheory T φ ψ) :
    WMConsequenceRuleOn
      (ClassicalHOLState (Base := Base) (Const := Const))
      (HOLQuery (Base := Base) (WithParams Const)) where
  side := stateModelsTheory T
  premise := φ
  conclusion := ψ
  sound := by
    intro W hW
    exact
      queryStrength_le_of_pointwise_onTheory
        T W φ ψ hW himp

/-- Classical Henkin completeness yields a concrete pointed model of `T`. -/
theorem exists_model_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const), ∀ ψ ∈ T, HenkinModel.models M ψ := by
  exact
    ClosedTheorySet.henkin_model_exists_of_consistent_classical
      (Base := Base) (Const := Const) (T := T) enum henum hCons hT0 hEM

/-- Classical Henkin completeness yields a concrete extensional pointed model
of `T`, preserving the semantic congruence law needed by `ExtDerivation`
soundness. -/
theorem exists_extensional_model_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ∃ M : ClassicalHOLPointed (Base := Base) (Const := Const),
      (∀ ψ ∈ T, HenkinModel.models M ψ) ∧
        HenkinModel.FunctionsRespectEqv M := by
  exact
    ClosedTheorySet.henkin_extensional_model_exists_of_consistent_classical
      (Base := Base) (Const := Const) (T := T) enum henum hCons hT0 hEM

/-- Completeness grounds a classical higher-order theory in a nonempty singleton WM state. -/
theorem exists_singletonStateModelsTheory_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ∃ W : ClassicalHOLState (Base := Base) (Const := Const),
      stateModelsTheory T W := by
  obtain ⟨M, hM⟩ :=
    exists_model_of_consistent_classicalTheory
      (T := T) enum henum hCons hT0 hEM
  refine ⟨({M} : ClassicalHOLState (Base := Base) (Const := Const)), ?_⟩
  intro N hN ψ hψ
  have hNM : N = M := by simpa using hN
  subst hNM
  exact hM ψ hψ

/-- A theory member gets concrete WM support `1` in the singleton state supplied by completeness. -/
theorem exists_singletonState_with_member_strength_one_of_consistent_classicalTheory
    {T : ClosedTheorySet (WithParams Const)}
    {φ : HOLQuery (Base := Base) (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (hφ : φ ∈ T) :
    ∃ W : ClassicalHOLState (Base := Base) (Const := Const),
      stateModelsTheory T W ∧
        BinaryWorldModel.queryStrength
            (State := ClassicalHOLState (Base := Base) (Const := Const))
            (Query := HOLQuery (Base := Base) (WithParams Const))
            W φ = 1 := by
  obtain ⟨M, hM⟩ :=
    exists_model_of_consistent_classicalTheory
      (T := T) enum henum hCons hT0 hEM
  refine ⟨({M} : ClassicalHOLState (Base := Base) (Const := Const)), ?_, ?_⟩
  · intro N hN ψ hψ
    have hNM : N = M := by simpa using hN
    subst hNM
    exact hM ψ hψ
  · exact
      Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_satisfies
        (Base := Base) (Const := WithParams Const) M φ (hM φ hφ)

end Mettapedia.Logic.PLNWorldModelHOLCompleteness
