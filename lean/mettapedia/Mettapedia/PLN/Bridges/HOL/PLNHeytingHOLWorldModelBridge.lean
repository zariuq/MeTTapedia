import Mettapedia.Logic.HOL.Semantics.HeytingGeneral
import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
import Mettapedia.PLN.WorldModel.WMReadout

/-!
# WorldModel readout for intuitionistic HOL over Heyting evidence states

The higher-order analogue of the first-order WM bridge
(`PLNWorldModelFOLCompleteness`): pointed states are Heyting-valued
substitutional models carrying a distinguished evidence value, satisfaction is
"the evidence lies below the formula's value", and WM query strength is the
generic crisp specialization over multisets of such states.

The headline readout mirrors the FO surface honestly: EM-free derivability of
an implication over a parameter-free theory coincides with singleton
WM-strength consequence over all theory-modelling Heyting evidence states.
The completeness direction is carried by the Lindenbaum model pointed at the
antecedent itself.  As in the FO bridge, this is an implication-fragment
readout surface, not a further metatheoretic completeness claim.
-/

namespace Mettapedia.PLN.Bridges.HOL.HeytingWorldModel

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HeytingSem
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open scoped ENNReal

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A pointed Heyting-valued model: a Heyting-valued substitutional model of
the EM-free calculus together with a distinguished evidence state. -/
structure PointedHeytingHOL (Base : Type u) (Const : Ty Base → Type v) where
  model : HeytingGeneralModel.{u, v, max u v} Base Const
  state : model.Ω

/-- Satisfaction at a pointed model: the evidence state lies below the
formula's value. -/
def heytingSatisfies (S : PointedHeytingHOL Base Const)
    (φ : ClosedFormula Const) : Prop :=
  S.model.le S.state (S.model.val φ)

/-- A pointed state models a closed theory. -/
def stateModelsTheory (T : ClosedTheorySet Const)
    (S : PointedHeytingHOL Base Const) : Prop :=
  ∀ ψ ∈ T, heytingSatisfies S ψ

/-- Evidence-state soundness: derivability transports any evidence state lying
below all hypotheses to below the conclusion. -/
theorem satisfies_of_provable {T : ClosedTheorySet Const}
    {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T θ)
    (S : PointedHeytingHOL Base Const) (hT : stateModelsTheory T S) :
    heytingSatisfies S θ := by
  rcases h with ⟨Γ, hΓ, d⟩
  have hclosed : ∀ ψ : ClosedFormula Const,
      subst (emptySubst (Base := Base) (Const := Const)) ψ = ψ := fun ψ =>
    KripkeHenkin.ClosedEnv.subst_empty (Base := Base) (Const := Const) _ ψ
  have hhyps : ∀ (Γ' : List (ClosedFormula Const)), (∀ ψ ∈ Γ', ψ ∈ T) →
      S.model.le S.state
        (S.model.hypVal (Γ'.map (subst (emptySubst (Base := Base) (Const := Const))))) := by
    intro Γ'
    induction Γ' with
    | nil => intro _; exact S.model.le_top _
    | cons ψ Γ' ih =>
        intro hmem
        refine S.model.le_inf ?_ (ih (fun ξ hξ => hmem ξ (List.mem_cons_of_mem _ hξ)))
        rw [hclosed ψ]
        exact hT ψ (hmem ψ List.mem_cons_self)
  have hs := HeytingSem.sound d S.model (emptySubst (Base := Base) (Const := Const))
  have hcomb := S.model.le_trans (hhyps Γ hΓ) hs
  unfold heytingSatisfies
  rw [← hclosed θ]
  exact hcomb

/-- Pointwise implication over all theory-modelling evidence states. -/
def pointwiseImpliesOnTheory (T : ClosedTheorySet Const)
    (φ ψ : ClosedFormula Const) : Prop :=
  ∀ S : PointedHeytingHOL Base Const, stateModelsTheory T S →
    heytingSatisfies S φ → heytingSatisfies S ψ

/-- Singleton WM-strength consequence over all theory-modelling evidence
states, via the generic crisp specialization. -/
def singletonStrengthLEOnTheory (T : ClosedTheorySet Const)
    (φ ψ : ClosedFormula Const) : Prop :=
  ∀ S : PointedHeytingHOL Base Const, stateModelsTheory T S →
    crispQueryStrength (heytingSatisfies (Base := Base) (Const := Const))
        ({S} : Multiset (PointedHeytingHOL Base Const)) φ ≤
      crispQueryStrength (heytingSatisfies (Base := Base) (Const := Const))
        ({S} : Multiset (PointedHeytingHOL Base Const)) ψ

/-- Fixed-state singleton WM consequence is satisfaction implication at that
state. -/
theorem singletonStrengthLE_singleton_iff_imp
    (S : PointedHeytingHOL Base Const) (φ ψ : ClosedFormula Const) :
    (crispQueryStrength (heytingSatisfies (Base := Base) (Const := Const))
        ({S} : Multiset (PointedHeytingHOL Base Const)) φ ≤
      crispQueryStrength (heytingSatisfies (Base := Base) (Const := Const))
        ({S} : Multiset (PointedHeytingHOL Base Const)) ψ) ↔
      (heytingSatisfies S φ → heytingSatisfies S ψ) := by
  classical
  constructor
  · intro hle hφ
    by_contra hψ
    rw [queryStrength_singleton_of_satisfies _ S φ hφ,
      queryStrength_singleton_of_not_satisfies _ S ψ hψ] at hle
    exact (not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1)) hle
  · intro himp
    by_cases hφ : heytingSatisfies S φ
    · rw [queryStrength_singleton_of_satisfies _ S φ hφ,
        queryStrength_singleton_of_satisfies _ S ψ (himp hφ)]
    · rw [queryStrength_singleton_of_not_satisfies _ S φ hφ]
      exact zero_le

/-- Pointwise implication and singleton strength consequence coincide. -/
theorem pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
    (T : ClosedTheorySet Const) (φ ψ : ClosedFormula Const) :
    pointwiseImpliesOnTheory (Base := Base) T φ ψ ↔
      singletonStrengthLEOnTheory (Base := Base) T φ ψ := by
  constructor
  · intro h S hS
    exact (singletonStrengthLE_singleton_iff_imp S φ ψ).mpr (h S hS)
  · intro h S hS
    exact (singletonStrengthLE_singleton_iff_imp S φ ψ).mp (h S hS)

/-- **The readout, implication fragment**: over a parameter-free theory,
EM-free derivability of an implication coincides with pointwise implication
over all Heyting evidence states modelling the theory.  Completeness is
carried by the Lindenbaum model pointed at the antecedent. -/
theorem provable_imp_iff_pointwiseImpliesOnTheory
    {T : ClosedTheorySet (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (φ ψ : ClosedFormula (WithParams Const)) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) ↔
      pointwiseImpliesOnTheory (Base := Base) T φ ψ := by
  constructor
  · intro h S hS hφ
    have himp := satisfies_of_provable h S hS
    unfold heytingSatisfies at himp hφ ⊢
    rw [S.model.val_imp] at himp
    exact S.model.le_trans (S.model.le_inf (S.model.le_refl _) hφ)
      (S.model.himp_adjoint_mp himp)
  · intro h
    set M₀ := Lindenbaum.lindenbaumModel (Base := Base) T hT0 with hM₀
    have hpoint := h ⟨M₀, φ⟩
      (fun ψ' hψ' => Lindenbaum.provable_mono (Set.subset_insert _ _)
        (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ'))
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const)
        (Set.mem_insert _ _))
    exact provable_imp_of_insert (Const := WithParams Const) hpoint

/-- **The WM readout surface**: EM-free derivability of an implication over a
parameter-free theory coincides with singleton WM-strength consequence over
all Heyting evidence states modelling the theory — the higher-order,
intuitionistic mirror of the first-order WM bridge surface. -/
theorem provable_imp_iff_singletonStrengthLEOnTheory
    {T : ClosedTheorySet (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (φ ψ : ClosedFormula (WithParams Const)) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) ↔
      singletonStrengthLEOnTheory (Base := Base) T φ ψ :=
  (provable_imp_iff_pointwiseImpliesOnTheory (Base := Base) hT0 φ ψ).trans
    (pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory (Base := Base) T φ ψ)

/-- **The crisp separating readout family**: the theory-modelling pointed
Heyting evidence states, reading formulas to crisp singleton strengths,
jointly separate the derivability order — the completeness theorem packaged
as a `SeparatingWMReadouts` instance (stage one of the support-to-evidence
readout programme). -/
noncomputable def heytingCrispSeparatingReadouts
    (T : ClosedTheorySet (WithParams Const))
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    Mettapedia.PLN.WorldModel.SeparatingWMReadouts
      {S : PointedHeytingHOL Base (WithParams Const) // stateModelsTheory T S}
      (ClosedFormula (WithParams Const)) ℝ≥0∞
      (fun φ ψ => ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ))
      (· ≤ ·) where
  mu S φ := crispQueryStrength
    (heytingSatisfies (Base := Base) (Const := WithParams Const))
    ({S.1} : Multiset (PointedHeytingHOL Base (WithParams Const))) φ
  monotone S {φ ψ} h := by
    refine (singletonStrengthLE_singleton_iff_imp S.1 φ ψ).mpr (fun hφ => ?_)
    have himp := satisfies_of_provable h S.1 S.2
    unfold heytingSatisfies at himp hφ ⊢
    rw [S.1.model.val_imp] at himp
    exact S.1.model.le_trans (S.1.model.le_inf (S.1.model.le_refl _) hφ)
      (S.1.model.himp_adjoint_mp himp)
  separates {φ ψ} h :=
    (provable_imp_iff_singletonStrengthLEOnTheory (Base := Base) hT0 φ ψ).mpr
      (fun S hS => h ⟨S, hS⟩)

end Mettapedia.PLN.Bridges.HOL.HeytingWorldModel
