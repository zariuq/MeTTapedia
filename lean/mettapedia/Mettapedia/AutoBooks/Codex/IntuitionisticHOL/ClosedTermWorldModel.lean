import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermQuotient
import Mettapedia.Logic.PLNWorldModel

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
World-model evidence for canonical closed-term worlds.

The semantic endpoint here is intentionally syntactic: a state is a multiset of
canonical `ClosedTheorySet.World`s, and a query is a closed HOL formula.  A
world supports a query exactly when the query belongs to its saturated carrier.
This gives the closed-term truth lemma an immediate singleton-strength reading:
membership/truth has strength `1`, while omission has strength `0`.
-/

namespace ClosedTermCanonicalWorldModel

/-- Closed formulas are the queries asked of canonical closed-term worlds. -/
abbrev CanonicalQuery (Const : Ty Base → Type v) := ClosedFormula Const

/-- A canonical world satisfies a closed query when the query belongs to its
closed saturated carrier. -/
def canonicalWorldSatisfies
    (W : ClosedTheorySet.World Const) (φ : CanonicalQuery Const) : Prop :=
  φ ∈ W.carrier

instance : EvidenceType (Multiset (ClosedTheorySet.World Const)) where

/-- Binary evidence extracted from a multiset of canonical worlds.  Positive
evidence counts worlds containing the query; negative evidence counts worlds
omitting it. -/
noncomputable def canonicalWorldEvidence
    (Ω : Multiset (ClosedTheorySet.World Const))
    (φ : CanonicalQuery Const) : BinaryEvidence := by
  classical
  exact
    ⟨(Multiset.countP (fun W => canonicalWorldSatisfies W φ) Ω : ℝ≥0∞),
     (Multiset.countP (fun W => ¬ canonicalWorldSatisfies W φ) Ω : ℝ≥0∞)⟩

theorem canonicalWorldEvidence_add
    (Ω₁ Ω₂ : Multiset (ClosedTheorySet.World Const))
    (φ : CanonicalQuery Const) :
    canonicalWorldEvidence (Base := Base) (Const := Const) (Ω₁ + Ω₂) φ =
      canonicalWorldEvidence (Base := Base) (Const := Const) Ω₁ φ +
        canonicalWorldEvidence (Base := Base) (Const := Const) Ω₂ φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [canonicalWorldEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]
  · simp [canonicalWorldEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

/-- The binary world-model instance induced by canonical-world membership
counting. -/
noncomputable instance :
    BinaryWorldModel
      (Multiset (ClosedTheorySet.World Const))
      (CanonicalQuery Const) where
  evidence := canonicalWorldEvidence (Base := Base) (Const := Const)
  evidence_add := canonicalWorldEvidence_add (Base := Base) (Const := Const)
  evidence_zero := by
    intro φ
    classical
    simp only [canonicalWorldEvidence, Multiset.countP_zero, Nat.cast_zero]
    rfl

theorem canonicalWorldEvidence_singleton_of_satisfies
    (W : ClosedTheorySet.World Const) (φ : CanonicalQuery Const)
    (h : canonicalWorldSatisfies W φ) :
    canonicalWorldEvidence (Base := Base) (Const := Const)
      ({W} : Multiset (ClosedTheorySet.World Const)) φ = ⟨1, 0⟩ := by
  classical
  apply BinaryEvidence.ext'
  · have hp :
        Multiset.countP (fun V : ClosedTheorySet.World Const =>
            canonicalWorldSatisfies V φ)
          ({W} : Multiset (ClosedTheorySet.World Const)) = 1 := by
      simpa using
        (Multiset.countP_cons_of_pos
          (p := fun V : ClosedTheorySet.World Const =>
            canonicalWorldSatisfies V φ)
          (s := (0 : Multiset (ClosedTheorySet.World Const))) h)
    simp [canonicalWorldEvidence, hp]
  · have hn :
        Multiset.countP (fun V : ClosedTheorySet.World Const =>
            ¬ canonicalWorldSatisfies V φ)
          ({W} : Multiset (ClosedTheorySet.World Const)) = 0 := by
      have hnot : ¬ ¬ canonicalWorldSatisfies W φ := fun hn => hn h
      simpa using
        (Multiset.countP_cons_of_neg
          (p := fun V : ClosedTheorySet.World Const =>
            ¬ canonicalWorldSatisfies V φ)
          (s := (0 : Multiset (ClosedTheorySet.World Const))) hnot)
    simp [canonicalWorldEvidence, hn]

theorem canonicalWorldEvidence_singleton_of_not_satisfies
    (W : ClosedTheorySet.World Const) (φ : CanonicalQuery Const)
    (h : ¬ canonicalWorldSatisfies W φ) :
    canonicalWorldEvidence (Base := Base) (Const := Const)
      ({W} : Multiset (ClosedTheorySet.World Const)) φ = ⟨0, 1⟩ := by
  classical
  apply BinaryEvidence.ext'
  · have hp :
        Multiset.countP (fun V : ClosedTheorySet.World Const =>
            canonicalWorldSatisfies V φ)
          ({W} : Multiset (ClosedTheorySet.World Const)) = 0 := by
      simpa using
        (Multiset.countP_cons_of_neg
          (p := fun V : ClosedTheorySet.World Const =>
            canonicalWorldSatisfies V φ)
          (s := (0 : Multiset (ClosedTheorySet.World Const))) h)
    simp [canonicalWorldEvidence, hp]
  · have hn :
        Multiset.countP (fun V : ClosedTheorySet.World Const =>
            ¬ canonicalWorldSatisfies V φ)
          ({W} : Multiset (ClosedTheorySet.World Const)) = 1 := by
      simpa using
        (Multiset.countP_cons_of_pos
          (p := fun V : ClosedTheorySet.World Const =>
            ¬ canonicalWorldSatisfies V φ)
          (s := (0 : Multiset (ClosedTheorySet.World Const))) h)
    simp [canonicalWorldEvidence, hn]

theorem queryStrength_singleton_of_satisfies
    (W : ClosedTheorySet.World Const) (φ : CanonicalQuery Const)
    (h : canonicalWorldSatisfies W φ) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World Const))
        (Query := CanonicalQuery Const)
        ({W} : Multiset (ClosedTheorySet.World Const)) φ = 1 := by
  change
    BinaryEvidence.toStrength
      (canonicalWorldEvidence (Base := Base) (Const := Const)
        ({W} : Multiset (ClosedTheorySet.World Const)) φ) = 1
  rw [canonicalWorldEvidence_singleton_of_satisfies
    (Base := Base) (Const := Const) W φ h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

theorem queryStrength_singleton_of_not_satisfies
    (W : ClosedTheorySet.World Const) (φ : CanonicalQuery Const)
    (h : ¬ canonicalWorldSatisfies W φ) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World Const))
        (Query := CanonicalQuery Const)
        ({W} : Multiset (ClosedTheorySet.World Const)) φ = 0 := by
  change
    BinaryEvidence.toStrength
      (canonicalWorldEvidence (Base := Base) (Const := Const)
        ({W} : Multiset (ClosedTheorySet.World Const)) φ) = 0
  rw [canonicalWorldEvidence_singleton_of_not_satisfies
    (Base := Base) (Const := Const) W φ h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

/-- Singleton adequacy for canonical closed worlds: membership is exactly query
strength `1`. -/
theorem singleton_adequacy_strength_one
    (W : ClosedTheorySet.World Const) (φ : CanonicalQuery Const) :
    canonicalWorldSatisfies W φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const)) φ = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies
      (Base := Base) (Const := Const) W φ h
  · intro h
    by_cases hs : canonicalWorldSatisfies W φ
    · exact hs
    · have h0 :
          BinaryWorldModel.queryStrength
              (State := Multiset (ClosedTheorySet.World Const))
              (Query := CanonicalQuery Const)
              ({W} : Multiset (ClosedTheorySet.World Const)) φ = 0 :=
        queryStrength_singleton_of_not_satisfies
          (Base := Base) (Const := Const) W φ hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              BinaryWorldModel.queryStrength
                  (State := Multiset (ClosedTheorySet.World Const))
                  (Query := CanonicalQuery Const)
                  ({W} : Multiset (ClosedTheorySet.World Const)) φ := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-- Singleton adequacy for canonical closed worlds: omission is exactly query
strength `0`. -/
theorem singleton_adequacy_strength_zero
    (W : ClosedTheorySet.World Const) (φ : CanonicalQuery Const) :
    ¬ canonicalWorldSatisfies W φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const)) φ = 0 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_not_satisfies
      (Base := Base) (Const := Const) W φ h
  · intro h hs
    have h1 :
        BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World Const))
            (Query := CanonicalQuery Const)
            ({W} : Multiset (ClosedTheorySet.World Const)) φ = 1 :=
      queryStrength_singleton_of_satisfies
        (Base := Base) (Const := Const) W φ hs
    have h10 : (1 : ℝ≥0∞) = 0 := by
      calc
        (1 : ℝ≥0∞) =
            BinaryWorldModel.queryStrength
                (State := Multiset (ClosedTheorySet.World Const))
                (Query := CanonicalQuery Const)
                ({W} : Multiset (ClosedTheorySet.World Const)) φ := h1.symm
        _ = 0 := h
    exact zero_ne_one h10.symm

/-- Closed-term quotient truth in a canonical world has singleton strength `1`
exactly when it is true. -/
theorem propTruth_iff_singleton_strength_one
    (W : ClosedTheorySet.World Const) (φ : ClosedFormula Const) :
    ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf φ) ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const)) φ = 1 := by
  rw [ClosedTermEq.propTruth_world_iff_mem (Const := Const) W φ]
  exact singleton_adequacy_strength_one (Base := Base) (Const := Const) W φ

/-- Failure of closed-term quotient truth in a canonical world has singleton
strength `0`. -/
theorem not_propTruth_iff_singleton_strength_zero
    (W : ClosedTheorySet.World Const) (φ : ClosedFormula Const) :
    ¬ ClosedTermEq.propTruth (T := W.carrier) (ClosedTermEq.classOf φ) ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const)) φ = 0 := by
  rw [ClosedTermEq.propTruth_world_iff_mem (Const := Const) W φ]
  exact singleton_adequacy_strength_zero (Base := Base) (Const := Const) W φ

/-- Open-formula canonical truth under a closed environment has singleton
strength `1` exactly when the closed instance is true in the world. -/
theorem envSatisfies_iff_singleton_strength_one
    (W : ClosedTheorySet.World Const) {Γ : Ctx Base}
    (ρ : ClosedTermEq.ClosedEnv (Base := Base) Const Γ)
    (φ : Formula Const Γ) :
    ClosedTermEq.envSatisfies (Const := Const) W.carrier ρ φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const))
          (ClosedTermEq.closeFormula ρ φ) = 1 := by
  rw [ClosedTermEq.envSatisfies_world_iff_mem (Const := Const) W ρ φ]
  exact singleton_adequacy_strength_one
    (Base := Base) (Const := Const) W (ClosedTermEq.closeFormula ρ φ)

/-- Failure of open-formula canonical truth under a closed environment has
singleton strength `0` for the closed instance. -/
theorem not_envSatisfies_iff_singleton_strength_zero
    (W : ClosedTheorySet.World Const) {Γ : Ctx Base}
    (ρ : ClosedTermEq.ClosedEnv (Base := Base) Const Γ)
    (φ : Formula Const Γ) :
    ¬ ClosedTermEq.envSatisfies (Const := Const) W.carrier ρ φ ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const))
          (ClosedTermEq.closeFormula ρ φ) = 0 := by
  rw [ClosedTermEq.envSatisfies_world_iff_mem (Const := Const) W ρ φ]
  exact singleton_adequacy_strength_zero
    (Base := Base) (Const := Const) W (ClosedTermEq.closeFormula ρ φ)

/-- Pointwise implication between closed canonical queries is equivalent to
singleton-strength preservation across canonical worlds. -/
theorem pointwiseImplies_iff_singletonStrengthLE
    (φ ψ : CanonicalQuery Const) :
    (∀ W : ClosedTheorySet.World Const,
        canonicalWorldSatisfies W φ → canonicalWorldSatisfies W ψ) ↔
      (∀ W : ClosedTheorySet.World Const,
        BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World Const))
            (Query := CanonicalQuery Const)
            ({W} : Multiset (ClosedTheorySet.World Const)) φ ≤
          BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World Const))
            (Query := CanonicalQuery Const)
            ({W} : Multiset (ClosedTheorySet.World Const)) ψ) := by
  constructor
  · intro himp W
    by_cases hφ : canonicalWorldSatisfies W φ
    · have hψ : canonicalWorldSatisfies W ψ := himp W hφ
      rw [queryStrength_singleton_of_satisfies
        (Base := Base) (Const := Const) W φ hφ]
      rw [queryStrength_singleton_of_satisfies
        (Base := Base) (Const := Const) W ψ hψ]
    · rw [queryStrength_singleton_of_not_satisfies
        (Base := Base) (Const := Const) W φ hφ]
      exact zero_le
  · intro hle W hφ
    by_contra hψ
    have hsingleton := hle W
    have h1 :
        BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World Const))
            (Query := CanonicalQuery Const)
            ({W} : Multiset (ClosedTheorySet.World Const)) φ = 1 :=
      queryStrength_singleton_of_satisfies
        (Base := Base) (Const := Const) W φ hφ
    have h0 :
        BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World Const))
            (Query := CanonicalQuery Const)
            ({W} : Multiset (ClosedTheorySet.World Const)) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies
        (Base := Base) (Const := Const) W ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      rw [h1, h0] at hsingleton
      exact hsingleton
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

end ClosedTermCanonicalWorldModel

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
