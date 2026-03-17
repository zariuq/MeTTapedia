import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.HOL.Semantics.SetBased
import Mettapedia.Logic.PLNWorldModelCrispSpecialization
import Mettapedia.Logic.PLNWorldModelFOL
import Mettapedia.Logic.PLNWorldModelSetTheoryBridge

/-!
# Set-Semantics -> HOL -> WM Bridge

This module packages the direct set-based HOL grounding into a public WM-facing
bridge.

Low-level architecture:

- `SetStructure M -> HOL` lives in `HOL/Semantics/SetBased.lean`
- the present file keeps the same pointed set structures used by the existing
  set-theory WM bridge
- and interprets genuine closed HOL queries over them via the direct HOL model
  induced by each pointed set structure.

This makes the comparison with the older `Set -> FOL -> WM` route completely
explicit on the very same states.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLSetBridge

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

abbrev SetLang := ℒₛₑₜ
abbrev SetTheory := Theory SetLang
abbrev SetPointed := SmallStruc SetLang
abbrev SetState := Multiset SetPointed

abbrev SetBaseTy := Mettapedia.Logic.HOL.Semantics.SetBased.SetBaseTy
abbrev SetConst := Mettapedia.Logic.HOL.Semantics.SetBased.SetConst
abbrev SetHOLQuery := Mettapedia.Logic.HOL.Semantics.SetBased.SetHOLQuery
abbrev SetHOLModel := Mettapedia.Logic.HOL.Semantics.SetBased.SetHOLModel

/-- Closed-formula HOL satisfaction over a pointed set structure, interpreted by
the directly induced set-based HOL model. -/
def setHolSatisfies (S : SetPointed) (φ : SetHOLQuery) : Prop :=
  ((Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S).denote φ (fun v => nomatch v)).down

instance : EvidenceType SetState where

/-- BinaryEvidence extracted from a multiset of pointed set structures, using the
directly induced HOL semantics. -/
noncomputable def setHolEvidence
    (W : SetState) (φ : SetHOLQuery) : BinaryEvidence := by
  classical
  exact
    ⟨(Multiset.countP (fun S => setHolSatisfies S φ) W : ℝ≥0∞),
     (Multiset.countP (fun S => ¬ setHolSatisfies S φ) W : ℝ≥0∞)⟩

/-- The direct set/HOL bridge is a direct instance of the generic
crisp-specialization evidence extractor. -/
theorem setHolEvidence_eq_crispEvidence
    (W : SetState) (φ : SetHOLQuery) :
    setHolEvidence W φ =
      Mettapedia.Logic.PLNWorldModelCrispSpecialization.crispEvidence
        setHolSatisfies W φ := by
  rfl

theorem setHolEvidence_add
    (W₁ W₂ : SetState) (φ : SetHOLQuery) :
    setHolEvidence (W₁ + W₂) φ =
      setHolEvidence W₁ φ + setHolEvidence W₂ φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [setHolEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]
  · simp [setHolEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

/-- World-model instance induced by direct set-based HOL evidence counting. -/
noncomputable instance : BinaryWorldModel SetState SetHOLQuery where
  evidence := setHolEvidence
  evidence_add := setHolEvidence_add

theorem setHolEvidence_singleton_of_satisfies
    (S : SetPointed) (φ : SetHOLQuery) (h : setHolSatisfies S φ) :
    setHolEvidence ({S} : SetState) φ = ⟨1, 0⟩ := by
  classical
  ext <;> simp [setHolEvidence, ← Multiset.cons_zero, h]

theorem setHolEvidence_singleton_of_not_satisfies
    (S : SetPointed) (φ : SetHOLQuery) (h : ¬ setHolSatisfies S φ) :
    setHolEvidence ({S} : SetState) φ = ⟨0, 1⟩ := by
  classical
  ext <;> simp [setHolEvidence, ← Multiset.cons_zero, h]

theorem queryStrength_singleton_of_satisfies
    (S : SetPointed) (φ : SetHOLQuery) (h : setHolSatisfies S φ) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) φ = 1 := by
  change BinaryEvidence.toStrength (setHolEvidence ({S} : SetState) φ) = 1
  rw [setHolEvidence_singleton_of_satisfies (S := S) (φ := φ) h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

theorem queryStrength_singleton_of_not_satisfies
    (S : SetPointed) (φ : SetHOLQuery) (h : ¬ setHolSatisfies S φ) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) φ = 0 := by
  change BinaryEvidence.toStrength (setHolEvidence ({S} : SetState) φ) = 0
  rw [setHolEvidence_singleton_of_not_satisfies (S := S) (φ := φ) h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

/-- Singleton adequacy for the direct set-based HOL semantics. -/
theorem singleton_adequacy_strength_one
    (S : SetPointed) (φ : SetHOLQuery) :
    setHolSatisfies S φ ↔
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) φ = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies (S := S) (φ := φ) h
  · intro h
    by_cases hs : setHolSatisfies S φ
    · exact hs
    · have h0 :
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState) φ = 0 :=
        queryStrength_singleton_of_not_satisfies (S := S) (φ := φ) hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
                ({S} : SetState) φ := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-- Explicit witness that the singleton adequacy theorem for the direct
set/HOL bridge is an instance of the generic crisp-specialization theorem
family. -/
theorem singleton_adequacy_strength_one_is_crispSpecialization
    (S : SetPointed) (φ : SetHOLQuery) :
    setHolSatisfies S φ ↔
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) φ = 1 := by
  simpa [Mettapedia.Logic.PLNWorldModelCrispSpecialization.crispQueryStrength,
    BinaryWorldModel.queryStrength, setHolEvidence_eq_crispEvidence]
    using
      (Mettapedia.Logic.PLNWorldModelCrispSpecialization.singleton_adequacy_strength_one
        (satisfies := setHolSatisfies) S φ)

/-- Pointwise implication over directly grounded HOL queries is equivalent to
singleton-strength consequence on pointed set structures. -/
theorem pointwiseImplies_iff_singletonStrengthLE
    (φ ψ : SetHOLQuery) :
    (∀ S : SetPointed, setHolSatisfies S φ → setHolSatisfies S ψ) ↔
      (∀ S : SetPointed,
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState) ψ) := by
  constructor
  · intro himp S
    by_cases hφ : setHolSatisfies S φ
    · have hψ : setHolSatisfies S ψ := himp S hφ
      rw [queryStrength_singleton_of_satisfies (S := S) (φ := φ) hφ]
      rw [queryStrength_singleton_of_satisfies (S := S) (φ := ψ) hψ]
    · rw [queryStrength_singleton_of_not_satisfies (S := S) (φ := φ) hφ]
      exact zero_le _
  · intro hle S hφ
    by_contra hψ
    have hsingleton := hle S
    have h1 :
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState) φ = 1 :=
      queryStrength_singleton_of_satisfies (S := S) (φ := φ) hφ
    have h0 :
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies (S := S) (φ := ψ) hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      rw [h1, h0] at htmp
      exact htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

/-- Pointwise semantic equivalence yields direct set/HOL world-model query
equivalence. -/
theorem queryEq_of_pointwiseIff
    (φ ψ : SetHOLQuery)
    (hiff : ∀ S : SetPointed, setHolSatisfies S φ ↔ setHolSatisfies S ψ) :
    WMQueryEq (State := SetState) (Query := SetHOLQuery) φ ψ := by
  intro W
  classical
  ext <;> simp [BinaryWorldModel.evidence, setHolEvidence, hiff]

/-- Pointwise semantic equivalence yields equality of direct set/HOL query
strengths. -/
theorem queryStrength_eq_of_pointwiseIff
    (W : SetState) (φ ψ : SetHOLQuery)
    (hiff : ∀ S : SetPointed, setHolSatisfies S φ ↔ setHolSatisfies S ψ) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W φ =
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W ψ := by
  exact
    WMQueryEq.to_queryStrength
      (State := SetState) (Query := SetHOLQuery)
      (queryEq_of_pointwiseIff (φ := φ) (ψ := ψ) hiff) W

private theorem countP_le_countP_of_imp
    (W : SetState)
    {p q : SetPointed → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ S, p S → q S) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      by_cases hp : p a
      · have hq : q a := himp a hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ ih
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans ih (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq]
            using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih

private theorem setHolEvidence_total
    (W : SetState) (φ : SetHOLQuery) :
    (setHolEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun S : SetPointed => setHolSatisfies S φ) W +
          Multiset.countP (fun S : SetPointed => ¬ setHolSatisfies S φ) W := by
    simpa using
      (Multiset.card_eq_countP_add_countP
        (p := fun S : SetPointed => setHolSatisfies S φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun S : SetPointed => setHolSatisfies S φ) W : ℝ≥0∞) +
          (Multiset.countP (fun S : SetPointed => ¬ setHolSatisfies S φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold setHolEvidence BinaryEvidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to multiset WM consequence for the
directly grounded set-based HOL semantics. -/
theorem queryStrength_le_of_pointwise
    (W : SetState) (φ ψ : SetHOLQuery)
    (himp : ∀ S : SetPointed, setHolSatisfies S φ → setHolSatisfies S ψ) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W ψ := by
  let pφ : SetPointed → Prop := fun S => setHolSatisfies S φ
  let pψ : SetPointed → Prop := fun S => setHolSatisfies S ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
    change (if (setHolEvidence W φ).total = 0 then 0
      else (setHolEvidence W φ).pos / (setHolEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [setHolEvidence_total (W := W) (φ := φ)]
    simp [setHolEvidence, pφ]
  have hψ :
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
    change (if (setHolEvidence W ψ).total = 0 then 0
      else (setHolEvidence W ψ).pos / (setHolEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [setHolEvidence_total (W := W) (φ := ψ)]
    simp [setHolEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp (W := W) (p := pφ) (q := pψ) (by
        intro S hp
        exact himp S (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from singleton-strength assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLE
    (W : SetState) (φ ψ : SetHOLQuery)
    (hsing : ∀ S : SetPointed,
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
          ({S} : SetState) φ ≤
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
          ({S} : SetState) ψ) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W ψ := by
  have himp : ∀ S : SetPointed, setHolSatisfies S φ → setHolSatisfies S ψ :=
    (pointwiseImplies_iff_singletonStrengthLE (φ := φ) (ψ := ψ)).2 hsing
  exact queryStrength_le_of_pointwise (W := W) (φ := φ) (ψ := ψ) himp

/-- Pointwise semantic equivalence is exactly direct set/HOL world-model query
equivalence. -/
theorem pointwiseIff_iff_queryEq
    (φ ψ : SetHOLQuery) :
    (∀ S : SetPointed, setHolSatisfies S φ ↔ setHolSatisfies S ψ) ↔
      WMQueryEq (State := SetState) (Query := SetHOLQuery) φ ψ := by
  constructor
  · intro hiff
    exact queryEq_of_pointwiseIff (φ := φ) (ψ := ψ) hiff
  · intro hEq S
    have hStrength :=
      WMQueryEq.to_queryStrength
        (State := SetState) (Query := SetHOLQuery) hEq ({S} : SetState)
    constructor
    · intro hφ
      have hleft :
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
              ({S} : SetState) φ = 1 :=
        queryStrength_singleton_of_satisfies (S := S) (φ := φ) hφ
      rw [hleft] at hStrength
      exact (singleton_adequacy_strength_one (S := S) (φ := ψ)).2 hStrength.symm
    · intro hψ
      have hright :
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
              ({S} : SetState) ψ = 1 :=
        queryStrength_singleton_of_satisfies (S := S) (φ := ψ) hψ
      rw [hright] at hStrength
      exact (singleton_adequacy_strength_one (S := S) (φ := φ)).2 hStrength

/-- Explicit witness that the pointwise-iff/query-equivalence theorem for the
direct set/HOL bridge is an instance of the generic crisp-specialization
equivalence theorem family. -/
theorem pointwiseIff_iff_queryEq_is_crispSpecialization
    (φ ψ : SetHOLQuery) :
    (∀ S : SetPointed, setHolSatisfies S φ ↔ setHolSatisfies S ψ) ↔
      Mettapedia.Logic.PLNWorldModelCrispSpecialization.CrispQueryEq
        setHolSatisfies φ ψ := by
  simpa using
    (Mettapedia.Logic.PLNWorldModelCrispSpecialization.pointwiseIff_iff_queryEq
      (satisfies := setHolSatisfies) φ ψ)

/-! ## Comparison with the existing FOL-routed set bridge -/

abbrev SetQuery := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetQuery

abbrev stateModelsTheory (T : SetTheory) (W : SetState) : Prop :=
  Mettapedia.Logic.PLNWorldModelSetTheoryBridge.stateModelsTheory T W

private theorem setHolSatisfies_embedSentence_iff_of_mutual_consequence
    (T : SetTheory) (S : SetPointed)
    (hT : S ⊧* T)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hφψ : T ⊨[SmallStruc SetLang] (φ ➝ ψ))
    (hψφ : T ⊨[SmallStruc SetLang] (ψ ➝ φ)) :
    setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
      setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  have hleφψ :=
    (Mettapedia.Logic.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
      (T := T) (φ := φ) (ψ := ψ)).1 hφψ S hT
  have hleψφ :=
    (Mettapedia.Logic.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
      (T := T) (φ := ψ) (ψ := φ)).1 hψφ S hT
  have himpφψ :=
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.singletonStrengthLE_singleton_iff_imp
      (S := S) (φ := φ) (ψ := ψ)).1 hleφψ
  have himpψφ :=
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.singletonStrengthLE_singleton_iff_imp
      (S := S) (φ := ψ) (ψ := φ)).1 hleψφ
  rw [show setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
      Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S φ by
        simpa [setHolSatisfies, Mettapedia.Logic.PLNWorldModelFOL.folSatisfies] using
          (Mettapedia.Logic.HOL.Semantics.SetBased.pointed_denote_embedSentence_iff
            (S := S) (φ := φ))]
  rw [show setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) ↔
      Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S ψ by
        simpa [setHolSatisfies, Mettapedia.Logic.PLNWorldModelFOL.folSatisfies] using
          (Mettapedia.Logic.HOL.Semantics.SetBased.pointed_denote_embedSentence_iff
            (S := S) (φ := ψ))]
  exact ⟨himpφψ, himpψφ⟩

/-- On embedded set-theory sentences, the direct HOL interpretation agrees
pointwise with the existing set-theory/FOL satisfaction relation. -/
theorem setHolSatisfies_embedSentence_iff
    (S : SetPointed) (φ : LO.FirstOrder.Sentence SetLang) :
    setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
      Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S φ := by
  simpa [setHolSatisfies, Mettapedia.Logic.PLNWorldModelFOL.folSatisfies] using
    (Mettapedia.Logic.HOL.Semantics.SetBased.pointed_denote_embedSentence_iff
      (S := S) (φ := φ))

/-- BinaryEvidence for embedded set-theory sentences agrees exactly between the direct
`Set -> HOL -> WM` route and the older `Set -> FOL -> WM` route. -/
theorem setHolEvidence_embedSentence_eq_folEvidence
    (W : SetState) (φ : LO.FirstOrder.Sentence SetLang) :
    setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      Mettapedia.Logic.PLNWorldModelFOL.folEvidence W φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [setHolEvidence, Mettapedia.Logic.PLNWorldModelFOL.folEvidence,
      setHolSatisfies_embedSentence_iff]
  · simp [setHolEvidence, Mettapedia.Logic.PLNWorldModelFOL.folEvidence,
      setHolSatisfies_embedSentence_iff]

/-- On theory-model states, mutually implied embedded set-theory sentences yield
identical direct HOL-routed WM evidence. This is the set/HOL rewrite-style
endpoint corresponding to theory-restricted semantic equivalence. -/
theorem setHolEvidence_eq_of_mutual_consequence_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : stateModelsTheory T W)
    (hφψ : T ⊨[SmallStruc SetLang] (φ ➝ ψ))
    (hψφ : T ⊨[SmallStruc SetLang] (ψ ➝ φ)) :
    setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  classical
  have hiff :
      ∀ S ∈ W,
        setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ↔
          setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
    intro S hS
    exact setHolSatisfies_embedSentence_iff_of_mutual_consequence
      (T := T) (S := S) (hT := hW S hS) (φ := φ) (ψ := ψ) hφψ hψφ
  have hpos :
      Multiset.countP
          (fun S => setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ))
          W =
        Multiset.countP
          (fun S => setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ))
          W := by
    refine Multiset.countP_congr rfl ?_
    intro S hS
    exact propext (hiff S hS)
  have hneg :
      Multiset.countP
          (fun S => ¬ setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ))
          W =
        Multiset.countP
          (fun S => ¬ setHolSatisfies S (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ))
          W := by
    refine Multiset.countP_congr rfl ?_
    intro S hS
    exact propext (not_congr (hiff S hS))
  apply BinaryEvidence.ext'
  · simpa [setHolEvidence] using congrArg (fun n : Nat => (n : ℝ≥0∞)) hpos
  · simpa [setHolEvidence] using congrArg (fun n : Nat => (n : ℝ≥0∞)) hneg

/-- On theory-model states, mutually provable implications between embedded
set-theory sentences yield identical direct HOL-routed WM evidence. -/
theorem setHolEvidence_eq_of_mutual_provable_imp_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : stateModelsTheory T W)
    (hφψ : T ⊢ (φ ➝ ψ))
    (hψφ : T ⊢ (ψ ➝ φ)) :
    setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  exact setHolEvidence_eq_of_mutual_consequence_embed
    (T := T) (W := W) (φ := φ) (ψ := ψ) hW (smallSound! hφψ) (smallSound! hψφ)

/-- Query strengths for embedded set-theory sentences agree exactly between the
direct HOL-routed bridge and the older FOL-routed bridge. -/
theorem queryStrength_embedSentence_eq_setQueryStrength
    (W : SetState) (φ : LO.FirstOrder.Sentence SetLang) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetState)
        (Query := SetQuery) W φ := by
  change
    BinaryEvidence.toStrength
      (setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ)) =
    BinaryEvidence.toStrength (Mettapedia.Logic.PLNWorldModelFOL.folEvidence W φ)
  exact congrArg BinaryEvidence.toStrength
    (setHolEvidence_embedSentence_eq_folEvidence (W := W) (φ := φ))

/-- On theory-model states, mutually implied embedded set-theory sentences have
equal direct HOL-routed WM strengths. -/
theorem queryStrength_eq_of_mutual_consequence_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : stateModelsTheory T W)
    (hφψ : T ⊨[SmallStruc SetLang] (φ ➝ ψ))
    (hψφ : T ⊨[SmallStruc SetLang] (ψ ➝ φ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  change BinaryEvidence.toStrength
      (setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ)) =
    BinaryEvidence.toStrength
      (setHolEvidence W (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ))
  exact congrArg BinaryEvidence.toStrength <|
    setHolEvidence_eq_of_mutual_consequence_embed
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hφψ hψφ

/-- On theory-model states, mutually provable implications between embedded
set-theory sentences have equal direct HOL-routed WM strengths. -/
theorem queryStrength_eq_of_mutual_provable_imp_embed
    (T : SetTheory) (W : SetState)
    (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : stateModelsTheory T W)
    (hφψ : T ⊢ (φ ➝ ψ))
    (hψφ : T ⊢ (ψ ➝ φ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) =
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  exact queryStrength_eq_of_mutual_consequence_embed
    (T := T) (W := W) (φ := φ) (ψ := ψ) hW (smallSound! hφψ) (smallSound! hψφ)

/-- Model-restricted singleton HOL consequence for embedded set-theory
sentences is equivalent to Foundation semantic consequence. -/
theorem consequence_iff_singletonStrengthLEOnTheory_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang) :
    T ⊨[SmallStruc SetLang] (φ ➝ ψ) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  constructor
  · intro hcons S hT
    have hle :=
      (Mettapedia.Logic.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
        (T := T) (φ := φ) (ψ := ψ)).1 hcons S hT
    simpa [queryStrength_embedSentence_eq_setQueryStrength
      (W := ({S} : SetState))] using hle
  · intro hhol
    have hfol :
        ∀ S : SetPointed, S ⊧* T →
          BinaryWorldModel.queryStrength
              (State := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetState)
              (Query := SetQuery)
              ({S} : SetState) φ ≤
            BinaryWorldModel.queryStrength
              (State := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetState)
              (Query := SetQuery)
              ({S} : SetState) ψ := by
      intro S hT
      have h := hhol S hT
      simpa [queryStrength_embedSentence_eq_setQueryStrength
        (W := ({S} : SetState))] using h
    exact
      (Mettapedia.Logic.PLNWorldModelSetTheoryBridge.consequence_iff_all_model_singleton_strength
        (T := T) (φ := φ) (ψ := ψ)).2 hfol

/-- Model-restricted singleton HOL consequence for embedded set-theory
sentences is equivalent to Foundation provability. -/
theorem provable_imp_iff_singletonStrengthLEOnTheory_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang) :
    (T ⊢ (φ ➝ ψ)) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
            ({S} : SetState)
            (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  constructor
  · intro hprov
    exact
      (consequence_iff_singletonStrengthLEOnTheory_embed (T := T) (φ := φ) (ψ := ψ)).1
        (smallSound! hprov)
  · intro hhol
    exact
      FirstOrder.complete
        ((consequence_iff_singletonStrengthLEOnTheory_embed
          (T := T) (φ := φ) (ψ := ψ)).2 hhol)

/-- On theory-model states, Foundation semantic consequence transports through
the direct HOL-routed set bridge to multiset WM strength inequality. -/
theorem multiset_strength_le_of_consequence_embed
    (T : SetTheory) (W : SetState) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : stateModelsTheory T W)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := φ)]
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := ψ)]
  exact
    Mettapedia.Logic.PLNWorldModelSetTheoryBridge.multiset_strength_le_of_consequence
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons

/-- On theory-model states, Foundation provability transports through the
direct HOL-routed set bridge to multiset WM strength inequality. -/
theorem multiset_strength_le_of_provable_imp_embed
    (T : SetTheory) (W : SetState) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ) := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := φ)]
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := W) (φ := ψ)]
  exact
    Mettapedia.Logic.PLNWorldModelSetTheoryBridge.multiset_strength_le_of_provable_imp
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov

/-- Public state-indexed WM consequence rule induced by Foundation semantic
consequence, but presented on embedded HOL queries over pointed set structures. -/
def wmConsequenceRuleOn_of_consequence_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetHOLQuery where
  side := stateModelsTheory T
  premise := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ
  conclusion := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ
  sound := by
    intro W hW
    exact multiset_strength_le_of_consequence_embed
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons

/-- Public state-indexed WM consequence rule induced by Foundation provability,
presented on embedded HOL queries over pointed set structures. -/
def wmConsequenceRuleOn_of_provable_imp_embed
    (T : SetTheory) (φ ψ : LO.FirstOrder.Sentence SetLang)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetHOLQuery where
  side := stateModelsTheory T
  premise := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence φ
  conclusion := Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence ψ
  sound := by
    intro W hW
    exact multiset_strength_le_of_provable_imp_embed
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov

/-- Positive comparison canary: embedded truth has singleton strength `1` in the
direct HOL-routed set bridge. -/
theorem canary_singleton_embedTruth_strength_one
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState)
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence (⊤ : LO.FirstOrder.Sentence SetLang)) = 1 := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := ({S} : SetState))
    (φ := (⊤ : LO.FirstOrder.Sentence SetLang))]
  exact
    Mettapedia.Logic.PLNWorldModelFOL.queryStrength_singleton_of_satisfies
      (S := S) (φ := (⊤ : LO.FirstOrder.Sentence SetLang)) (by
        simp [Mettapedia.Logic.PLNWorldModelFOL.folSatisfies])

/-- Negative comparison canary: embedded falsity has singleton strength `0` in
the direct HOL-routed set bridge. -/
theorem canary_singleton_embedFalsum_strength_zero
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState)
        (Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence (⊥ : LO.FirstOrder.Sentence SetLang)) = 0 := by
  rw [queryStrength_embedSentence_eq_setQueryStrength (W := ({S} : SetState))
    (φ := (⊥ : LO.FirstOrder.Sentence SetLang))]
  exact
    Mettapedia.Logic.PLNWorldModelFOL.queryStrength_singleton_of_not_satisfies
      (S := S) (φ := (⊥ : LO.FirstOrder.Sentence SetLang)) (by
        simp [Mettapedia.Logic.PLNWorldModelFOL.folSatisfies])

end Mettapedia.Logic.PLNWorldModelHOLSetBridge
