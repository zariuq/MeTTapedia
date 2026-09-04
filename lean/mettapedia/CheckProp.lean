import Mettapedia.Logic.ModalQuantaleSemantics
import Mathlib.Data.Set.Card
import Mathlib.Order.Iterate

open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalQuantaleSemantics

namespace Scratch

#check Function.iterate_succ_apply
#check Function.iterate_succ_apply'
#check Set.eq_of_subset_of_ncard_le

theorem monotone_set_chain_stabilizes_at_card [Finite S]
    (chain : Nat → Set S) (monotone : Monotone chain)
    (stable : ∀ index,
      chain index = chain (index + 1) →
        chain (index + 1) = chain (index + 2)) :
    chain (Nat.card S) = chain (Nat.card S + 1) := by
  have cardinalityMonotone : Monotone fun index => (chain index).ncard := by
    intro left right ordered
    exact Set.ncard_le_ncard (monotone ordered) (Set.toFinite _)
  have cardinalityBound : ∀ index, (chain index).ncard ≤ Nat.card S := by
    intro index
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (by intro _ _; trivial) (Set.toFinite _)
  have cardinalityStable : ∀ index,
      (chain index).ncard = (chain (index + 1)).ncard →
        (chain (index + 1)).ncard = (chain (index + 2)).ncard := by
    intro index equalCardinality
    have equalSets : chain index = chain (index + 1) :=
      Set.eq_of_subset_of_ncard_le (monotone (by omega))
        (by omega) (Set.toFinite _)
    exact congrArg Set.ncard (stable index equalSets)
  have equalCardinality := Nat.stabilises_of_monotone
    cardinalityMonotone cardinalityBound cardinalityStable
    (show Nat.card S ≤ Nat.card S + 1 by omega)
  exact Set.eq_of_subset_of_ncard_le (monotone (by omega))
    (by omega) (Set.toFinite _)

theorem orderHom_lfp_eq_iterate_empty [Finite S]
    (transformer : Set S →o Set S) :
    transformer.lfp =
      (transformer : Set S → Set S)^[Nat.card S] (∅ : Set S) := by
  let approximation : Nat → Set S := fun index =>
    (transformer : Set S → Set S)^[index] (∅ : Set S)
  have approximationMonotone : Monotone approximation :=
    transformer.monotone.monotone_iterate_of_le_map bot_le
  have approximationStable : ∀ index,
      approximation index = approximation (index + 1) →
        approximation (index + 1) = approximation (index + 2) := by
    intro index equal
    simpa [approximation, Function.iterate_succ_apply'] using
      congrArg transformer equal
  have stabilized := monotone_set_chain_stabilizes_at_card
    approximation approximationMonotone approximationStable
  have fixed : transformer (approximation (Nat.card S)) =
      approximation (Nat.card S) := by
    simpa [approximation, Function.iterate_succ_apply'] using stabilized.symm
  have approximationLe : ∀ index, approximation index ≤ transformer.lfp := by
    intro index
    induction index with
    | zero => exact bot_le
    | succ index inductionHypothesis =>
        simpa only [approximation, Function.iterate_succ_apply'] using
          (transformer.monotone inductionHypothesis).trans_eq
            transformer.map_lfp
  exact le_antisymm (transformer.lfp_le_fixed fixed)
    (by simpa [approximation] using approximationLe (Nat.card S))

theorem antitone_set_chain_stabilizes_at_card [Finite S]
    (chain : Nat → Set S) (antitone : Antitone chain)
    (stable : ∀ index,
      chain index = chain (index + 1) →
        chain (index + 1) = chain (index + 2)) :
    chain (Nat.card S) = chain (Nat.card S + 1) := by
  let complementChain : Nat → Set S := fun index => (chain index)ᶜ
  have complementMonotone : Monotone complementChain := by
    intro left right ordered
    exact Set.compl_subset_compl.mpr (antitone ordered)
  have complementStable : ∀ index,
      complementChain index = complementChain (index + 1) →
        complementChain (index + 1) = complementChain (index + 2) := by
    intro index equalComplements
    exact congrArg (fun states : Set S => statesᶜ)
      (stable index (compl_inj_iff.mp equalComplements))
  exact compl_inj_iff.mp (monotone_set_chain_stabilizes_at_card
    complementChain complementMonotone complementStable)

theorem orderHom_gfp_eq_iterate_univ [Finite S]
    (transformer : Set S →o Set S) :
    transformer.gfp =
      (transformer : Set S → Set S)^[Nat.card S] (Set.univ : Set S) := by
  let approximation : Nat → Set S := fun index =>
    (transformer : Set S → Set S)^[index] (Set.univ : Set S)
  have approximationAntitone : Antitone approximation :=
    transformer.monotone.antitone_iterate_of_map_le le_top
  have approximationStable : ∀ index,
      approximation index = approximation (index + 1) →
        approximation (index + 1) = approximation (index + 2) := by
    intro index equal
    simpa [approximation, Function.iterate_succ_apply'] using
      congrArg transformer equal
  have stabilized := antitone_set_chain_stabilizes_at_card
    approximation approximationAntitone approximationStable
  have fixed : transformer (approximation (Nat.card S)) =
      approximation (Nat.card S) := by
    simpa [approximation, Function.iterate_succ_apply'] using stabilized.symm
  have approximationGe : ∀ index, transformer.gfp ≤ approximation index := by
    intro index
    induction index with
    | zero => exact le_top
    | succ index inductionHypothesis =>
        simpa only [approximation, Function.iterate_succ_apply'] using
          transformer.map_gfp.symm.le.trans
            (transformer.monotone inductionHypothesis)
  exact le_antisymm
    (by simpa [approximation] using approximationGe (Nat.card S))
    (transformer.le_gfp fixed.ge)

local instance : Mul Prop where
  mul := And

local instance : CommSemigroup Prop where
  mul_assoc := fun _ _ _ => propext and_assoc
  mul_comm := fun _ _ => propext and_comm

local instance : IsCommQuantale Prop :=
  IsCommQuantale.ofCommSemigroup (by
    intro proposition propositions
    change (proposition ∧ sSup propositions) =
      iSup (fun y : Prop => iSup fun _ : y ∈ propositions => proposition ∧ y)
    apply propext
    simp)

#synth CompleteLattice Prop
#synth CommSemigroup Prop
#synth IsCommQuantale Prop
#check iSup_Prop_eq
#check iInf_Prop_eq

@[simp] theorem prop_mul_iff (left right : Prop) :
    left * right ↔ left ∧ right := Iff.rfl

theorem prop_leftResiduate_iff (premise conclusion : Prop) :
    leftResiduate premise conclusion ↔ (premise → conclusion) := by
  constructor
  · intro residuated premiseProof
    exact modusPonens_left premise conclusion ⟨residuated, premiseProof⟩
  · intro implication
    exact (residuate_galois premise conclusion (premise → conclusion)).mp
      (fun conjunction => implication conjunction.2) implication

def truthQLTS (lts : LTS S Act) : QLTS Prop S Act where
  trans := lts.trans

theorem qSatisfies_truth_iff (lts : LTS S Act) (ρ : Env S n)
    (formula : Formula Act n) (state : S) :
    qSatisfies (truthQLTS lts) ρ formula state ↔
      satisfies lts ρ formula state := by
  induction formula generalizing state with
  | tt => rfl
  | ff => rfl
  | neg formula inductionHypothesis =>
      simp only [qSatisfies, satisfies, prop_leftResiduate_iff]
      exact not_congr (inductionHypothesis ρ state)
  | conj left right leftHypothesis rightHypothesis =>
      simp only [qSatisfies, satisfies]
      exact and_congr (leftHypothesis ρ state) (rightHypothesis ρ state)
  | disj left right leftHypothesis rightHypothesis =>
      simp only [qSatisfies, satisfies]
      exact or_congr (leftHypothesis ρ state) (rightHypothesis ρ state)
  | diamond action formula inductionHypothesis =>
      simp only [qSatisfies, satisfies, truthQLTS, LTS.successors,
        Set.mem_setOf_eq, prop_mul_iff, iSup_Prop_eq]
      exact exists_congr fun target =>
        and_congr Iff.rfl (inductionHypothesis ρ target)
  | box action formula inductionHypothesis =>
      simp only [qSatisfies, satisfies, truthQLTS, LTS.successors,
        Set.mem_setOf_eq, prop_leftResiduate_iff, iInf_Prop_eq]
      exact forall_congr' fun target =>
        imp_congr Iff.rfl (inductionHypothesis ρ target)
  | mu body inductionHypothesis =>
      simp only [qSatisfies, satisfies, iInf_Prop_eq]
      constructor
      · intro least candidate preFixed
        exact least candidate (fun target satisfied =>
          preFixed target
            ((inductionHypothesis (ρ.extend candidate) target).mp satisfied))
      · intro least candidate preFixed
        exact least candidate (fun target satisfied =>
          preFixed target
            ((inductionHypothesis (ρ.extend candidate) target).mpr satisfied))
  | nu body inductionHypothesis =>
      simp only [qSatisfies, satisfies, iSup_Prop_eq]
      constructor
      · rintro ⟨candidate, postFixed, member⟩
        exact ⟨candidate, member, fun target targetMember =>
          (inductionHypothesis (ρ.extend candidate) target).mp
            (postFixed target targetMember)⟩
      · rintro ⟨candidate, member, postFixed⟩
        exact ⟨candidate, (fun target targetMember =>
          (inductionHypothesis (ρ.extend candidate) target).mpr
            (postFixed target targetMember)), member⟩
  | var index => rfl

theorem satisfies_mono_env (lts : LTS S Act) {n : Nat}
    (formula : Formula Act n) (index : Fin n) (polarity : Bool)
    (positive : formula.isPositiveIn index polarity = true) :
    ∀ (left right : Env S n),
      (∀ other state, other ≠ index → left other state = right other state) →
      (∀ state, left index state → right index state) →
      ∀ state, if polarity then satisfies lts left formula state →
        satisfies lts right formula state else
        satisfies lts right formula state → satisfies lts left formula state := by
  intro left right agree inclusion state
  have quantaleMonotonicity := qSatisfies_mono_env
    (truthQLTS lts) formula index polarity positive left right agree inclusion state
  cases polarity with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at quantaleMonotonicity ⊢
      intro satisfied
      exact (qSatisfies_truth_iff lts left formula state).mp
        (quantaleMonotonicity
          ((qSatisfies_truth_iff lts right formula state).mpr satisfied))
  | true =>
      simp only [↓reduceIte] at quantaleMonotonicity ⊢
      intro satisfied
      exact (qSatisfies_truth_iff lts right formula state).mp
        (quantaleMonotonicity
          ((qSatisfies_truth_iff lts left formula state).mpr satisfied))

noncomputable def bodyOrderHom (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true) :
    Set S →o Set S where
  toFun candidate := sat lts (ρ.extend candidate) body
  monotone' := by
    intro left right inclusion state satisfied
    exact satisfies_mono_env lts body 0 true positive
      (ρ.extend left) (ρ.extend right)
      (by
        intro index state indexNotZero
        unfold Env.extend
        split
        · exfalso
          exact indexNotZero (Fin.ext ‹_›)
        · rfl)
      (by
        intro state member
        exact inclusion member)
      state satisfied

theorem satisfies_mu_iff_mem_lfp (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.mu body) state ↔
      state ∈ (bodyOrderHom lts ρ body positive).lfp := by
  let transformer := bodyOrderHom lts ρ body positive
  constructor
  · intro least
    apply least transformer.lfp
    intro target satisfied
    exact transformer.map_le_lfp le_rfl satisfied
  · intro member candidate preFixed
    exact transformer.lfp_le preFixed member

theorem satisfies_nu_iff_mem_gfp (lts : LTS S Act) (ρ : Env S n)
    (body : Formula Act (n + 1)) (positive : body.isPositive = true)
    (state : S) :
    satisfies lts ρ (.nu body) state ↔
      state ∈ (bodyOrderHom lts ρ body positive).gfp := by
  let transformer := bodyOrderHom lts ρ body positive
  constructor
  · rintro ⟨candidate, member, postFixed⟩
    exact transformer.le_gfp postFixed member
  · intro member
    exact ⟨transformer.gfp, member,
      fun target targetMember => transformer.gfp_le_map le_rfl targetMember⟩

end Scratch
