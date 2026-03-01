import Mettapedia.Logic.PLNInferenceControlAlgorithms

/-!
# Chapter 13 Chainer Interfaces

Typed forward/backward chainer interfaces over the Chapter-13 greedy theorem spine.
These operators expose MeTTa/PeTTa-style step/search entry points while preserving
formal links to the existing coverage and ranking guarantees.
-/

namespace Mettapedia.Logic.PLNInferenceControlChainer

open scoped Classical
open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.PremiseSelectionOptimality
open Mettapedia.Logic.PLNInferenceControlAlgorithms

noncomputable section

section Interfaces

variable {Fact : Type*} [Fintype Fact] [DecidableEq Fact]

/-- Single forward-chaining step: apply `greedyPick?` then insert if available. -/
def forwardStep (D S : Finset Fact) : Finset Fact :=
  match greedyPick? D S with
  | some a => insert a S
  | none => S

theorem forwardStep_eq_insert_or_id (D S : Finset Fact) :
    (∃ a, greedyPick? D S = some a ∧ forwardStep D S = insert a S)
      ∨ (greedyPick? D S = none ∧ forwardStep D S = S) := by
  cases hpick : greedyPick? D S with
  | none =>
      exact Or.inr ⟨rfl, by simp [forwardStep, hpick]⟩
  | some a =>
      exact Or.inl ⟨a, rfl, by simp [forwardStep, hpick]⟩

theorem forwardStep_spec_of_card_lt_univ (D S : Finset Fact)
    (hS : S.card < Fintype.card Fact) :
    ∃ a, greedyPick? D S = some a
      ∧ forwardStep D S = insert a S
      ∧ IsGreedyStep D S a := by
  rcases greedyPick?_isGreedyStep_of_card_lt_univ (D := D) (S := S) hS with
    ⟨a, hpick, hstep⟩
  exact ⟨a, hpick, by simp [forwardStep, hpick], hstep⟩

/-- Forward bounded search from the empty selected set. -/
noncomputable def forwardSearch (D : Finset Fact) (fuel : Nat) : Finset Fact :=
  greedySelect D fuel

theorem forwardSearch_chain_of_le_card (D : Finset Fact) {k : Nat}
    (hk : k ≤ Fintype.card Fact) :
    GreedyChain D k (forwardSearch D k) := by
  simpa [forwardSearch] using greedySelect_chain_of_le_card (D := D) (k := k) hk

theorem forwardSearch_one_minus_exp_bound_of_le_card (D : Finset Fact) {k : Nat}
    (hk : k ≤ Fintype.card Fact) :
    (1 - Real.exp (-1)) * (Nat.min k D.card : ℝ) ≤ dependencyCoverage D (forwardSearch D k) := by
  simpa [forwardSearch] using greedySelect_one_minus_exp_bound_of_le_card (D := D) (k := k) hk

def isSelectedB (S : Finset Fact) (a : Fact) : Bool :=
  decide (a ∈ S)

/-- Single backward-chaining pick: choose any currently selected fact. -/
noncomputable def backwardPick? (S : Finset Fact) : Option Fact :=
  firstWhere? (isSelectedB S) ((Finset.univ : Finset Fact).toList)

/-- Single backward-chaining step: erase one currently selected fact if present. -/
noncomputable def backwardStep (S : Finset Fact) : Finset Fact :=
  match backwardPick? S with
  | some a => S.erase a
  | none => S

lemma backwardPick?_some_of_card_pos (S : Finset Fact)
    (hS : 0 < S.card) :
    ∃ a, backwardPick? S = some a ∧ a ∈ S := by
  rcases Finset.card_pos.mp hS with ⟨a0, ha0S⟩
  have hex :
      ∃ x ∈ (Finset.univ : Finset Fact).toList, isSelectedB S x = true := by
    refine ⟨a0, by simp, ?_⟩
    simp [isSelectedB, ha0S]
  rcases firstWhere?_some_of_exists
      (p := isSelectedB S)
      (l := (Finset.univ : Finset Fact).toList) hex with ⟨a, hpick⟩
  have hspec : isSelectedB S a = true :=
    firstWhere?_some_spec
      (p := isSelectedB S)
      (l := (Finset.univ : Finset Fact).toList) hpick
  exact ⟨a, hpick, by simpa [isSelectedB] using hspec⟩

theorem backwardStep_card_sub_one_of_card_pos (S : Finset Fact)
    (hS : 0 < S.card) :
    (backwardStep S).card = S.card - 1 := by
  rcases backwardPick?_some_of_card_pos (S := S) hS with ⟨a, hpick, haS⟩
  simpa [backwardStep, hpick] using Finset.card_erase_of_mem haS

/-- Bounded backward search from an initial selected set. -/
noncomputable def backwardSearch : Nat → Finset Fact → Finset Fact
  | 0, S => S
  | n + 1, S => backwardSearch n (backwardStep S)

theorem backwardSearch_card_eq_sub :
    ∀ {n : Nat} {S : Finset Fact},
      n ≤ S.card → (backwardSearch n S).card = S.card - n
  | 0, S, _ => by
      simp [backwardSearch]
  | n + 1, S, hle => by
      have hSpos : 0 < S.card := lt_of_lt_of_le (Nat.succ_pos n) hle
      have hstepCard : (backwardStep S).card = S.card - 1 :=
        backwardStep_card_sub_one_of_card_pos (S := S) hSpos
      have hleSub : n ≤ S.card - 1 := Nat.le_sub_of_add_le hle
      have hleStep : n ≤ (backwardStep S).card := by
        simpa [hstepCard] using hleSub
      have ih := backwardSearch_card_eq_sub (n := n) (S := backwardStep S) hleStep
      calc
        (backwardSearch (n + 1) S).card
            = (backwardSearch n (backwardStep S)).card := by
                simp [backwardSearch]
        _ = (backwardStep S).card - n := ih
        _ = (S.card - 1) - n := by simp [hstepCard]
        _ = S.card - (1 + n) := by simpa using (Nat.sub_sub S.card 1 n)
        _ = S.card - (n + 1) := by simp [Nat.add_comm]

/-- Bounded bidirectional search:
forward phase from empty, then optional backward trimming to budget `topK`. -/
noncomputable def boundedSearch (D : Finset Fact) (topK fuel : Nat) : Finset Fact :=
  let Sf := forwardSearch D fuel
  if _ : topK ≤ Sf.card then
    backwardSearch (Sf.card - topK) Sf
  else Sf

theorem boundedSearch_eq_forwardSearch_of_card_le_topK
    (D : Finset Fact) (topK fuel : Nat)
    (hcard : (forwardSearch D fuel).card ≤ topK) :
    boundedSearch D topK fuel = forwardSearch D fuel := by
  unfold boundedSearch
  set Sf := forwardSearch D fuel
  by_cases htop : topK ≤ Sf.card
  · have hEq : Sf.card = topK := Nat.le_antisymm (by simpa [Sf] using hcard) htop
    simp [hEq, Sf, backwardSearch]
  · simp [htop, Sf]

/-- Operator-style direction tag. -/
inductive ChainerDirection where
  | forward
  | backward
  deriving DecidableEq, Repr

/-- Operator-style bounded search config. -/
structure ChainerConfig where
  fuel : Nat
  topK : Nat
  deriving Repr

/-- Operator-style entrypoint used by front-end bindings. -/
noncomputable def runChainer
    (dir : ChainerDirection) (cfg : ChainerConfig)
    (D : Finset Fact) (S0 : Finset Fact := ∅) : Finset Fact :=
  match dir with
  | .forward => boundedSearch D cfg.topK cfg.fuel
  | .backward => backwardSearch cfg.fuel S0

@[simp] theorem runChainer_forward (cfg : ChainerConfig) (D S0 : Finset Fact) :
    runChainer (Fact := Fact) .forward cfg D S0 = boundedSearch D cfg.topK cfg.fuel := by
  rfl

@[simp] theorem runChainer_backward (cfg : ChainerConfig) (D S0 : Finset Fact) :
    runChainer (Fact := Fact) .backward cfg D S0 = backwardSearch cfg.fuel S0 := by
  rfl

end Interfaces

end

end Mettapedia.Logic.PLNInferenceControlChainer
