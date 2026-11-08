import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionDerivation

/-!
# Redundancy of non-ground clauses and inferences

Redundancy is defined through ground instances:

* **A non-ground clause is redundant** with respect to a set `N` (`NRedundant`) when every ground
  instance of it is redundant (Bachmair–Ganzinger) with respect to the ground instances of `N`
  (`groundInstances`).
* **A non-ground inference is redundant** with respect to a set of ground clauses `T`
  (`RedundantNInference`) when every ground instance of it that is an inference of the ground
  calculus is redundant with respect to `T`. An inference whose conclusion is in `N` is redundant
  with respect to the ground instances of `N` (`RedundantNInference.of_mem`): making an inference
  makes it redundant.

## Simplifications lift

The non-ground simplifications (`NSimplification`): tautology deletion (a literal `s ≈ s`, or a
literal with its complement), subsumption by a strict sub-multiset of an instance, demodulation by an
instance of a unit equation `l ≈ r` with `lσ ≻ rσ` and below a literal of the clause, and deletion
of a literal `s ≉ s`.

* **Every ground instance of a non-ground simplification is a ground simplification**
  (`NSimplification.ground`), with premises and replacements among the ground instances of the
  non-ground ones.
* Hence **a simplified clause is redundant** with respect to any set holding the premises and
  replacements (`NSimplification.redundant`): if a simplification takes a clause, every ground
  instance of that clause is redundant.

## Removing redundant clauses keeps redundancy

The irredundant ground instances of `N` are ground instances of `N \ R` when every clause of `R` is
redundant (`irredundant_subset`). So redundancy of clauses and inferences survives removing
redundant clauses (`NRedundant.diff`, `RedundantNInference.diff`), by the ground theorem
`redundant_diff`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

variable {sig : LPSignature}

/-! ## The non-ground simplifications -/

/-- **The non-ground simplification rules**: `NSimplification ord C premises replacements`. -/
inductive NSimplification (ord : StableOrder sig) :
    NClause sig → List (NClause sig) → List (NClause sig) → Prop
  /-- Tautology deletion: a literal `s ≈ s`. -/
  | tautology (C : NClause sig) (L : NLit sig) (member : L ∈ C) (positive : L.negative = false)
      (trivial : L.lhs = L.rhs) : NSimplification ord C [] []
  /-- Tautology deletion: a literal together with its complement. -/
  | complementary (C : NClause sig) (L M : NLit sig) (inL : L ∈ C) (inM : M ∈ C)
      (positive : L.negative = false) (negative : M.negative = true)
      (sides : (M.lhs = L.lhs ∧ M.rhs = L.rhs) ∨ (M.lhs = L.rhs ∧ M.rhs = L.lhs)) :
      NSimplification ord C [] []
  /-- Subsumption: an instance of `D` is a strict sub-multiset of `C`. -/
  | subsumption (C D : NClause sig) (σ : Subst sig)
      (sub : ((D.subst σ : NClause sig) : Multiset (NLit sig)) ≤ (C : Multiset (NLit sig)))
      (proper : D.length < C.length) : NSimplification ord C [D] []
  /-- Demodulation: rewrite a side of a literal with an instance of a unit equation that is
  decreasing and below a literal of the clause. -/
  | demodulation (s t : NClause sig) (M : NLit sig) (l r : Term sig) (σ : Subst sig)
      (c : FirstOrderRewriting.Context sig) (other : Term sig)
      (sides : (M.lhs = c.fill (σ.applyTerm l) ∧ M.rhs = other) ∨
        (M.rhs = c.fill (σ.applyTerm l) ∧ M.lhs = other))
      (decreasing : ord.gt (σ.applyTerm l) (σ.applyTerm r))
      (smaller : ∃ K ∈ s ++ M :: t, ord.litGt K (posLit (σ.applyTerm l) (σ.applyTerm r))) :
      NSimplification ord (s ++ M :: t) [[posLit l r]]
        [⟨M.negative, c.fill (σ.applyTerm r), other⟩ :: (s ++ t)]
  /-- Deletion of a literal `s ≉ s`. -/
  | deleteFalse (s t : NClause sig) (L : NLit sig) (negative : L.negative = true)
      (trivial : L.lhs = L.rhs) : NSimplification ord (s ++ L :: t) [] [s ++ t]

section Redundancy

variable [LinearOrder (GroundTerm sig)]

/-- **The ground instances of a set of non-ground clauses.** -/
def groundInstances (N : Set (NClause sig)) : Set (Clause (GroundTerm sig)) :=
  {G | ∃ C ∈ N, ∃ θ : Grounding sig, NClause.ground θ C = G}

theorem ground_mem_groundInstances {N : Set (NClause sig)} {C : NClause sig} (member : C ∈ N)
    (θ : Grounding sig) : NClause.ground θ C ∈ groundInstances N :=
  ⟨C, member, θ, rfl⟩

theorem groundInstances_mono {N N' : Set (NClause sig)} (sub : N ⊆ N') :
    groundInstances N ⊆ groundInstances N' :=
  fun _ ⟨C, member, θ, same⟩ => ⟨C, sub member, θ, same⟩

/-- **A redundant non-ground clause**: every ground instance is redundant with respect to the ground
instances of the set. -/
def NRedundant (N : Set (NClause sig)) (C : NClause sig) : Prop :=
  ∀ θ : Grounding sig, Redundant (groundInstances N) (NClause.ground θ C)

theorem NRedundant.mono {N N' : Set (NClause sig)} (sub : N ⊆ N') {C : NClause sig}
    (redundant : NRedundant N C) : NRedundant N' C :=
  fun θ => (redundant θ).mono (groundInstances_mono sub)

/-- **A redundant non-ground inference**, with premises `side` and `main`, most general unifier `μ`
and conclusion `concl`: every ground instance that is an inference of the ground calculus is
redundant with respect to `T`. -/
def RedundantNInference (T : Set (Clause (GroundTerm sig))) (side : Option (NClause sig))
    (main : NClause sig) (μ : Subst sig) (concl : NClause sig) : Prop :=
  ∀ ν : Grounding sig,
    Inference (side.map fun D => NClause.ground ν (D.subst μ)) (NClause.ground ν (main.subst μ))
      (NClause.ground ν concl) →
    RedundantInference T (NClause.ground ν (main.subst μ)) (NClause.ground ν concl)

theorem RedundantNInference.mono {T T' : Set (Clause (GroundTerm sig))} (sub : T ⊆ T')
    {side : Option (NClause sig)} {main : NClause sig} {μ : Subst sig} {concl : NClause sig}
    (redundant : RedundantNInference T side main μ concl) : RedundantNInference T' side main μ concl :=
  fun ν inference => (redundant ν inference).mono sub

/-- **Making an inference makes it redundant**: an inference whose conclusion is in `N` is redundant
with respect to the ground instances of `N`, because the calculus is reductive. -/
theorem RedundantNInference.of_mem [GroundSimplification sig] {N : Set (NClause sig)}
    {side : Option (NClause sig)} {main : NClause sig} {μ : Subst sig} {concl : NClause sig}
    (member : concl ∈ N) : RedundantNInference (groundInstances N) side main μ concl :=
  fun ν inference => RedundantInference.of_mem inference (ground_mem_groundInstances member ν)

/-- **The irredundant ground instances survive removing redundant clauses.** -/
theorem irredundant_subset {N R : Set (NClause sig)} (removed : ∀ D ∈ R, NRedundant N D) :
    irredundant (groundInstances N) ⊆ groundInstances (N \ R) := by
  rintro G ⟨⟨C, member, θ, rfl⟩, notRedundant⟩
  by_cases inR : C ∈ R
  · exact absurd (removed C inR θ) notRedundant
  · exact ⟨C, ⟨member, inR⟩, θ, rfl⟩

variable [WellFoundedLT (GroundTerm sig)]

/-- **Removing redundant clauses keeps the redundancy of clauses.** -/
theorem NRedundant.diff {N R : Set (NClause sig)} (removed : ∀ D ∈ R, NRedundant N D)
    {C : NClause sig} (redundant : NRedundant N C) : NRedundant (N \ R) C :=
  fun θ => (redundant_diff (redundant θ)).mono (irredundant_subset removed)

/-- **Removing redundant clauses keeps the redundancy of inferences.** -/
theorem RedundantNInference.diff {N R : Set (NClause sig)} (removed : ∀ D ∈ R, NRedundant N D)
    {side : Option (NClause sig)} {main : NClause sig} {μ : Subst sig} {concl : NClause sig}
    (redundant : RedundantNInference (groundInstances N) side main μ concl) :
    RedundantNInference (groundInstances (N \ R)) side main μ concl :=
  fun ν inference => (redundantInference_diff (redundant ν inference)).mono (irredundant_subset removed)

end Redundancy

/-! ## Simplifications lift -/

section Simplifications

variable [LinearOrder (GroundTerm sig)]

/-- A literal made on two terms has them as its sides, in one order or the other. -/
theorem Lit.make_sides {T : Type*} [LinearOrder T] (negative : Bool) (a b : T) :
    ((Lit.make negative a b).lhs = a ∧ (Lit.make negative a b).rhs = b) ∨
      ((Lit.make negative a b).rhs = a ∧ (Lit.make negative a b).lhs = b) := by
  rcases le_total b a with h | h
  · exact Or.inl ⟨max_eq_left h, min_eq_right h⟩
  · exact Or.inr ⟨min_eq_left h, max_eq_right h⟩

/-- **Every ground instance of a non-ground simplification is a ground simplification**, with premises
and replacements among the ground instances of the non-ground ones. -/
theorem NSimplification.ground (ord : GroundedOrder sig) {C : NClause sig} {ps rs : List (NClause sig)}
    (simplification : NSimplification ord.toStableOrder C ps rs) (θ : Grounding sig) :
    ∃ ps' rs' : List (Clause (GroundTerm sig)), Simplification (NClause.ground θ C) ps' rs' ∧
      (∀ G ∈ ps', ∃ D ∈ ps, ∃ θ' : Grounding sig, NClause.ground θ' D = G) ∧
      (∀ G ∈ rs', ∃ D ∈ rs, ∃ θ' : Grounding sig, NClause.ground θ' D = G) := by
  cases simplification with
  | tautology C L member positive trivial =>
      refine ⟨[], [], Simplification.tautology _ (L.ground θ) (NClause.mem_ground member) positive ?_,
        by simp, by simp⟩
      show min (θ.groundTerm L.lhs) (θ.groundTerm L.rhs) = max (θ.groundTerm L.lhs) (θ.groundTerm L.rhs)
      rw [trivial, min_self, max_self]
  | complementary C L M inL inM positive negative sides =>
      have same : (M.ground θ).lhs = (L.ground θ).lhs ∧ (M.ground θ).rhs = (L.ground θ).rhs := by
        show max (θ.groundTerm M.lhs) (θ.groundTerm M.rhs) = max (θ.groundTerm L.lhs) (θ.groundTerm L.rhs) ∧
          min (θ.groundTerm M.lhs) (θ.groundTerm M.rhs) = min (θ.groundTerm L.lhs) (θ.groundTerm L.rhs)
        rcases sides with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
          exact ⟨rfl, rfl⟩
        · rw [h1, h2]
          exact ⟨max_comm _ _, min_comm _ _⟩
      exact ⟨[], [], Simplification.complementary _ (L.ground θ) (M.ground θ) (NClause.mem_ground inL)
        (NClause.mem_ground inM) positive negative same.1 same.2, by simp, by simp⟩
  | subsumption C D σ sub proper =>
      refine ⟨[NClause.ground θ (D.subst σ)], [], Simplification.subsumption _ _ ?_ ?_, ?_, by simp⟩
      · exact Multiset.map_le_map sub
      · intro same
        have cards := congrArg Multiset.card same
        simp only [NClause.ground, NClause.subst, Multiset.coe_card, List.length_map] at cards
        omega
      · intro G member
        rw [List.mem_singleton.mp member]
        exact ⟨D, List.mem_singleton_self D, groundAfter θ σ, (NClause.ground_subst θ σ D).symm⟩
  | demodulation s t M l r σ c other sides decreasing smaller =>
      have below : θ.groundTerm (σ.applyTerm r) < θ.groundTerm (σ.applyTerm l) :=
        ord.gt_ground θ _ _ decreasing
      have posEq : (posLit (σ.applyTerm l) (σ.applyTerm r)).ground θ = Lit.pos _ _ below.le :=
        Lit.make_false_eq_pos below.le
      have sides' : ((M.ground θ).lhs = (groundCtx θ c).fill (θ.groundTerm (σ.applyTerm l)) ∧
            (M.ground θ).rhs = θ.groundTerm other) ∨
          ((M.ground θ).rhs = (groundCtx θ c).fill (θ.groundTerm (σ.applyTerm l)) ∧
            (M.ground θ).lhs = θ.groundTerm other) := by
        show ((Lit.make M.negative (θ.groundTerm M.lhs) (θ.groundTerm M.rhs)).lhs = _ ∧
            (Lit.make M.negative (θ.groundTerm M.lhs) (θ.groundTerm M.rhs)).rhs = _) ∨
          ((Lit.make M.negative (θ.groundTerm M.lhs) (θ.groundTerm M.rhs)).rhs = _ ∧
            (Lit.make M.negative (θ.groundTerm M.lhs) (θ.groundTerm M.rhs)).lhs = _)
        rcases sides with ⟨atL, atO⟩ | ⟨atL, atO⟩
        · rw [atL, atO, groundTerm_fill]
          exact Lit.make_sides _ _ _
        · rw [atL, atO, groundTerm_fill]
          rcases Lit.make_sides M.negative (θ.groundTerm other)
              ((groundCtx θ c).fill (θ.groundTerm (σ.applyTerm l))) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact Or.inl ⟨h2, h1⟩
      have smaller' : ClauseLT {Lit.pos _ _ below.le} (M.ground θ ::ₘ NClause.ground θ (s ++ t)) := by
        obtain ⟨K, member, gt⟩ := smaller
        have lt := ord.litGt_ground θ _ _ gt
        rw [posEq] at lt
        refine dm_of_all_below _ _ Multiset.cons_ne_zero fun y hy => ⟨K.ground θ, ?_, ?_⟩
        · rw [← NClause.ground_middle]
          exact NClause.mem_ground member
        · rw [Multiset.mem_singleton.mp hy]
          exact lt
      refine ⟨[{Lit.pos _ _ below.le}], [Lit.make M.negative
        ((groundCtx θ c).fill (θ.groundTerm (σ.applyTerm r))) (θ.groundTerm other) ::ₘ
          NClause.ground θ (s ++ t)], ?_, ?_, ?_⟩
      · rw [NClause.ground_middle]
        exact Simplification.demodulation _ (M.ground θ) (groundCtx θ c) below (θ.groundTerm other) sides'
          smaller'
      · intro G member
        rw [List.mem_singleton.mp member]
        refine ⟨[posLit l r], List.mem_singleton_self _, groundAfter θ σ, ?_⟩
        show (posLit l r).ground (groundAfter θ σ) ::ₘ 0 = _
        rw [← NLit.ground_subst]
        exact congrArg (· ::ₘ 0) posEq
      · intro G member
        rw [List.mem_singleton.mp member]
        refine ⟨_, List.mem_singleton_self _, θ, ?_⟩
        show Lit.make M.negative (θ.groundTerm (c.fill (σ.applyTerm r))) (θ.groundTerm other) ::ₘ
          NClause.ground θ (s ++ t) = _
        rw [groundTerm_fill]
  | deleteFalse s t L negative trivial =>
      refine ⟨[], [NClause.ground θ (s ++ t)], ?_, by simp, ?_⟩
      · rw [NClause.ground_middle]
        refine Simplification.deleteFalse _ (L.ground θ) negative ?_
        show min (θ.groundTerm L.lhs) (θ.groundTerm L.rhs) = max (θ.groundTerm L.lhs) (θ.groundTerm L.rhs)
        rw [trivial, min_self, max_self]
      · intro G member
        rw [List.mem_singleton.mp member]
        exact ⟨s ++ t, List.mem_singleton_self _, θ, rfl⟩

/-- **A simplification takes only a redundant clause**: every ground instance of the simplified clause
is redundant with respect to any set holding the premises and the replacements. -/
theorem NSimplification.redundant [GroundSimplification sig] (ord : GroundedOrder sig)
    {C : NClause sig} {ps rs : List (NClause sig)}
    (simplification : NSimplification ord.toStableOrder C ps rs) {N : Set (NClause sig)}
    (inN : ∀ D ∈ ps ++ rs, D ∈ N) : NRedundant N C := by
  intro θ
  obtain ⟨ps', rs', ground, fromPs, fromRs⟩ := simplification.ground ord θ
  obtain ⟨smaller, entails⟩ := ground.redundant
  refine entails.mono fun G member => ⟨?_, smaller G ?_⟩
  · rcases member with inPs | inRs
    · obtain ⟨D, memD, θ', rfl⟩ := fromPs G inPs
      exact ⟨D, inN D (List.mem_append_left _ memD), θ', rfl⟩
    · obtain ⟨D, memD, θ', rfl⟩ := fromRs G inRs
      exact ⟨D, inN D (List.mem_append_right _ memD), θ', rfl⟩
  · rcases member with inPs | inRs
    · exact List.mem_append_left _ inPs
    · exact List.mem_append_right _ inRs

end Simplifications

#print axioms ground_mem_groundInstances
#print axioms NRedundant.mono
#print axioms RedundantNInference.mono
#print axioms RedundantNInference.of_mem
#print axioms irredundant_subset
#print axioms NRedundant.diff
#print axioms RedundantNInference.diff
#print axioms Lit.make_sides
#print axioms NSimplification.ground
#print axioms NSimplification.redundant

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
