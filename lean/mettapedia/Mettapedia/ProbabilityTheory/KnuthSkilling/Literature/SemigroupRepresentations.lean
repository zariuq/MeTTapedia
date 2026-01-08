import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Real.Embedding
import Mathlib.RingTheory.HahnSeries.HahnEmbedding

/-!
# Representation scaffolding for ordered groups/semigroups

This file is a staging area for formalizing (and then importing) the key *representation and
completion* theorems for ordered groups/semigroups that are adjacent to the K&S Appendix A goals.

Primary sources (local PDFs):
- `literature/KS_codex/Ordered_Semigroups_Hofner.pdf` (Fox 1975, ordered-group completions/embeddings)
- `literature/KS_codex/Fuchs_2007_Ordered_Groups.pdf` (survey note on ordered groups)
- `literature/KS_codex/Representation_Theorems_Ordered_Structures.pdf` (survey)
- `literature/KS_codex/Bajri_2021_Semigroup_Representations.pdf` (thesis)
- `literature/KS_codex/Kudryavtseva_2015_Lattice_Ordered_Semigroups.pdf` (lattice-ordered semigroups)

For now we:
1. Define the named properties that recur across these sources (cancellation, “isolated” subgroup,
   divisibility/completion).
2. Package the large theorems as explicit `Prop` interfaces (no `sorry`) with citations.

The intent is to bridge to K&S as follows:
`[KSSeparation α]` should imply a small list of these hypotheses, which then implies an embedding
into an ordered abelian group / ℝ, making commutativity automatic.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

open Classical

/-!
## Isolated subgroups (Fox 1975, §1.1)

Fox defines a subgroup `B` of a group `G` to be isolated if `g^n ∈ B` implies `g ∈ B`.
Mathlib already has the notion `Subgroup.IsIsolated` in some contexts, but we record the definition
explicitly here to keep the literature mapping obvious.
-/

def Subgroup.IsIsolated {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ g : G, ∀ n : ℕ, 0 < n → g ^ n ∈ H → g ∈ H

/-!
### Isolated closure (Fox 1975, §1.1)

Fox defines the *isolated closure* `I(A)` of a subgroup `A ≤ G` as the intersection of all isolated
subgroups of `G` containing `A`.

We formalize this construction using the complete lattice structure on `Subgroup G`.
-/

/-- The set of isolated subgroups of `G` that contain `A`. -/
def Subgroup.isolatedSupersets {G : Type*} [Group G] (A : Subgroup G) : Set (Subgroup G) :=
  {H : Subgroup G | A ≤ H ∧ Subgroup.IsIsolated H}

/-- The *isolated closure* `I(A)` of a subgroup `A ≤ G`: intersection of all isolated subgroups
containing `A`. (Fox 1975, §1.1) -/
def Subgroup.isolatedClosure {G : Type*} [Group G] (A : Subgroup G) : Subgroup G :=
  sInf (Subgroup.isolatedSupersets A)

theorem Subgroup.le_isolatedClosure {G : Type*} [Group G] (A : Subgroup G) :
    A ≤ Subgroup.isolatedClosure A := by
  refine le_sInf ?_
  intro H hH
  exact hH.1

theorem Subgroup.isolated_isolatedClosure {G : Type*} [Group G] (A : Subgroup G) :
    Subgroup.IsIsolated (Subgroup.isolatedClosure A) := by
  intro g n hn hgn
  -- Reduce to membership in each isolated superset.
  refine (Subgroup.mem_sInf).2 ?_
  intro H hH
  have hgnH : g ^ n ∈ H := (Subgroup.mem_sInf).1 hgn H hH
  exact hH.2 g n hn hgnH

theorem Subgroup.isolatedClosure_le {G : Type*} [Group G] (A H : Subgroup G) (hAH : A ≤ H)
    (hH : Subgroup.IsIsolated H) : Subgroup.isolatedClosure A ≤ H := by
  refine sInf_le ?_
  exact ⟨hAH, hH⟩

theorem Subgroup.isolatedClosure_eq {G : Type*} [Group G] (A : Subgroup G) (hA : Subgroup.IsIsolated A) :
    Subgroup.isolatedClosure A = A := by
  apply le_antisymm
  · exact Subgroup.isolatedClosure_le A A le_rfl hA
  · exact Subgroup.le_isolatedClosure A

/-!
## Divisibility and completion (Fox 1975, §1.1)

Fox: a group is divisible if `∀ g n>0, ∃ x, x^n = g`.
-/

def Group.IsDivisible (G : Type*) [Group G] : Prop :=
  ∀ g : G, ∀ n : ℕ, 0 < n → ∃ x : G, x ^ n = g

/-!
## Theorems now available in mathlib (ordered abelian groups)

Two of the “big” representation results in the PDF set are now present in mathlib:

1. **Hölder embedding** for Archimedean ordered abelian groups:
   `Archimedean.exists_orderAddMonoidHom_real_injective`
   (see `Mathlib/Data/Real/Embedding.lean`).
2. **Hahn embedding theorem** for linearly ordered abelian groups:
   `hahnEmbedding_isOrderedAddMonoid`
   (see `Mathlib/RingTheory/HahnSeries/HahnEmbedding.lean`).

We wrap these in K&S-facing names so the Appendix A development can depend on them without
hard-coding mathlib paths.
-/

/-- **Hölder embedding** (Clay–Rolfsen Thm 2.6, Hölder 1901):
an ordered embedding of an Archimedean linearly ordered abelian group into `ℝ`. -/
def HolderEmbeddingSpec (G : Type*) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] : Prop :=
  ∃ f : G →+o ℝ, Function.Injective f

/-- Mathlib provides Hölder’s embedding for Archimedean ordered abelian groups. -/
theorem holderEmbeddingSpec_of_archimedean (G : Type*) [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [Archimedean G] : HolderEmbeddingSpec G := by
  simpa [HolderEmbeddingSpec] using (Archimedean.exists_orderAddMonoidHom_real_injective (M := G))

/-- **Hahn embedding theorem** (Clifford 1954; modern proof in mathlib):
every linearly ordered abelian group embeds as an ordered subgroup of a Hahn product. -/
def OrderedGroupHahnEmbeddingSpec (G : Type*) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] :
    Prop :=
  ∃ f : G →+o Lex (HahnSeries (FiniteArchimedeanClass G) ℝ), Function.Injective f

/-- Mathlib’s Hahn embedding theorem, repackaged as `OrderedGroupHahnEmbeddingSpec`. -/
theorem orderedGroupHahnEmbeddingSpec (G : Type*) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] :
    OrderedGroupHahnEmbeddingSpec G := by
  refine ⟨?_, ?_⟩
  · exact (hahnEmbedding_isOrderedAddMonoid (M := G)).choose
  · exact (hahnEmbedding_isOrderedAddMonoid (M := G)).choose_spec.1

end Mettapedia.ProbabilityTheory.KnuthSkilling.Literature
