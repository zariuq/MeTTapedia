import Foundation.FirstOrder.Incompleteness.Dense
import Mettapedia.Logic.StoneGunkDuality
import Mettapedia.SetTheory.OpenTower.InternalTower

/-!
# No terminal stage, no isolated completion, no principal perspective

Three statements are kept apart here, because none implies another.

1. **No terminal stage** (a tower of sets). Every closed set is a member of a later closed set,
   under the named inaccessibility hypothesis (`closedSets_noTerminalStage`, from
   `InternalTower.no_terminal_stage`).
2. **No isolated completion** (theories). For every consistent theory of arithmetic that
   extends `𝗜𝚺₁` and is `Δ₁`-axiomatized, the space of its completions is nonempty
   (`completions_nonempty`) and perfect (`completions_perfect`): no completion is isolated
   (`no_isolated_completion`). This is Gödel–Rosser incompleteness (the Lindenbaum algebra is
   densely ordered, from the Foundation library) read through Stone duality (atomless iff
   perfect, `Foundations.Gunk.isGunky_iff_perfect_stoneSpace`).
3. **No principal perspective** (points of a space of perspectives). Atomless Boolean
   algebras have perfect Stone spaces; on the stage indices of an ω-tower, no free ultrafilter
   is the only free ultrafilter containing one of its sets (`free_ultrafilter_not_isolated`).

**What connects them, as theorems.** For a Boolean algebra, "the nonzero elements form a
refinement tower without a terminal stage" is equivalent to "the Stone space has no isolated
point" (`noTerminalStage_iff_perfect`). For the arithmetic theories above, the consistent
finite strengthenings of the theory form a tower without a terminal stage
(`lindenbaum_noTerminalStage`), which is the same statement as (2). The tower of sets in (1)
is a different order: its stages are sets, not sentences, and no theorem here derives (1) from
(2) or (2) from (1).

**What (2) does not say.** It does not refute the existence of a model of the theory, or of a
complete consistent extension: completions exist. It does not prevent a stronger metatheory
from naming one completion, for instance the theory of the standard model. It says that no
completion is cut out of the others by a single sentence over the theory.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion

open LO LO.FirstOrder LO.Entailment Mettapedia.Foundations.Gunk
open Mettapedia.Logic.HOL.Embedding ZFSetUniverseClosure InternalTower

universe u

/-! ## A tower without a terminal stage, as an order-theoretic statement -/

/-- A relation of "later stage" in which every stage has a later one. -/
def NoTerminalStage {α : Type*} (later : α → α → Prop) : Prop :=
  ∀ p, ∃ q, later p q

/-- Strict refinement among the nonzero elements of an order: a stage `a` is followed by a
strictly smaller nonzero `b`. -/
def refines {B : Type*} [PartialOrder B] [OrderBot B] (a b : {x : B // x ≠ ⊥}) : Prop :=
  b.1 < a.1

theorem isGunky_iff_noTerminalStage {B : Type*} [PartialOrder B] [OrderBot B] :
    IsGunky B ↔ NoTerminalStage (refines (B := B)) := by
  constructor
  · intro hg a
    obtain ⟨b, hb, hba⟩ := hg a.1 a.2
    exact ⟨⟨b, hb⟩, hba⟩
  · intro hn a ha
    obtain ⟨b, hba⟩ := hn ⟨a, ha⟩
    exact ⟨b.1, b.2, hba⟩

/-- **For a Boolean algebra, a refinement tower without a terminal stage is a space of
perspectives without an isolated point.** -/
theorem noTerminalStage_iff_perfect (B : Type u) [BooleanAlgebra B] :
    NoTerminalStage (refines (B := B)) ↔ PerfectSpace (StoneSpace B) :=
  isGunky_iff_noTerminalStage.symm.trans isGunky_iff_perfect_stoneSpace

/-- Negative control: a two-valued algebra, the shape of a complete theory, has a terminal
stage. -/
theorem bool_has_terminalStage : ¬ NoTerminalStage (refines (B := Bool)) :=
  fun h => not_isGunky_bool (isGunky_iff_noTerminalStage.mpr h)

/-- **Statement 1.** Closed sets under membership have no terminal stage. -/
theorem closedSets_noTerminalStage (h : CofinalInaccessibles.{u}) :
    NoTerminalStage (fun U V : {U : ZFSet.{u} // Closed U} => U.1 ∈ V.1) := by
  intro U
  obtain ⟨V, hV, hUV, _⟩ := no_terminal_stage h U.1
  exact ⟨⟨V, hV⟩, hUV⟩

/-! ## Statement 2: no isolated completion -/

theorem isGunky_of_denselyOrdered {α : Type*} [PartialOrder α] [OrderBot α]
    [DenselyOrdered α] : IsGunky α := by
  intro a ha
  obtain ⟨b, hb₁, hb₂⟩ := exists_between (bot_lt_iff_ne_bot.mpr ha)
  exact ⟨b, ne_bot_of_gt hb₁, hb₂⟩

/-- The Lindenbaum algebra of a `Δ₁` extension of `𝗜𝚺₁` is atomless. -/
theorem lindenbaum_isGunky (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁] :
    IsGunky (LindenbaumAlgebra T) :=
  isGunky_of_denselyOrdered

/-- The consistent finite strengthenings of the theory form a tower without a terminal stage:
every consistent sentence over the theory is strictly implied by another consistent one. -/
theorem lindenbaum_noTerminalStage (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁] :
    NoTerminalStage (refines (B := LindenbaumAlgebra T)) :=
  isGunky_iff_noTerminalStage.mp (lindenbaum_isGunky T)

/-- The space of completions is perfect. -/
theorem completions_perfect (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁] :
    PerfectSpace (StoneSpace (LindenbaumAlgebra T)) :=
  isGunky_iff_perfect_stoneSpace.mp (lindenbaum_isGunky T)

/-- A consistent theory has a completion. -/
theorem completions_nonempty (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁] [Consistent T] :
    Nonempty (StoneSpace (LindenbaumAlgebra T)) := by
  have : Nontrivial (LindenbaumAlgebra T) := LindenbaumAlgebra.nontrivial_of_consistent
  have : Nontrivial (AsBoolRing (LindenbaumAlgebra T)) := ‹Nontrivial (LindenbaumAlgebra T)›
  infer_instance

/-- **Statement 2.** No completion is isolated: every completion is a limit of others. -/
theorem no_isolated_completion (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁]
    (x : StoneSpace (LindenbaumAlgebra T)) : ¬ IsOpen ({x} : Set _) := by
  have := perfectSpace_iff_forall_not_isolated.mp (completions_perfect T) x
  exact not_isOpen_singleton x

/-! ## Statement 3: no principal perspective on the stage indices -/

/-- A set in a free ultrafilter on the natural numbers is infinite. -/
theorem infinite_of_mem_free {𝒰 : Ultrafilter ℕ} (hfree : (𝒰 : Filter ℕ) ≤ Filter.cofinite)
    {A : Set ℕ} (hA : A ∈ 𝒰) : A.Infinite := by
  intro hfin
  have hcompl : Aᶜ ∈ (𝒰 : Filter ℕ) := hfree (Filter.mem_cofinite.mpr (by simpa using hfin))
  exact (Ultrafilter.compl_notMem_iff.mpr hA) hcompl

/-- An infinite set of natural numbers contains two disjoint infinite sets. -/
theorem exists_disjoint_infinite {A : Set ℕ} (hA : A.Infinite) :
    ∃ B C : Set ℕ, B ⊆ A ∧ C ⊆ A ∧ B.Infinite ∧ C.Infinite ∧ Disjoint B C := by
  let e := hA.natEmbedding A
  have he : Function.Injective fun n => (e n).1 :=
    fun m n same => e.injective (Subtype.ext same)
  refine ⟨Set.range fun n => (e (2 * n)).1, Set.range fun n => (e (2 * n + 1)).1,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (e (2 * n)).2
  · rintro _ ⟨n, rfl⟩
    exact (e (2 * n + 1)).2
  · exact Set.infinite_range_of_injective (fun m n same => by
      have := he same
      omega)
  · exact Set.infinite_range_of_injective (fun m n same => by
      have := he same
      omega)
  · rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ ⟨n, same⟩
    have := he same
    omega

/-- **Statement 3, for the stage indices of an ω-tower.** No free ultrafilter is the only free
ultrafilter containing one of its sets: every free perspective is a limit of others. -/
theorem free_ultrafilter_not_isolated {𝒰 : Ultrafilter ℕ}
    (hfree : (𝒰 : Filter ℕ) ≤ Filter.cofinite) {A : Set ℕ} (hA : A ∈ 𝒰) :
    ∃ 𝒱 : Ultrafilter ℕ, (𝒱 : Filter ℕ) ≤ Filter.cofinite ∧ A ∈ 𝒱 ∧ 𝒱 ≠ 𝒰 := by
  obtain ⟨B, C, hB, hC, hBinf, hCinf, hBC⟩ :=
    exists_disjoint_infinite (infinite_of_mem_free hfree hA)
  have hnot : B ∉ 𝒰 ∨ C ∉ 𝒰 := by
    by_contra both
    push Not at both
    have := Filter.inter_mem both.1 both.2
    rw [hBC.inter_eq] at this
    exact 𝒰.empty_notMem this
  rcases hnot with hB𝒰 | hC𝒰
  · have := hBinf.cofinite_inf_principal_neBot
    let 𝒱 := Ultrafilter.of (Filter.cofinite ⊓ Filter.principal B)
    have hle : (𝒱 : Filter ℕ) ≤ Filter.cofinite ⊓ Filter.principal B := Ultrafilter.of_le _
    have hB𝒱 : B ∈ 𝒱 := (le_inf_iff.mp hle).2 (Filter.mem_principal_self B)
    refine ⟨𝒱, (le_inf_iff.mp hle).1, Filter.mem_of_superset hB𝒱 hB, ?_⟩
    rintro rfl
    exact hB𝒰 hB𝒱
  · have := hCinf.cofinite_inf_principal_neBot
    let 𝒱 := Ultrafilter.of (Filter.cofinite ⊓ Filter.principal C)
    have hle : (𝒱 : Filter ℕ) ≤ Filter.cofinite ⊓ Filter.principal C := Ultrafilter.of_le _
    have hC𝒱 : C ∈ 𝒱 := (le_inf_iff.mp hle).2 (Filter.mem_principal_self C)
    refine ⟨𝒱, (le_inf_iff.mp hle).1, Filter.mem_of_superset hC𝒱 hC, ?_⟩
    rintro rfl
    exact hC𝒰 hC𝒱

#print axioms noTerminalStage_iff_perfect
#print axioms bool_has_terminalStage
#print axioms closedSets_noTerminalStage
#print axioms lindenbaum_noTerminalStage
#print axioms completions_perfect
#print axioms completions_nonempty
#print axioms no_isolated_completion
#print axioms free_ultrafilter_not_isolated

end Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion
