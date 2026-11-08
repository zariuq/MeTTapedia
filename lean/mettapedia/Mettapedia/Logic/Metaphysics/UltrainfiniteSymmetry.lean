import Mathlib.Logic.Equiv.Basic
import Mettapedia.Logic.Metaphysics.UltrainfiniteCofinite

/-!
# No symmetric choice of a free One

**The shared form** (`select_ne_of_fixed`): if a selection commutes with a symmetry, then at a
point the symmetry fixes, the selection is neither member of a pair the symmetry exchanges.

**Ultrafilters** (`map_ne_of_preimage_eq_compl`): a map that carries a set onto its complement
moves every ultrafilter. The proof is the shared form, with the ultrafilter as the fixed point and
"the half of `{S, Sᶜ}` it contains" as the selection (`chosenHalf`, `chosenHalf_map`).

* **No ultrafilter on `ℕ` is fixed by every permutation** (`no_permutation_invariant_ultrafilter`);
  the evens/odds swap alone moves each one (`map_evenOddSwap_ne`).
* Control: **every free ultrafilter is fixed by every transposition** (`map_swap_eq_of_isFree`), so
  by every permutation that moves finitely many points. What a free ultrafilter decides is
  invisible to finite changes; only an infinite symmetry, such as the swap, moves it.

The relation to `ObserverChoices.no_equivariant_selection` is in `UltrainfiniteSymmetryObserver`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

universe u v

/-- **The shared form**: at a fixed point of a symmetry, a selection that commutes with the
symmetry is neither member of a pair the symmetry exchanges. -/
theorem select_ne_of_fixed {X : Sort u} {Y : Sort v} (act : X → X) (act' : Y → Y) (select : X → Y)
    (equivariant : ∀ x, select (act x) = act' (select x)) {x : X} (fixed : act x = x) {a b : Y}
    (apart : a ≠ b) (exchanges : act' a = b ∧ act' b = a) : select x ≠ a ∧ select x ≠ b := by
  have kept : act' (select x) = select x := by rw [← equivariant, fixed]
  refine ⟨fun picked => ?_, fun picked => ?_⟩
  · rw [picked, exchanges.1] at kept
    exact apart kept.symm
  · rw [picked, exchanges.2] at kept
    exact apart kept

/-! ## Ultrafilters -/

section Ultrafilters

open Classical in
/-- The half of `{S, Sᶜ}` an ultrafilter contains. -/
noncomputable def chosenHalf {α : Type u} (S : Set α) (U : Ultrafilter α) : Set α :=
  if S ∈ U then S else Sᶜ

theorem chosenHalf_map {α : Type u} {S : Set α} {m : α → α} (swaps : m ⁻¹' S = Sᶜ)
    (U : Ultrafilter α) : chosenHalf S (U.map m) = m ⁻¹' chosenHalf S U := by
  have moved : S ∈ U.map m ↔ S ∉ U := by
    rw [Ultrafilter.mem_map, swaps, Ultrafilter.compl_mem_iff_notMem]
  unfold chosenHalf
  by_cases inside : S ∈ U
  · rw [if_neg (fun h => moved.mp h inside), if_pos inside, swaps]
  · rw [if_pos (moved.mpr inside), if_neg inside, Set.preimage_compl, swaps, compl_compl]

/-- **A map that carries a set onto its complement moves every ultrafilter.** -/
theorem map_ne_of_preimage_eq_compl {α : Type u} {S : Set α} {m : α → α} (swaps : m ⁻¹' S = Sᶜ)
    (U : Ultrafilter α) : U.map m ≠ U := by
  intro fixed
  have apart : S ≠ Sᶜ := fun same => by
    obtain ⟨x⟩ := U.nonempty_of_mem Filter.univ_mem
    have := congrArg (x ∈ ·) same
    simp at this
  have exchanges : m ⁻¹' S = Sᶜ ∧ m ⁻¹' Sᶜ = S := ⟨swaps, by rw [Set.preimage_compl, swaps, compl_compl]⟩
  obtain ⟨notS, notCompl⟩ :=
    select_ne_of_fixed (Ultrafilter.map m) (Set.preimage m) (chosenHalf S) (chosenHalf_map swaps)
      fixed apart exchanges
  unfold chosenHalf at notS notCompl
  split_ifs at notS notCompl
  · exact notS rfl
  · exact notCompl rfl

end Ultrafilters

/-! ## The evens/odds swap on `ℕ` -/

/-- Exchange `2k` and `2k + 1`. -/
def evenOddSwapFun (n : ℕ) : ℕ := if n % 2 = 0 then n + 1 else n - 1

theorem evenOddSwapFun_involutive : Function.Involutive evenOddSwapFun := fun n => by
  unfold evenOddSwapFun
  split_ifs <;> omega

/-- **The evens/odds swap**, a permutation of `ℕ`. -/
def evenOddSwap : Equiv.Perm ℕ := evenOddSwapFun_involutive.toPerm

/-- The evens. -/
def evens : Set ℕ := {n | n % 2 = 0}

theorem preimage_evenOddSwap_evens : evenOddSwap ⁻¹' evens = evensᶜ := by
  ext n
  simp only [evenOddSwap, Function.Involutive.coe_toPerm, Set.mem_preimage, evens,
    Set.mem_ofPred_eq, Set.mem_compl_iff, evenOddSwapFun]
  split_ifs <;> omega

/-- **The swap moves every ultrafilter on `ℕ`.** -/
theorem map_evenOddSwap_ne (U : Ultrafilter ℕ) : U.map evenOddSwap ≠ U :=
  map_ne_of_preimage_eq_compl preimage_evenOddSwap_evens U

/-- **No ultrafilter on `ℕ` is fixed by every permutation.** -/
theorem no_permutation_invariant_ultrafilter :
    ¬ ∃ U : Ultrafilter ℕ, ∀ π : Equiv.Perm ℕ, U.map π = U :=
  fun ⟨U, fixed⟩ => map_evenOddSwap_ne U (fixed evenOddSwap)

/-! ## Control: finite symmetries fix the free ultrafilters -/

/-- **Every free ultrafilter is fixed by every transposition.** -/
theorem map_swap_eq_of_isFree {α : Type u} [DecidableEq α] {U : Ultrafilter α} (free : IsFree U)
    (a b : α) : U.map (Equiv.swap a b) = U := by
  have away : ∀ᶠ x in (U : Filter α), x ≠ a ∧ x ≠ b :=
    (Filter.le_cofinite_iff_eventually_ne.mp (isFree_iff_le_cofinite.mp free) a).and
      (Filter.le_cofinite_iff_eventually_ne.mp (isFree_iff_le_cofinite.mp free) b)
  refine Ultrafilter.ext fun s => ?_
  rw [Ultrafilter.mem_map]
  refine Filter.congr_sets ?_
  filter_upwards [away] with x ⟨ha, hb⟩
  show (Equiv.swap a b) x ∈ s ↔ x ∈ s
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- The hyperfilter on `ℕ` is fixed by the transposition of `0` and `1` but not by the swap. -/
theorem hyperfilter_swap_control :
    (Filter.hyperfilter ℕ).map (Equiv.swap 0 1) = Filter.hyperfilter ℕ ∧
      (Filter.hyperfilter ℕ).map evenOddSwap ≠ Filter.hyperfilter ℕ :=
  ⟨map_swap_eq_of_isFree isFree_hyperfilter 0 1, map_evenOddSwap_ne _⟩

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms select_ne_of_fixed
#print axioms chosenHalf_map
#print axioms map_ne_of_preimage_eq_compl
#print axioms preimage_evenOddSwap_evens
#print axioms map_evenOddSwap_ne
#print axioms no_permutation_invariant_ultrafilter
#print axioms map_swap_eq_of_isFree
#print axioms hyperfilter_swap_control

end Mettapedia.Logic.Metaphysics.Ultrainfinite
