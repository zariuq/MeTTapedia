import Mettapedia.InformationTheory.RelationStoreFloors
import Mettapedia.Computability.KolmogorovComplexity.Basic

/-!
# The floor for stored relations in Kolmogorov complexity

A program for a relation's bitmap is a description of the relation: run the
program, read the bits back.  So the counting floor of `RelationStoreFloors`
holds for program length too:

* `exists_relation_complexity_ge` : for any algorithm reaching every string,
  some `N`-element relation over `M` tuples needs a program of at least
  `⌊log₂ C(M, N)⌋` bits for its bitmap;
* `exists_relation_kolmogorov_ge` : the same for the Kolmogorov complexity `K`
  of the universal algorithm;
* `card_complexity_lt_lt` : fewer than `2 ^ L` relations have bitmaps with
  programs shorter than `L`, so all but a `2⁻ᶜ` share of the `N`-element
  relations have complexity at least `⌊log₂ C(M, N)⌋ - c`.
-/

namespace Mettapedia.InformationTheory.RelationStoreFloors

open Finset KolmogorovComplexity

variable {β : Type*}

/-- Run `U` on a program and read its output through the decoder `R`. -/
noncomputable def throughAlgorithm (U : Algorithm) (R : BinString → Option β)
    (p : BinString) : Option β := by
  classical
  exact if h : (U p).Dom then R ((U p).get h) else none

theorem throughAlgorithm_of_mem {U : Algorithm} {R : BinString → Option β}
    {p x : BinString} (h : x ∈ U p) : throughAlgorithm U R p = R x := by
  classical
  obtain ⟨hdom, hget⟩ := h
  unfold throughAlgorithm
  rw [dif_pos hdom, hget]

/-- A program shorter than `L` for the encoding of `s` describes `s` in fewer
than `L` bits. -/
theorem describedBelow_of_complexity_lt {U : Algorithm} {R : BinString → Option β}
    {enc : β → BinString} (hR : ∀ s, R (enc s) = some s) {s : β} {L : ℕ}
    (hreach : ∃ p, enc s ∈ U p) (hlt : C[U](enc s) < L) :
    DescribedBelow (throughAlgorithm U R) L s := by
  obtain ⟨p, hp, hlen⟩ := exists_program_of_complexity U (enc s) hreach
  exact ⟨p, (throughAlgorithm_of_mem hp).trans (hR s), hlen ▸ hlt⟩

variable {M : ℕ}

/-- For any algorithm reaching every string, some `N`-element relation over
`M` tuples has a bitmap of complexity at least `⌊log₂ C(M, N)⌋`. -/
theorem exists_relation_complexity_ge (U : Algorithm) (hU : ∀ x, ∃ p, x ∈ U p)
    {N : ℕ} (hN : N ≤ M) :
    ∃ s : Finset (Fin M), s.card = N ∧
      Nat.log 2 (M.choose N) ≤ C[U](bitmapEncode s) := by
  obtain ⟨s, hs, hnot⟩ := exists_subset_needs_log_choose
    (throughAlgorithm U (bitmapDecode (M := M))) (α := Fin M) (N := N) (by simpa using hN)
  refine ⟨s, hs, not_lt.mp fun hlt => hnot ?_⟩
  simpa using describedBelow_of_complexity_lt (L := Nat.log 2 (M.choose N))
    bitmapDecode_encode (hU (bitmapEncode s)) hlt

/-- Fewer than `2 ^ L` relations of any size have bitmaps with programs
shorter than `L`, under any algorithm reaching every string. -/
theorem card_complexity_lt_lt (U : Algorithm) (hU : ∀ x, ∃ p, x ∈ U p)
    (F : Finset (Finset (Fin M))) (L : ℕ) :
    (F.filter fun s => C[U](bitmapEncode s) < L).card < 2 ^ L := by
  classical
  have hsub : F.filter (fun s => C[U](bitmapEncode s) < L) ⊆
      F.filter (DescribedBelow (throughAlgorithm U (bitmapDecode (M := M))) L) := by
    intro s hs
    rw [mem_filter] at hs ⊢
    exact ⟨hs.1, describedBelow_of_complexity_lt bitmapDecode_encode
      (hU (bitmapEncode s)) hs.2⟩
  refine (card_le_card hsub).trans_lt ?_
  simpa using card_describedBelow_lt
    (throughAlgorithm U (bitmapDecode (M := M))) (σ := Bool) (by simp) F L

/-- The universal algorithm reaches every string: through the identity. -/
theorem universal_reaches (x : BinString) :
    ∃ p, x ∈ (Classical.choose exists_optimal_algorithm) p := by
  obtain ⟨code, hcode⟩ := universal_is_universal identityAlgorithm identityAlgorithm_partrec
  exact ⟨code ++ x, hcode x x (by simp [identityAlgorithm])⟩

/-- Some `N`-element relation over `M` tuples has a bitmap of Kolmogorov
complexity at least `⌊log₂ C(M, N)⌋`. -/
theorem exists_relation_kolmogorov_ge {N : ℕ} (hN : N ≤ M) :
    ∃ s : Finset (Fin M), s.card = N ∧
      Nat.log 2 (M.choose N) ≤ K(bitmapEncode s) :=
  exists_relation_complexity_ge _ universal_reaches hN

/-- Incompressibility in Kolmogorov complexity: if `2 ^ (L + c) ≤ C(M, N)`,
the `N`-element relations whose bitmaps have complexity below `L` number fewer
than `C(M, N) / 2 ^ c`. -/
theorem card_kolmogorov_lt_mul_lt {N L c : ℕ} (hL : 2 ^ (L + c) ≤ M.choose N) :
    (((univ : Finset (Fin M)).powersetCard N).filter
        fun s => K(bitmapEncode s) < L).card * 2 ^ c < M.choose N := by
  have hlt := card_complexity_lt_lt _ universal_reaches
    ((univ : Finset (Fin M)).powersetCard N) L
  calc (((univ : Finset (Fin M)).powersetCard N).filter
          fun s => K(bitmapEncode s) < L).card * 2 ^ c
      < 2 ^ L * 2 ^ c := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
    _ = 2 ^ (L + c) := (pow_add _ _ _).symm
    _ ≤ M.choose N := hL

end Mettapedia.InformationTheory.RelationStoreFloors
