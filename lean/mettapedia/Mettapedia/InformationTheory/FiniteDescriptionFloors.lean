import Mettapedia.InformationTheory.RelationStoreKolmogorov

/-!
# Description and program-length floors for finite semantic interfaces

These laws reuse the existing finite-string counting and Kolmogorov
development, with an arbitrary finite value type instead of a relation
bitmap. They are worst-case/counting laws for a fixed decoder or algorithm,
not per-value lower bounds and not a procedure for finding shortest programs.

When the value type is an observer quotient, only observable distinctions
are charged. The decoder, retained context and chosen output encoding remain
part of the stated interface. No uniform probability on source states or
machine memory layout is inferred from a count of semantic classes.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.FiniteDescriptionFloors

open RelationStoreFloors KolmogorovComplexity

universe u

theorem exists_value_not_short {Value : Type u} [Finite Value] (decoder : List Bool → Option Value)
    (length : Nat) (enoughValues : 2 ^ length ≤ Nat.card Value) :
    ∃ value, ¬DescribedBelow decoder length value := by
  classical
  let := Fintype.ofFinite Value
  have short := card_describedBelow_lt decoder (by simp : 2 ≤ Fintype.card Bool)
    (Finset.univ : Finset Value) length
  have fewer : ((Finset.univ : Finset Value).filter (DescribedBelow decoder length)).card <
      (Finset.univ : Finset Value).card := by
    simpa only [Fintype.card_bool, Finset.card_univ, ← Nat.card_eq_fintype_card] using short.trans_le enoughValues
  obtain ⟨value, member, missing⟩ := Finset.exists_mem_notMem_of_card_lt_card fewer
  exact ⟨value, fun described => missing (Finset.mem_filter.mpr ⟨member, described⟩)⟩

theorem exists_value_needs_floor_log {Value : Type u} [Finite Value] [Nonempty Value]
    (decoder : List Bool → Option Value) :
    ∃ value, ¬DescribedBelow decoder (Nat.log 2 (Nat.card Value)) value :=
  exists_value_not_short decoder _ (Nat.pow_log_le_self 2 (Nat.card_pos.ne'))

theorem short_values_fraction {Value : Type u} [Fintype Value] (decoder : List Bool → Option Value)
    (length slack : Nat) (enoughValues : 2 ^ (length + slack) ≤ Fintype.card Value)
    [DecidablePred (DescribedBelow decoder length)] :
    ((Finset.univ : Finset Value).filter (DescribedBelow decoder length)).card * 2 ^ slack < Fintype.card Value := by
  have short := card_describedBelow_lt decoder (by simp : 2 ≤ Fintype.card Bool)
    (Finset.univ : Finset Value) length
  rw [Fintype.card_bool] at short
  calc
    _ < 2 ^ length * 2 ^ slack := Nat.mul_lt_mul_of_pos_right short (by positivity)
    _ = 2 ^ (length + slack) := (Nat.pow_add ..).symm
    _ ≤ _ := enoughValues

/-- Any algorithm whose outputs include the chosen encoding inherits the
description floor. The decoder's round trip prevents merging distinct values. -/
theorem exists_program_length_floor {Value : Type u} [Finite Value] [Nonempty Value]
    (algorithm : Algorithm) (encode : Value → BinString) (decode : BinString → Option Value)
    (roundtrip : ∀ value, decode (encode value) = some value)
    (reachable : ∀ value, ∃ program, encode value ∈ algorithm program) :
    ∃ value, Nat.log 2 (Nat.card Value) ≤ C[algorithm](encode value) := by
  obtain ⟨value, notShort⟩ := exists_value_needs_floor_log (throughAlgorithm algorithm decode)
  refine ⟨value, Nat.le_of_not_gt ?_⟩
  intro short
  exact notShort (describedBelow_of_complexity_lt roundtrip (reachable value) short)

theorem exists_kolmogorov_floor {Value : Type u} [Finite Value] [Nonempty Value]
    (encode : Value → BinString) (decode : BinString → Option Value)
    (roundtrip : ∀ value, decode (encode value) = some value) :
    ∃ value, Nat.log 2 (Nat.card Value) ≤ K(encode value) :=
  exists_program_length_floor _ encode decode roundtrip (fun value => universal_reaches (encode value))

namespace Controls

def onlyZero : List Bool → Option (Fin 2) := fun _ => some 0

theorem one_value_can_be_exceptionally_short : DescribedBelow onlyZero 1 0 :=
  ⟨[], rfl, by decide⟩

theorem the_same_decoder_cannot_describe_the_other : ¬DescribedBelow onlyZero 1 1 := by
  rintro ⟨program, equal, _⟩
  have impossible : (some (0 : Fin 2)) = some 1 := equal
  cases impossible

end Controls

end Mettapedia.InformationTheory.FiniteDescriptionFloors
