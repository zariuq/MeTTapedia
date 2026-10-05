import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalLookupProgram

/-! # Faithful data encodings for ordered natural-key tables -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem encodeNaturalTable_injective {α : Type} (encode : α → Term)
    (injective : Function.Injective encode) : Function.Injective (encodeNaturalTable encode) := by
  intro left right same
  apply List.map_injective_iff.mpr ?_ (Term.list.inj same)
  intro left right same
  rcases left with ⟨key, value⟩
  rcases right with ⟨other, entry⟩
  simp only [Term.list.injEq, List.cons.injEq, and_true] at same
  exact Prod.ext (natural_injective same.1) (injective same.2)

theorem encodeLookupResult_injective : Function.Injective encodeLookupResult := by
  intro left right same
  cases left <;> cases right <;> simp_all [encodeLookupResult]

theorem natural_table_preserves_duplicate_rows (key : Nat) (first second : Term) :
    encodeNaturalTable id [(key, first), (key, second)] =
      .list [.list [natural key, first], .list [natural key, second]] := rfl

theorem natural_table_distinguishes_row_order (key : Nat) (first second : Term)
    (different : first ≠ second) :
    encodeNaturalTable id [(key, first), (key, second)] ≠
      encodeNaturalTable id [(key, second), (key, first)] := by
  intro same
  have rows := encodeNaturalTable_injective id Function.injective_id same
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at rows
  exact different rows.1

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
