import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalCompilation

/-! Every finite equality row has an actual source equality derivation.
False comparisons and values outside the declared envelope have no row;
absence outside that envelope is not advertised as a source decision.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem provider_row_source {bound : Nat} {row : GeneralPremise.ProviderRow}
    (member : row ∈ (provider bound).rows) :
    ∃ left right, left ≤ bound ∧ right ≤ bound ∧ left ≤ right ∧ row = trueRow left right ∧
      Maude.Equivalent Maude.Examples.conditional [] "Bool"
        (Maude.ConditionalMax.le (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right))
        Maude.ConditionalMax.truth := by
  obtain ⟨⟨left, right⟩, pairMember, same⟩ := List.mem_map.mp member
  have bounds := (comparisonPairs_iff bound left right).mp pairMember
  exact ⟨left, right, bounds.1, bounds.2.1, bounds.2.2, same.symm,
    comparison_source_equality bound left right pairMember⟩

#guard (1, 3) ∈ comparisonPairs 3
#guard (2, 2) ∈ comparisonPairs 3
#guard (0, 0) ∈ comparisonPairs 0
#guard (3, 1) ∉ comparisonPairs 3
#guard (4, 4) ∉ comparisonPairs 3
#guard (provider 0).rows.length == 1
#guard (provider 3).rows.length == 10

#print axioms provider_row_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation
