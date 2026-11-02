import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalProvider
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTermCodec
import Mettapedia.Languages.Maude.ConditionalMaxValue

/-! Actual encoded equality rows preserve numeral identities. Snapshot
membership reflects exactly the bounded true comparisons, so a failed
comparison cannot enter through an encoding collision.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL

theorem numeral_injective : Function.Injective Maude.ConditionalMax.numeral := by
  intro first second same
  have values := congrArg Maude.ConditionalMax.value? same
  simpa only [Maude.ConditionalMax.value?_numeral, Option.some.injEq] using values

theorem trueRow_injective {first second left right : Nat}
    (same : trueRow first second = trueRow left right) : first = left ∧ second = right := by
  have values := congrArg GeneralPremise.ProviderRow.values same
  have firstValue := (List.cons.inj values).1
  have terms := encode_injective firstValue
  have arguments := (Maude.Term.app.inj terms).2
  have firstSame := (List.cons.inj arguments).1
  have secondSame := (List.cons.inj (List.cons.inj arguments).2).1
  exact ⟨numeral_injective firstSame, numeral_injective secondSame⟩

theorem trueRow_member_iff (bound left right : Nat) :
    trueRow left right ∈ (provider bound).rows ↔ left ≤ bound ∧ right ≤ bound ∧ left ≤ right := by
  constructor
  · intro member
    obtain ⟨⟨first, second⟩, pair, same⟩ := List.mem_map.mp member
    obtain ⟨rfl, rfl⟩ := trueRow_injective same
    exact (comparisonPairs_iff bound _ _).mp pair
  · intro bounds
    exact List.mem_map.mpr ⟨(left, right), (comparisonPairs_iff bound left right).mpr bounds, rfl⟩

theorem false_guard_has_no_row (bound left right : Nat) (falseGuard : right < left) :
    trueRow left right ∉ (provider bound).rows := by
  intro member
  have ordered := ((trueRow_member_iff bound left right).mp member).2.2
  omega

#print axioms trueRow_member_iff
#print axioms false_guard_has_no_row

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation
