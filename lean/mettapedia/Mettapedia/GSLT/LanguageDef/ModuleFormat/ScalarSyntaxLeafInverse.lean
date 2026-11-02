import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Inverse
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

/-! Successful lexical printing retains the exact canonical scalar leaf and
its declared character-class evidence. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter

theorem lexicalRow?_sort {description : Description} {sort : String}
    {row : Fin description.profile.states.length}
    (selected : lexicalRow? description sort = some row) :
    (description.profile.states.get row).resultSort = sort := by
  unfold lexicalRow? at selected
  split at selected
  · rename_i actual picked
    cases Option.some.inj selected
    have present : row ∈ (List.finRange description.profile.states.length).filter
        (fun candidate => (description.profile.states.get candidate).resultSort == sort) := by
      rw [picked]
      exact List.mem_singleton_self _
    exact beq_iff_eq.mp (List.mem_filter.mp present).2
  · cases selected

theorem readLeaf?_inverse {description : Description} {row : Fin description.profile.states.length}
    {pattern : Pattern} {point : Nat} (read : readLeaf? description row pattern = some point) :
    ∃ formed : description.profile.ClassEvidence (description.profile.states.get row).className point,
      leaf description row point formed = pattern := by
  unfold readLeaf? at read
  split at read
  · rename_i label word
    split at read
    · rename_i labelEq
      obtain ⟨actual, decoded, accepted⟩ := Option.bind_eq_some_iff.mp read
      split at accepted
      · rename_i formed
        cases Option.some.inj accepted
        obtain ⟨bounded, encoded⟩ := Radix16Codec.decode?_inverse word point
          (Radix16Scalar.decode?_formed word point decoded).1
        refine ⟨formed, ?_⟩
        simp only [leaf, wordLeaf, encoded, labelEq]
      · cases accepted
    · cases read
  · cases read

theorem constructor?_meaning {grammar : LanguageDef} {label sort : String} {row : GrammarRule}
    (selected : constructor? grammar label sort = some row) :
    row ∈ grammar.terms ∧ row.label = label ∧ row.category = sort := by
  unfold constructor? at selected
  split at selected
  · rename_i actual picked
    cases Option.some.inj selected
    have present : row ∈ grammar.terms.filter (fun candidate => candidate.label == label && candidate.category == sort) := by
      rw [picked]
      exact List.mem_singleton_self _
    simpa only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] using present
  · cases selected

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
