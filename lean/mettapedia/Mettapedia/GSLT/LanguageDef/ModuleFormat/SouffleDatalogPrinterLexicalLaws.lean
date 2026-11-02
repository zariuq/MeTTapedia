import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinter

/-! Lexical leaves built by the independent-IR printer retain their exact
characters through the shared grammar printer. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.Parsing

theorem scalar_complete (row : ScalarCore.Row) (character : Char)
    (formed : SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className character.toNat) :
    scalar? (ScalarCore.lexicalState row).resultSort character = .ok (ScalarCore.leaf row character.toNat formed) := by
  simp only [scalar?,CorePrinter.lexical_row_exact]
  simp only [dif_pos formed]
  rfl

theorem lexical_row_sort (sort : String) (row : ScalarCore.Row)
    (selected : CorePrinter.lexicalRow? sort = some row) :
    (ScalarCore.lexicalState row).resultSort = sort := by
  unfold CorePrinter.lexicalRow? at selected
  split at selected
  · rename_i actual picked
    cases Option.some.inj selected
    have present : row ∈ (List.finRange SourceViews.profile.states.length).filter
        (fun candidate => (ScalarCore.lexicalState candidate).resultSort == sort) := by
      rw [picked]
      exact List.mem_singleton_self _
    exact beq_iff_eq.mp (List.mem_filter.mp present).2
  · cases selected

theorem scalar_print (sort : String) (character : Char) (pattern : Pattern)
    (built : scalar? sort character = .ok pattern) :
    CorePrinter.printText? sort pattern = some (String.singleton character) := by
  unfold scalar? at built
  cases selected : CorePrinter.lexicalRow? sort with
  | none => simp [selected] at built
  | some row =>
    simp only [selected] at built
    split at built
    · rename_i formed
      cases Except.ok.inj built
      have sameSort := lexical_row_sort sort row selected
      subst sort
      have lexical : CorePrinter.lexical (ScalarCore.lexicalState row).resultSort =
          some (fun pattern => (ScalarCore.readLeaf? row pattern).map (fun point => [point])) := by
        simp only [CorePrinter.lexical,CorePrinter.lexical_row_exact,Option.map_some]
      have printed : CorePrinter.printScalars? (ScalarCore.lexicalState row).resultSort (ScalarCore.leaf row character.toNat formed) =
          (ScalarCore.readLeaf? row (ScalarCore.leaf row character.toNat formed)).map (fun point => [point]) := by
        unfold ScalarCore.leaf ScalarCore.wordLeaf
        exact DeclaredConstructorPrinter.print?_lexical _ _ _ _ _ _ _ lexical
      simp only [CorePrinter.printText?,printed,ScalarCore.readLeaf?_leaf,Option.map_some,
        List.map_singleton,Char.ofNat_toNat]
      rfl
    · cases built

#print axioms lexical_row_sort
#print axioms scalar_print
#print axioms scalar_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
