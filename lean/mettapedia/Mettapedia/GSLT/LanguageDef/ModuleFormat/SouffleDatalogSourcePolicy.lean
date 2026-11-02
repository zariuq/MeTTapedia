import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax
import Mettapedia.GSLT.LanguageDef.ModuleSource.StringListView

/-! Datalog's reserved identifiers are read from its authored selection
port. The vocabulary follows the pinned Souffle 2.5 scanner; constructor
grammar, word selection and semantic IR remain separate layers. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePolicy

open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

def filters? : Option (List SourceSyntax.FamilyFilter) := SourceSyntax.selection? Syntax.library Syntax.module

def words? : Option (List String) := do
  let [.rejectWords "DlIdentifier" words] ← filters? | none
  some words

def reservedWords : List String := module_strings_view% words?

theorem words_exact : words? = some reservedWords := by decide +kernel

def filters : List SourceSyntax.FamilyFilter := [.rejectWords "DlIdentifier" reservedWords]

theorem filters_exact : filters? = some [.rejectWords "DlIdentifier" reservedWords] := by decide +kernel

theorem reserved_controls : "count" ∈ reservedWords ∧ "match" ∈ reservedWords ∧
    "if" ∉ reservedWords ∧ "counted" ∉ reservedWords := by decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePolicy
