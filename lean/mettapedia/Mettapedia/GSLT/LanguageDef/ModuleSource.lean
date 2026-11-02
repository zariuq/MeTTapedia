import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTyping
import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTypingControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtraction
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraInterpretation
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.Printer
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.Controls
import Mettapedia.GSLT.LanguageDef.ModuleSource.FaithfulSpellingControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.QuotedVariableControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSource
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSourceControls

/-!
# The `.module` format

The human text format of language definitions: theories with parameters, joins over shared
origins, replacements and renamed exports, imports, and an entry theory. `#module_file` reads a
`.module` file in Lean and `ModuleSource.elaborate` gives it its `LanguageDef`;
`ModuleSource.Printer.print` writes it back. The same format is LBNF data
(`metta/gslt/module/module_v1.cf`) for grammar-driven readers; `ModuleSource.LbnfDecode` reads
their trees as the same module data.

`Inductives` retains dependent declarations as source data. The selected Nat/Vec
route resolves their names and enters indexed admission; the ordinary regular
LanguageDef projection refuses this block rather than dropping it. General
typed module composition and textual operation elaboration remain separate.
-/
