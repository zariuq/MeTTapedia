import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-! Quoted variable and rule names retain punctuation and keywords. Their
spellings stay distinct from quoted constructor heads. -/

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.QuotedVariableControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Commands

#module_file "../../../../../../metta/gslt/module/controls/QuotedVariables.module"
#module_roundtrip QuotedVariables

theorem punctuation_preserved :
    Printer.pattern [] (.fvar "ml:environment") = "? \"ml:environment\"" := by
  rw [Printer.pattern_free]
  decide +kernel

theorem keyword_preserved :
    Printer.pattern [] (.fvar "by") = "? \"by\"" := by
  rw [Printer.pattern_free]
  decide +kernel

theorem constructor_and_variable_differ :
    Printer.pattern [] (.apply "ml:environment" []) ≠ Printer.pattern [] (.fvar "ml:environment") := by
  rw [Printer.pattern_nullary, Printer.pattern_free]
  decide +kernel

theorem punctuation_is_not_whitespace :
    Printer.pattern [] (.fvar "ml:environment") ≠ Printer.pattern [] (.fvar "ml environment") := by
  rw [Printer.pattern_free, Printer.pattern_free]
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleSource.QuotedVariableControls
