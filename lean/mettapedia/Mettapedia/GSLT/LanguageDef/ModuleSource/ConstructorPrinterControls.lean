import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-! Module text round trips retain nonidentifier and keyword constructor
heads as well as escaped literal data in nested patterns and syntax rows. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.ConstructorPrinterControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ModuleSource.Commands
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

Module ExactConstructorText {
  Theory Data() {
    Types { E; }
    Terms {
      "namespace:node" . child:E |- "node" child : E;
      "if" . |- "keyword" : E;
      "quotes \"and\" \\ slash\nλ😀" . child:E |- "escaped \"text\" \\ payload\nλ😀" child : E;
    }
    Rewrites {
      Keep . x:E |- "namespace:node"(x) ~> "namespace:node"(x);
      Keyword . |- "if" ~> "if";
      Escaped . x:E |- "quotes \"and\" \\ slash\nλ😀"(x) ~> "namespace:node"(x);
    }
  }
  theory Data()
}

#module_roundtrip ExactConstructorText

theorem nonidentifier_application_text :
    Printer.pattern [] (.apply "namespace:node" [.apply "if" []]) =
      "\"namespace:node\"(\"if\")" := by
  rw [Printer.pattern_apply_one _ _ _ (by decide +kernel), Printer.pattern_nullary]
  decide +kernel

theorem escaped_constructor_text :
    Printer.pattern [] (.apply "quotes \"and\" \\ slash\nλ😀" [.fvar "x"]) =
      "\"quotes \\\"and\\\" \\\\ slash\\nλ😀\"(? \"x\")" := by
  rw [Printer.pattern_apply_one _ _ _ (by decide +kernel), Printer.pattern_free]
  decide +kernel

theorem keyword_does_not_become_a_variable :
    Printer.pattern [] (.apply "if" []) ≠ Printer.pattern [] (.fvar "if") := by
  rw [Printer.pattern_nullary, Printer.pattern_free]
  decide +kernel

#print axioms nonidentifier_application_text
#print axioms escaped_constructor_text
#print axioms keyword_does_not_become_a_variable

end Mettapedia.GSLT.LanguageDef.ModuleSource.ConstructorPrinterControls
