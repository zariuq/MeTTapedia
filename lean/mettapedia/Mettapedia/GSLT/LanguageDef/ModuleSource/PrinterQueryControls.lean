import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-! Query relation names have their own quoted source syntax. Punctuation in
an authored relation must survive module printing and reading unchanged. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.PrinterQueryControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open scoped Commands

Module QueryRoundtrip {
  Theory Data() {
    Types { Datum; }
    Terms {
      Zero . |- "zero" : Datum;
      Query . input:Datum |- "query" input : Datum;
    }
    Rewrites {
      QueryNamed . input:Datum, output:Datum | "ml-primitive"(input, output) |-
        (Query input) ~> output;
      QueryEscaped . input:Datum, output:Datum | "quoted\"relation\\name"(input, output) |-
        (Query input) ~> output;
      QueryPlain . input:Datum, output:Datum | ordinary(input, output) |-
        (Query input) ~> output;
    }
  }
  theory Data()
}

#guard QueryRoundtrip.language.isOk
#module_roundtrip QueryRoundtrip
#guard Printer.premise (.relationQuery "ml-primitive" [.fvar "input", .fvar "output"]) ==
  "\"ml-primitive\"(input, output)"
#guard Printer.premise (.relationQuery "ordinary" []) == "\"ordinary\"()"

end Mettapedia.GSLT.LanguageDef.ModuleSource.PrinterQueryControls
