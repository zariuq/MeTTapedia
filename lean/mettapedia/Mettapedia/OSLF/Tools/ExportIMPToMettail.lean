import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.Languages.IMP.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.Languages.IMP.LanguageDef

private def withIMPLogicStub (src : String) : String :=
  if src.endsWith "}" then
    (src.dropEnd 1).toString
      ++ "\n\n    logic {\n"
      ++ "        relation storeGet(Store, ImpVar, Nat);\n"
      ++ "        relation storeSet(Store, ImpVar, Nat, Store);\n"
      ++ "        relation natAdd(Nat, Nat, Nat);\n"
      ++ "        relation natMul(Nat, Nat, Nat);\n"
      ++ "        relation natLe(Nat, Nat, Bool);\n"
      ++ "        relation natEq(Nat, Nat, Bool);\n"
      ++ "    },\n"
      ++ "}"
  else
    src

/-- Print IMP as Rust `language!` macro text to stdout. -/
def main (_args : List String) : IO UInt32 := do
  IO.println (withIMPLogicStub (renderLanguage imp))
  pure 0
