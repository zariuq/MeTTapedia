import Mettapedia.GSLT.LanguageDef.WaltersZantemaDAWire

open Mettapedia.GSLT.LanguageDef.WaltersZantemaDA.Wire in
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      writeRadixTwo path
      pure 0
  | _ =>
      IO.eprintln "usage: ExportWaltersZantemaDA <output.metta>"
      pure 1
