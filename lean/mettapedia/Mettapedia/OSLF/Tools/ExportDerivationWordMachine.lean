import Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      IO.FS.writeFile path
        Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef.wire
      pure 0
  | _ =>
      IO.eprintln
        "usage: export-derivation-word-machine <output-path>"
      pure 2
