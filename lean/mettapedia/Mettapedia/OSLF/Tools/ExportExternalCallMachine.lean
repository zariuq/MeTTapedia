import Mettapedia.GSLT.LanguageDef.ExternalCallMachine

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      IO.FS.writeFile path
        Mettapedia.GSLT.LanguageDef.ExternalCallMachine.externalCallLanguageWire
      pure 0
  | _ =>
      IO.eprintln "usage: export-external-call-machine <output-path>"
      pure 2
