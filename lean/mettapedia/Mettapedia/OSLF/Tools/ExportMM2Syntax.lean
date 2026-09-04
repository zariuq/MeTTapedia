import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-mm2-syntax <output-path>"
      pure 2
