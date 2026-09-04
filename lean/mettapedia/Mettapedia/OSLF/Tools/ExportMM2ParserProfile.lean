import Mettapedia.Languages.ProcessCalculi.MORK.MM2ParserProfileWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.Languages.ProcessCalculi.MORK.MM2ParserProfileWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-mm2-parser-profile <output-path>"
      pure 2
