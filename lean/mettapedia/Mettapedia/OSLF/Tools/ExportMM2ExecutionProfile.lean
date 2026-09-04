import Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-mm2-execution-profile <output-path>"
      pure 2
