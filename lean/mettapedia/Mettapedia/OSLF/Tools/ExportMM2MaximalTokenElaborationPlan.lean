import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlanWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlanWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-mm2-elaboration-plan <output-path>"
      pure 2
