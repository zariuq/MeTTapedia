import Mettapedia.DocText.MmLean4ReadmeCompositional

open Mettapedia.DocText.MmLean4ReadmeCompositional

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.print mmLean4ReadmeMarkdown
      return 0
  | [output] =>
      IO.FS.writeFile output mmLean4ReadmeMarkdown
      return 0
  | _ =>
      IO.eprintln "Usage: GenerateMmLean4Readme.lean [OUTPUT]"
      return 2
