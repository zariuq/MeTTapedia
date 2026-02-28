import Mettapedia.DocText.GFReadmeCompositional

open Mettapedia.DocText.GFReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/Languages/GF/README.md" gfReadmeMarkdown
