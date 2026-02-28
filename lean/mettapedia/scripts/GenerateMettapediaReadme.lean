import Mettapedia.DocText.MettapediaReadmeCompositional

open Mettapedia.DocText.MettapediaReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/lean-projects/mettapedia/README.md" mettapediaReadmeMarkdown
