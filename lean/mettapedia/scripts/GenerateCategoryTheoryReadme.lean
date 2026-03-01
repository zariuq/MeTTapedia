import Mettapedia.DocText.CategoryTheoryReadmeCompositional

open Mettapedia.DocText.CategoryTheoryReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/lean-projects/mettapedia/Mettapedia/CategoryTheory/README.md" categoryTheoryReadmeMarkdown
