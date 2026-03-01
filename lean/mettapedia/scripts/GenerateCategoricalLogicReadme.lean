import Mettapedia.DocText.CategoricalLogicReadmeCompositional

open Mettapedia.DocText.CategoricalLogicReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/lean-projects/mettapedia/Mettapedia/CategoricalLogic/README.md" categoricalLogicReadmeMarkdown
