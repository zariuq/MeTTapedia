import Mettapedia.DocText.MetatheoryReadmeCompositional

open Mettapedia.DocText.MetatheoryReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/lean-projects/mettapedia/Mettapedia/Metatheory/README.md" metatheoryReadmeMarkdown
