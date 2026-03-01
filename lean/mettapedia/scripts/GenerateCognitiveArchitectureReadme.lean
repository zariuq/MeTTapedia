import Mettapedia.DocText.CognitiveArchitectureReadmeCompositional

open Mettapedia.DocText.CognitiveArchitectureReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/lean-projects/mettapedia/Mettapedia/CognitiveArchitecture/README.md" cognitiveArchitectureReadmeMarkdown
