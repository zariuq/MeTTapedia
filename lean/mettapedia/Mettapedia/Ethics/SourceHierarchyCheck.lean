import Mettapedia.Ethics.SourceHierarchyConcordance

/-!
# Executable Formal Ethics hierarchy check

This checker parses one SUO-KIF source and compares the represented ethical
theory and sentence subclass edges with the finite, theorem-checked tables in
`SourceHierarchyConcordance`.
-/

set_option autoImplicit false

open Mettapedia.Languages.KIF

namespace Mettapedia.Ethics.SourceHierarchyCheck

open SourceHierarchyConcordance

def edgeText (edge : String × String) : String :=
  s!"{edge.1} -> {edge.2}"

def hierarchyNames (edges : List (String × String)) : List String :=
  (edges.flatMap fun edge => [edge.1, edge.2]).eraseDups

unsafe def reportEdges
    (label : String) (actual expected : List (String × String)) : IO Bool := do
  let missing := edgeDifference expected actual
  let extra := edgeDifference actual expected
  IO.println s!"{label} expected edges: {expected.eraseDups.length}"
  IO.println s!"{label} source edges: {actual.eraseDups.length}"
  IO.println s!"{label} missing edges: {missing.length}"
  for edge in missing do
    IO.eprintln s!"missing {label} edge: {edgeText edge}"
  IO.println s!"{label} extra edges: {extra.length}"
  for edge in extra do
    IO.eprintln s!"extra {label} edge: {edgeText edge}"
  return missing.isEmpty && extra.isEmpty

unsafe def checkFile (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  match lex source with
  | .error failure =>
      IO.eprintln s!"lexical error: {repr failure}"
      return 1
  | .ok lexed =>
      let parsed := parse lexed
      let inventory := declarationInventory parsed
      IO.println s!"top-level forms: {parsed.forms.length}"
      IO.println s!"structural errors: {parsed.errors.length}"
      for failure in parsed.errors do
        IO.eprintln s!"structural error: {repr failure}"
      IO.println s!"declaration errors: {inventory.errors.length}"
      for failure in inventory.errors do
        IO.eprintln s!"declaration error: {repr failure}"
      let theoryEdges := relevantTheoryEdges inventory.declarations
      let sentenceEdges := relevantSentenceEdges inventory.declarations
      let theoryValid ← reportEdges "ethical-theory"
        theoryEdges expectedNamedTheoryEdges
      let sentenceValid ← reportEdges "ethical-sentence"
        sentenceEdges expectedNamedSentenceEdges
      let theoryNamesMissing := representedTheoryNames.filter fun name =>
        !(hierarchyNames theoryEdges).contains name
      let sentenceNamesMissing := representedSentenceNames.filter fun name =>
        !(hierarchyNames sentenceEdges).contains name
      IO.println s!"represented theory names absent from edges: {theoryNamesMissing.length}"
      for name in theoryNamesMissing do
        IO.eprintln s!"absent represented theory name: {name}"
      IO.println s!"represented sentence names absent from edges: {sentenceNamesMissing.length}"
      for name in sentenceNamesMissing do
        IO.eprintln s!"absent represented sentence name: {name}"
      return if parsed.errors.isEmpty && inventory.errors.isEmpty &&
          theoryValid && sentenceValid && theoryNamesMissing.isEmpty &&
          sentenceNamesMissing.isEmpty then 0 else 1

end Mettapedia.Ethics.SourceHierarchyCheck

unsafe def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] => Mettapedia.Ethics.SourceHierarchyCheck.checkFile path
  | _ =>
      IO.eprintln "usage: ethics-source-hierarchy-check <source.kif>"
      return 2
