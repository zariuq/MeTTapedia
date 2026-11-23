import Lean.Elab.Command

/-! Character views select consecutive slices. Chunk boundaries reconstruct the
named lists used by the source checkers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceCharacterViews

open Lean Elab Command

private def indexLabel (index : Nat) : String :=
  let digits := toString index
  String.ofList (List.replicate (3 - digits.length) '0') ++ digits

private def slices (anchor : Syntax) (first size : Nat) : Array (TSyntax `term) :=
  ((List.range' first size).map fun index =>
    ⟨(mkIdentFrom anchor (Name.mkSimple ("sourceSlice_" ++ indexLabel index))).raw⟩).toArray

/-- Each cut ends a chunk. The starting offset and cuts are slice indices. -/
syntax (name := characterView) "source_character_view " ident " from " num " cuts " "[" num,* "]" :
  command

elab_rules : command
  | `(command| source_character_view $name:ident from $first:num cuts [$ends:num,*]) => do
      let mut start := first.getNat
      let mut chunks : Array (TSyntax `term) := #[]
      let mut blocks : Array (TSyntax `term) := #[]
      for (cut, index) in ends.getElems.zipIdx do
        unless start < cut.getNat do
          throwErrorAt cut "expected a later slice cut"
        let chunk := mkIdentFrom name (name.getId.appendAfter ("_" ++ indexLabel index))
        let block := mkIdentFrom name (name.getId.appendAfter ("Block_" ++ indexLabel index))
        let pieces := slices name start (cut.getNat - start)
        elabCommand (← `(private def $block : List (List Char) := [$pieces,*]))
        elabCommand (← `(def $chunk : List Char := ($block).flatten))
        chunks := chunks.push ⟨chunk.raw⟩
        blocks := blocks.push ⟨block.raw⟩
        start := cut.getNat
      let allBlocks := mkIdentFrom name (name.getId.appendAfter "Blocks")
      let allSlices := mkIdentFrom name (name.getId.appendAfter "Slices")
      let assembled := mkIdentFrom name (name.getId.appendAfter "FromSlices")
      elabCommand (← `(private def $allBlocks : List (List (List Char)) := [$blocks,*]))
      elabCommand (← `(private def $allSlices : List (List Char) := ($allBlocks).flatten))
      elabCommand (← `(def $name : List Char := ([$chunks,*] : List (List Char)).flatten))
      elabCommand (← `(private theorem $assembled : $name = ($allSlices).flatten :=
        (List.flatten_flatten (L := $allBlocks)).symm))


end Mettapedia.GSLT.Parsing.SourceCharacterViews
