import Lean.Elab.Command
import Mettapedia.Data.List.AdjacentCheck

/-! Declare an exact table of consecutive chunks and prove that the projected
labels of its flattening are strictly increasing. Each leaf and join is a
separate kernel-checked declaration. -/

set_option autoImplicit false

namespace Mettapedia.Data.List.LabelChunkProof

open Lean Elab Command

private structure CheckedTable where
  chunks : Term
  first : Term
  last : Term
  proof : Term
  deriving Inhabited

private def issue (chunks first last evidence : Term) : CommandElabM CheckedTable := do
  let name := mkIdent (← liftCoreM (mkFreshUserName `labelOrder))
  elabCommand (← `(private theorem $name :
    OrderedChunks (fun left right : String => left < right) $chunks $first $last := $evidence))
  pure ⟨chunks, first, last, ⟨name.raw⟩⟩

private def verifyChunk (projection chunk : Term) : CommandElabM CheckedTable := do
  let labels ← `(List.map $projection $chunk)
  issue (← `([$labels])) (← `(List.head $labels (by decide +kernel)))
    (← `(List.getLast $labels (by decide +kernel))) (← `(OrderedChunks.single
      (relation := fun left right : String => left < right) $labels (by decide +kernel) (by decide +kernel)))

private def merge (left right : CheckedTable) : CommandElabM CheckedTable := do
  issue (← `($(left.chunks) ++ $(right.chunks))) left.first right.last
    (← `(OrderedChunks.append $(left.proof) $(right.proof) (by decide +kernel)))

/-- Supply the original chunks in order and a projection to their labels. -/
syntax (name := certifiedLabelChunks) "certified_label_chunks " ident " as " ident
  " via " term " from " "[" term,+ "]" : command

elab_rules : command
  | `(command| certified_label_chunks $table:ident as $ordered:ident via $project:term from [$chunks:term,*]) => do
      elabCommand (← `(private def $table := [$chunks,*]))
      let mut proofs : Array CheckedTable := #[]
      for chunk in chunks.getElems do
        proofs := proofs.push (← verifyChunk project chunk)
      while proofs.size > 1 do
        let mut joined := #[]
        for index in [:proofs.size / 2] do
          let left := proofs[2 * index]!
          let right := proofs[2 * index + 1]!
          joined := joined.push (← merge left right)
        if proofs.size % 2 = 1 then
          joined := joined.push proofs.back!
        proofs := joined
      let proof := proofs[0]!.proof
      elabCommand (← `(private theorem $ordered :
          List.IsChain (fun left right : String => left < right)
            (List.map (List.map $project) $table).flatten := by
        change List.IsChain (fun left right : String => left < right)
          (List.map (List.map $project) [$chunks,*]).flatten
        simpa only [List.map_cons, List.map_nil, List.append_assoc, List.nil_append,
          List.append_nil, List.cons_append] using ($proof).segment.ordered))

end Mettapedia.Data.List.LabelChunkProof
