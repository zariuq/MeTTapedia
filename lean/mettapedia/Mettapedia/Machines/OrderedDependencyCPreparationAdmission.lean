import Mettapedia.Machines.OrderedDependencyCPreparationSource
import Mettapedia.Machines.OrderedDependencyCPreparationTokens

/-!
# Complete recognition of the actual dependency preparation

Lexer pieces are checked separately and then composed. Token recognition is
compared with an independently authored syntax tree, preserving the complete
capacity and preparation functions rather than projecting their signatures.
These are source-admission laws, not heap or allocator refinement laws.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace Mettapedia.Machines.OrderedDependencyCPreparationSource

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open OrderedDependencyCPreparationTokens

theorem reserve_lexer_exact : lex reserveSource.toList = .ok reserveTokens := by
  have text : String.join (reservePieces.map Prod.fst) = reserveSource := by decide +kernel
  rw [← text]
  exact reserve_lexed

theorem preparation_lexer_exact : lex preparationSource.toList = .ok preparationTokens := by
  have text : String.join (preparationPieces.map Prod.fst) = preparationSource := by decide +kernel
  rw [← text]
  exact preparation_lexed

theorem reserve_tokens_admitted : functionUsing? (declaratorParameter? typeNames)
    (2 * reserveTokens.length + 4) typeNames (ordinaryFunctionTokens reserveTokens) =
    some (reserveFunction, []) := by rfl

theorem preparation_tokens_admitted : functionUsing? (declaratorParameter? typeNames)
    (2 * preparationTokens.length + 4) typeNames (ordinaryFunctionTokens preparationTokens) =
    some (preparationFunction, []) := by rfl

theorem complete_reserve_source_admitted : declaratorFunctionText? typeNames
    reserveSource.toList = some reserveFunction :=
  function_text_using_of_parts _ _ _ _ _ reserve_lexer_exact reserve_tokens_admitted

theorem complete_preparation_source_admitted : declaratorFunctionText? typeNames
    preparationSource.toList = some preparationFunction :=
  function_text_using_of_parts _ _ _ _ _ preparation_lexer_exact preparation_tokens_admitted

#print axioms reserve_lexer_exact
#print axioms preparation_lexer_exact
#print axioms reserve_tokens_admitted
#print axioms preparation_tokens_admitted
#print axioms complete_reserve_source_admitted
#print axioms complete_preparation_source_admitted

end Mettapedia.Machines.OrderedDependencyCPreparationSource
