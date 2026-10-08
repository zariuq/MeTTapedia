import Mettapedia.Machines.OrderedDependencyCPreparationSource
import Mettapedia.Machines.OrderedDependencyCPreparationTokens
import Mettapedia.GSLT.LanguageDef.NativeOpsCBodyTextAgreement

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

open private reserve0 reserve1 reserve2 reserve3 reserve4 reserve5 reserve6 preparation0 preparation1 preparation2 preparation3 preparation4 preparation5 preparation6 preparation7 preparation8 preparation9 preparation10 preparation11 preparation12 preparation13 preparation14 preparation15 preparation16 from Mettapedia.Machines.OrderedDependencyCPreparationTokens

private theorem reserve_source_characters : reserveSource.toList = native_c_characters% reserveSource :=
  String.toList_ofList

private theorem reserve0_characters : reserve0.1.toList = native_c_characters% reserve0.1 :=
  String.toList_ofList

private theorem reserve1_characters : reserve1.1.toList = native_c_characters% reserve1.1 :=
  String.toList_ofList

private theorem reserve2_characters : reserve2.1.toList = native_c_characters% reserve2.1 :=
  String.toList_ofList

private theorem reserve3_characters : reserve3.1.toList = native_c_characters% reserve3.1 :=
  String.toList_ofList

private theorem reserve4_characters : reserve4.1.toList = native_c_characters% reserve4.1 :=
  String.toList_ofList

private theorem reserve5_characters : reserve5.1.toList = native_c_characters% reserve5.1 :=
  String.toList_ofList

private theorem reserve6_characters : reserve6.1.toList = native_c_characters% reserve6.1 :=
  String.toList_ofList

private theorem reserve_text_exact : String.join (reservePieces.map Prod.fst) = reserveSource := by
  apply String.toList_inj.mp
  rw [String.toList_join, reserve_source_characters]
  simp only [reservePieces, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [reserve0_characters, reserve1_characters, reserve2_characters, reserve3_characters, reserve4_characters, reserve5_characters, reserve6_characters]
  rfl

private theorem preparation_source_characters : preparationSource.toList = native_c_characters% preparationSource :=
  String.toList_ofList

private theorem preparation0_characters : preparation0.1.toList = native_c_characters% preparation0.1 :=
  String.toList_ofList

private theorem preparation1_characters : preparation1.1.toList = native_c_characters% preparation1.1 :=
  String.toList_ofList

private theorem preparation2_characters : preparation2.1.toList = native_c_characters% preparation2.1 :=
  String.toList_ofList

private theorem preparation3_characters : preparation3.1.toList = native_c_characters% preparation3.1 :=
  String.toList_ofList

private theorem preparation4_characters : preparation4.1.toList = native_c_characters% preparation4.1 :=
  String.toList_ofList

private theorem preparation5_characters : preparation5.1.toList = native_c_characters% preparation5.1 :=
  String.toList_ofList

private theorem preparation6_characters : preparation6.1.toList = native_c_characters% preparation6.1 :=
  String.toList_ofList

private theorem preparation7_characters : preparation7.1.toList = native_c_characters% preparation7.1 :=
  String.toList_ofList

private theorem preparation8_characters : preparation8.1.toList = native_c_characters% preparation8.1 :=
  String.toList_ofList

private theorem preparation9_characters : preparation9.1.toList = native_c_characters% preparation9.1 :=
  String.toList_ofList

private theorem preparation10_characters : preparation10.1.toList = native_c_characters% preparation10.1 :=
  String.toList_ofList

private theorem preparation11_characters : preparation11.1.toList = native_c_characters% preparation11.1 :=
  String.toList_ofList

private theorem preparation12_characters : preparation12.1.toList = native_c_characters% preparation12.1 :=
  String.toList_ofList

private theorem preparation13_characters : preparation13.1.toList = native_c_characters% preparation13.1 :=
  String.toList_ofList

private theorem preparation14_characters : preparation14.1.toList = native_c_characters% preparation14.1 :=
  String.toList_ofList

private theorem preparation15_characters : preparation15.1.toList = native_c_characters% preparation15.1 :=
  String.toList_ofList

private theorem preparation16_characters : preparation16.1.toList = native_c_characters% preparation16.1 :=
  String.toList_ofList

private theorem preparation_text_exact : String.join (preparationPieces.map Prod.fst) = preparationSource := by
  apply String.toList_inj.mp
  rw [String.toList_join, preparation_source_characters]
  simp only [preparationPieces, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [preparation0_characters, preparation1_characters, preparation2_characters, preparation3_characters, preparation4_characters, preparation5_characters, preparation6_characters, preparation7_characters, preparation8_characters, preparation9_characters, preparation10_characters, preparation11_characters, preparation12_characters, preparation13_characters, preparation14_characters, preparation15_characters, preparation16_characters]
  rfl


theorem reserve_lexer_exact : lex reserveSource.toList = .ok reserveTokens := by
  rw [← reserve_text_exact]
  exact reserve_lexed

theorem preparation_lexer_exact : lex preparationSource.toList = .ok preparationTokens := by
  rw [← preparation_text_exact]
  exact preparation_lexed

theorem reserve_tokens_admitted : functionUsing? (declaratorParameter? typeNames)
    (2 * reserveTokens.length + 4) typeNames (ordinaryFunctionTokens reserveTokens) =
    some (reserveFunction, []) := by native_c_parser_reflexivity

theorem preparation_tokens_admitted : functionUsing? (declaratorParameter? typeNames)
    (2 * preparationTokens.length + 4) typeNames (ordinaryFunctionTokens preparationTokens) =
    some (preparationFunction, []) := by native_c_parser_reflexivity

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
