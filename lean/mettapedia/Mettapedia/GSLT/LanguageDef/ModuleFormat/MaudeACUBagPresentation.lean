import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTermCodec
import Mettapedia.Languages.Maude.ACUFold

/-! A separate physical bag presentation for a declared Maude ACU carrier.
The raw tree codec remains unchanged. Reading a physical bag returns the
source fold; the round trip is source equivalence rather than tree equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagPresentation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def pack (wrapper : String) (parts : List Maude.Term) (rest : Option String := none) : Pattern :=
  .apply wrapper [.collection .hashBag (parts.map encode) rest]

def encodeBag {theory : Maude.Theory} {context : Maude.VariableContext}
    (operation : Maude.ACUOperation theory context) (wrapper : String) (source : Maude.Term) : Pattern :=
  pack wrapper (operation.flatten source)

def decodeBag? {theory : Maude.Theory} {context : Maude.VariableContext}
    (operation : Maude.ACUOperation theory context) (wrapper : String) : Pattern → Option Maude.Term
  | .apply label [.collection .hashBag parts none] =>
      if label = wrapper then (parts.mapM decode?).map operation.fold else none
  | _ => none

theorem decode_parts (parts : List Maude.Term) : (parts.map encode).mapM decode? = some parts := by
  induction parts with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, List.mapM_cons, decode_encode, ih]; rfl

theorem decode_pack {theory : Maude.Theory} {context : Maude.VariableContext}
    (operation : Maude.ACUOperation theory context) (wrapper : String) (parts : List Maude.Term) :
    decodeBag? operation wrapper (pack wrapper parts) = some (operation.fold parts) := by
  simp only [decodeBag?, pack, decode_parts, Option.map_some, if_true]

theorem source_roundtrip {theory : Maude.Theory} {context : Maude.VariableContext}
    (operation : Maude.ACUOperation theory context) (checked : theory.signature.check = true)
    (wrapper : String) (source : Maude.Term)
    (typed : Maude.HasSort theory.signature context source operation.declaration.result) :
    decodeBag? operation wrapper (encodeBag operation wrapper source) =
        some (operation.fold (operation.flatten source)) ∧
      Maude.Equivalent theory context operation.declaration.result source
        (operation.fold (operation.flatten source)) :=
  ⟨decode_pack operation wrapper _, operation.equivalent_fold_flatten checked typed⟩

#print axioms source_roundtrip

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagPresentation
