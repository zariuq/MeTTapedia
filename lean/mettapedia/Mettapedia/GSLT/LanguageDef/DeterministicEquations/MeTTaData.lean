import Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataEquality
import Mettapedia.Languages.MeTTa.HE.Types

/-!
# Computational data in MeTTa atoms

Guest symbols, literals and variables are distinct tagged string values.
Expression and list spines are explicit constructor data. The round trip and
binding laws concern the existing MeTTa atom model; textual parsing and native
evaluation are separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)

mutual

def encode : Term → Atom
  | .sym name => .expression [.symbol "nik:Sym", .grounded (.string name)]
  | .lit text => .expression [.symbol "nik:Lit", .grounded (.string text)]
  | .var name => .expression [.symbol "nik:Var", .grounded (.string name)]
  | .expr items => .expression [.symbol "nik:Expr", encodeItems items]
  | .list items => .expression [.symbol "nik:List", encodeItems items]

def encodeItems : List Term → Atom
  | [] => .symbol "nik:Nil"
  | first :: rest => .expression [.symbol "nik:Cons", encode first, encodeItems rest]

end

mutual

def decode : Atom → Option Term
  | .expression [.symbol "nik:Sym", .grounded (.string name)] => some (.sym name)
  | .expression [.symbol "nik:Lit", .grounded (.string text)] => some (.lit text)
  | .expression [.symbol "nik:Var", .grounded (.string name)] => some (.var name)
  | .expression [.symbol "nik:Expr", items] => (decodeItems items).map Term.expr
  | .expression [.symbol "nik:List", items] => (decodeItems items).map Term.list
  | _ => none

def decodeItems : Atom → Option (List Term)
  | .symbol "nik:Nil" => some []
  | .expression [.symbol "nik:Cons", first, rest] => do
      let value ← decode first
      let values ← decodeItems rest
      pure (value :: values)
  | _ => none

end

mutual

@[simp] theorem decode_encode (term : Term) : decode (encode term) = some term := by
  cases term with
  | sym | lit | var => rfl
  | expr items => simp [encode, decode, decodeItems_encodeItems items]
  | list items => simp [encode, decode, decodeItems_encodeItems items]
termination_by sizeOf term

@[simp] theorem decodeItems_encodeItems (terms : List Term) :
    decodeItems (encodeItems terms) = some terms := by
  cases terms with
  | nil => rfl
  | cons first rest =>
      simp [encodeItems, decodeItems, decode_encode first, decodeItems_encodeItems rest]
termination_by sizeOf terms

end

theorem encode_injective : Function.Injective encode := by
  intro left right same
  have recovered := congrArg decode same
  simpa using recovered

theorem equality_reflects (left right : Term) :
    (encode left == encode right) = dataEqual left right := by
  apply Bool.eq_iff_iff.mpr
  simp [encode_injective.eq_iff, dataEqual_eq_true]

private theorem bindings_preserve_node (bindings : Bindings) (head : String)
    (arguments : List Atom)
    (stable : ∀ argument ∈ arguments, ∀ fuel, bindings.applyFull argument fuel = argument)
    (fuel : Nat) :
    bindings.applyFull (.expression (.symbol head :: arguments)) fuel =
      .expression (.symbol head :: arguments) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [Bindings.applyFull, List.map_cons]
      have headFixed : bindings.applyFull (.symbol head) fuel = .symbol head := by
        cases fuel <;> rfl
      rw [headFixed]
      congr 2
      calc
        arguments.map (bindings.applyFull · fuel) = arguments.map id :=
          List.map_congr_left (fun argument member => stable argument member fuel)
        _ = arguments := List.map_id arguments

mutual

/-- Even source variables are data: arbitrary target bindings cannot capture them. -/
theorem bindings_preserve_encode (bindings : Bindings) (term : Term) (fuel : Nat) :
    bindings.applyFull (encode term) fuel = encode term := by
  cases term with
  | sym name | lit name | var name =>
      apply bindings_preserve_node
      intro argument member fuel
      simp only [List.mem_singleton] at member
      subst argument
      cases fuel <;> rfl
  | expr items | list items =>
      apply bindings_preserve_node
      intro argument member fuel
      simp only [List.mem_singleton] at member
      subst argument
      exact bindings_preserve_items bindings items fuel
termination_by sizeOf term

theorem bindings_preserve_items (bindings : Bindings) (terms : List Term) (fuel : Nat) :
    bindings.applyFull (encodeItems terms) fuel = encodeItems terms := by
  cases terms with
  | nil => cases fuel <;> rfl
  | cons first rest =>
      apply bindings_preserve_node
      intro argument member fuel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact bindings_preserve_encode bindings first fuel
      · exact bindings_preserve_items bindings rest fuel
termination_by sizeOf terms

end

theorem encoded_data_is_not_empty (term : Term) : encode term ≠ Atom.empty := by
  cases term <;> simp [encode, Atom.empty]

theorem malformed_list_refused :
    decode (.expression [.symbol "nik:List", .symbol "Empty"]) = none := rfl

theorem callable_name_roundtrip :
    decode (encode (.expr [.sym "eval", .var "x"])) =
      some (.expr [.sym "eval", .var "x"]) := decode_encode _

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData
