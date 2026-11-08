import Mettapedia.Languages.Lean.Declarations.BlockProfile
import Mettapedia.Languages.Lean.Declarations.ReaderControls
import Mettapedia.Machines.FunctionalCorrespondence

/-!
# Source-derived tagged-block admission controls

The inventories are produced from the actual Lean declarations. These tests
check members, constructor origins, recursor order, dependent indices and
erasure. Equivalences with the source carriers are separate theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.BlockControls

open _root_.Lean _root_.Lean.Meta
open Mettapedia.Machines

def cek : BlockReading := lean_block% CEK.Val
def krivine : BlockReading := lean_block% Krivine.NThunk
def tree : BlockReading := lean_block% Controls.Tree
def parity : BlockReading := lean_block% Controls.Even
def rose : BlockReading := lean_block% Controls.Rose

def count (block : BlockReading) : Option Nat :=
  ((BlockProfile.admit Profile.Model.syntactic block).toOption).map (·.constructors.length)

theorem cek_is_admitted : count cek = some 4 := rfl
theorem krivine_is_admitted : count krivine = some 3 := rfl
theorem tree_is_admitted : count tree = some 3 := rfl
theorem parity_is_admitted : count parity = some 3 := rfl

theorem cek_member_sources : cek.members.map (·.source) =
    [.name "Mettapedia.Machines.CEK.Val",
     .app (.name "List") (.name "Mettapedia.Machines.CEK.Val")] := rfl

theorem cek_constructor_origins : cek.origins.map (·.source) =
    ["Mettapedia.Machines.CEK.Val.lit", "Mettapedia.Machines.CEK.Val.clo", "List.nil", "List.cons"] := rfl

theorem cek_motive_order : cek.recursors.map (·.motives) = [[0, 1]] := rfl

theorem cek_minor_order : cek.recursors.map (·.minors) =
    [["Mettapedia.Machines.CEK.Val.lit", "Mettapedia.Machines.CEK.Val.clo",
      "Mettapedia.Machines.CEK.Val._nested_1.nil", "Mettapedia.Machines.CEK.Val._nested_1.cons"]] := rfl

theorem parity_retains_indices : parity.members.map (fun member => member.reading.family.indices.length) =
    [1, 1] := rfl

theorem recursive_function_field_refused :
    (BlockProfile.admit Profile.Model.syntactic rose).toOption = none := rfl

theorem cek_fields_preserved : (BlockProfile.inventoryKept cek).map (·.map Prod.snd) =
    some [[true], [true, true], [], [true, true]] := rfl

theorem parity_proofs_erased : (BlockProfile.inventoryKept parity).map (·.map Prod.snd) =
    some [[], [true, false], [true, false]] := rfl

inductive NestedFunction where
  | node (children : Nat → List NestedFunction) : NestedFunction

def nestedFunction : BlockReading := lean_block% NestedFunction

theorem nested_function_field_refused :
    (BlockProfile.admit Profile.Model.syntactic nestedFunction).toOption = none := rfl

inductive UnknownContainer where
  | node : Option UnknownContainer → UnknownContainer

/- The runtime reader must identify the unsupported container by name. -/
#guard_msgs in
#eval show MetaM Unit from do
  match ← readBlock ``UnknownContainer with
  | .error (.unknownContainer owner container) =>
      unless owner == (``UnknownContainer).toString do throwError "wrong refusal owner"
      unless container == "Option" do throwError "wrong container: {container}"
  | .error reason => throwError "wrong refusal: {repr reason}"
  | .ok _ => throwError "unregistered container was admitted"

end Mettapedia.Languages.Lean.Declarations.BlockControls
