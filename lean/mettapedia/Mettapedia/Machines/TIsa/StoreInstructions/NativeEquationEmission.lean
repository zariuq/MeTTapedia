import Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationEffect

/-! # Emitting the operand loads and equation stores -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationEmission

open X86PlacedScalar (Code)
open NativeEquationInputs (Operands previousWire leftWire rightWire)
open NativeEquationEffect (Destination)
open PackedEquations (Arena Node)

variable {slot candidate : Word} {capacity : ℕ} {arena : Arena}

def loads (input : Operands slot candidate) : List ℕ :=
  input.previous.source.bytes previousWire ++ (input.left.bytes leftWire ++ input.right.bytes rightWire)

theorem load_size (input : Operands slot candidate) : (loads input).length = input.width := by
  simp only [loads, List.length_append, NativeWords.Source.bytes_length, Operands.width, NativeRoleGate.WordAt.source,
    NativeWords.Source.width, Nat.add_assoc]

def stores (layout : Destination capacity arena) (node : Node) : List ℕ :=
  NativeStores.emitted layout.encoding (layout.moves node) ++ layout.root.bytes layout.rootEncoding

theorem store_size (layout : Destination capacity arena) (node : Node) :
    (stores layout node).length = layout.width := by
  simp only [stores, List.length_append, NativeStores.emitted_size, NativeStores.Write.byte_length, Destination.width,
    Destination.moves, NativeEquationAppend.width]

theorem same_bytes_for_other_node (layout : Destination capacity arena) (left right : Node) :
    stores layout left = stores layout right := by
  simp only [stores, NativeStores.emitted, Destination.moves, NativeEquationAppend.instructions, List.flatMap_map,
    NativeStores.Write.bytes, NativeEquationAppend.word]

def emit (input : Operands slot candidate) (layout : Destination capacity arena) (node : Node) : List ℕ :=
  loads input ++ stores layout node

theorem size (input : Operands slot candidate) (layout : Destination capacity arena) (node : Node) :
    (emit input layout node).length = input.width + layout.width := by
  simp only [emit, List.length_append, load_size, store_size]

theorem checked_input (input : Operands slot candidate) (image : NativeImage.View) (start : ℕ)
    (inside : start + input.width ≤ image.size) (installed : Code image start (loads input)) :
    input.Checked image start := by
  obtain ⟨previous, rest⟩ := NativeWords.code_append (show Code image start
    (input.previous.source.bytes previousWire ++ (input.left.bytes leftWire ++ input.right.bytes rightWire)) from installed)
  rw [NativeWords.Source.bytes_length] at rest
  obtain ⟨left, right⟩ := NativeWords.code_append rest
  rw [NativeWords.Source.bytes_length] at right
  exact ⟨inside, previous, left, right⟩

theorem checked_destination (layout : Destination capacity arena) (node : Node) (image : NativeImage.View) (start : ℕ)
    (inside : start + layout.width ≤ image.size) (installed : Code image start (stores layout node)) :
    layout.Placed node image start := by
  obtain ⟨privateCode, publishCode⟩ := NativeWords.code_append (show Code image start
    (NativeStores.emitted layout.encoding (layout.moves node) ++ layout.root.bytes layout.rootEncoding) from installed)
  have length : (NativeStores.emitted layout.encoding (layout.moves node)).length = 3 * layout.encoding.length := by
    rw [NativeStores.emitted_size, Destination.moves, NativeEquationAppend.width]
  rw [length] at publishCode
  have many : start + (NativeStores.emitted layout.encoding (layout.moves node)).length ≤ image.size := by
    rw [length]
    unfold Destination.width at inside
    omega
  exact ⟨NativeStores.checked_of_emitted layout.encoding image start (layout.moves node) many privateCode,
    by simpa only [Destination.width, Nat.add_assoc] using inside, publishCode⟩

theorem checked_of_emitted (input : Operands slot candidate) (layout : Destination capacity arena)
    (node : Node) (image : NativeImage.View) (start : ℕ)
    (inside : start + (emit input layout node).length ≤ image.size)
    (installed : Code image start (emit input layout node)) :
    input.Checked image start ∧ layout.Placed node image (start + input.width) := by
  obtain ⟨read, append⟩ := NativeWords.code_append (show Code image start
    (loads input ++ stores layout node) from installed)
  rw [load_size] at append
  rw [size] at inside
  exact ⟨checked_input input image start (by omega) read,
    checked_destination layout node image (start + input.width) (by omega) append⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationEmission
