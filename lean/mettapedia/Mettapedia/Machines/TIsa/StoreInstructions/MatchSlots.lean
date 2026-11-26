import Mettapedia.Machines.TIsa.StoreInstructions.Execution
import Mettapedia.Machines.TIsa.X86PlacedQwordStore

/-!
# Native OPEN changes a match reference

A level holds one word selecting its match description. Code zero
selects the constructed empty match, including the matcher's own
initial binding value. OPEN can reset the level without touching old
payloads or an adjacent level.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.MatchSlots

open Derivation (Matcher Match)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (CodeApart Cell Reads footprint)
open X86BoundedStore (Instruction Fits layout bytes count physical displacement)
local instance : MemoryPrimitives := X86Memory.ordinary

universe u v w

structure Directory (n : ℕ) (V : Type v) (B : Type w) where
  addr : Fin n → BitVec 48
  records : Array (Match V B)

variable {T : Type u} {V : Type v} {B : Type w} {n : ℕ}

def book (matcher : Matcher T V B) (d : Directory n V B) : Array (Match V B) :=
  #[Match.start matcher] ++ d.records

def decode (matcher : Matcher T V B) (d : Directory n V B) (code : Word) : Option (Match V B) :=
  (book matcher d)[code.toNat]?

theorem decode_zero (matcher : Matcher T V B) (d : Directory n V B) :
    decode matcher d 0 = some (Match.start matcher) := by
  unfold decode book
  simp

def Represents (matcher : Matcher T V B) (d : Directory n V B) (native : X86RegisterRefinement.State)
    (levels : ℕ → Match V B) : Prop :=
  ∀ level : Fin n, ∃ handle, Reads native (d.addr level) handle ∧ decode matcher d handle = some (levels level.val)

def Apart (d : Directory n V B) (opened : Fin n) : Prop :=
  ∀ other : Fin n, other ≠ opened → Disjoint (footprint (d.addr other)) (footprint (d.addr opened))

theorem represents_update (matcher : Matcher T V B) (d : Directory n V B) {opened : Fin n}
    {native next : X86RegisterRefinement.State} {levels : ℕ → Match V B}
    {handle : Word} {selected : Match V B}
    {registers : Finset Register} (initial : Represents matcher d native levels)
    (frame : X86StateFrame.Frame registers (footprint (d.addr opened)) native next)
    (reset : Reads next (d.addr opened) handle) (decoded : decode matcher d handle = some selected)
    (apart : Apart d opened) :
    Represents matcher d next (Function.update levels opened.val selected) := by
  intro level
  by_cases same : level = opened
  · subst level
    refine ⟨handle, reset, ?_⟩
    rw [Function.update_self]
    exact decoded
  · obtain ⟨handle, bytes, value⟩ := initial level
    refine ⟨handle, bytes.preserved frame (apart level same), ?_⟩
    have others : level.val ≠ opened.val := fun equal => same (Fin.ext equal)
    rw [Function.update_of_ne others]
    exact value

theorem represents_open (matcher : Matcher T V B) (d : Directory n V B) {opened : Fin n}
    {native next : X86RegisterRefinement.State} {levels : ℕ → Match V B}
    {registers : Finset Register} (initial : Represents matcher d native levels)
    (frame : X86StateFrame.Frame registers (footprint (d.addr opened)) native next)
    (reset : Reads next (d.addr opened) 0) (apart : Apart d opened) :
    Represents matcher d next (Function.update levels opened.val (Match.start matcher)) :=
  represents_update matcher d initial frame reset (decode_zero matcher d) apart

theorem represents_memory (matcher : Matcher T V B) (d : Directory n V B)
    {native next : X86RegisterRefinement.State} {levels : ℕ → Match V B}
    (initial : Represents matcher d native levels) (same : next.mem = native.mem) :
    Represents matcher d next levels := by
  intro level
  obtain ⟨handle, stored, meaning⟩ := initial level
  exact ⟨handle, fun byte inside => by rw [same]; exact stored byte inside, meaning⟩

/-- A checked placed word store of the empty descriptor implements
OPEN. The packed store and the match descriptions are outside this
one level cell's footprint; they are not rewritten by the operation. -/
theorem lower_open_x86 [DecidableEq V] (matcher : Matcher T V B) (d : Directory n V B)
    (st : StoreInstructions.State V B) (opened : Fin n)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base : BitVec 48} {offset : ℕ}
    {code : Instruction} (point : At image native base offset)
    (checked : X86PlacedQwordStore.Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) (wide : code.wide = true)
    (inside : Fits (X86PlacedQwordStore.input point checked facts))
    (cell : Cell facts.pointer (displacement code)) (located : cell.address = d.addr opened)
    (zero : lookup native (physical code.source) = some 0)
    (outsideCode : CodeApart image base (footprint cell.address))
    (initial : Represents matcher d native st.levels) (apart : Apart d opened) :
    letI : OtherOpcodeHandlers := X86PlacedQwordStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ next abstract,
      (X86FuelPrefix.fetches (count code)).run native = .ok () next ∧
      executeInstruction matcher st (.transform (.open opened.val)) = .ok abstract ∧
      X86StateFrame.Frame X86Bounds.writes (footprint cell.address) native next ∧
      Represents matcher d next abstract.levels ∧
      Nonempty (At image next base (offset + (bytes code).length)) := by
  obtain ⟨next, fetched, frame, reset, continuation⟩ :=
    X86PlacedQwordStore.writes other extra vector point checked facts wide inside 0 cell zero outsideCode
  refine ⟨next, st.setLevel opened.val (Match.start matcher), fetched, rfl, frame, ?_, continuation⟩
  exact represents_open matcher d initial (located ▸ frame) (located ▸ reset) apart

namespace Examples

private def addBinding : Matcher Unit ℕ ℕ :=
  ⟨5, fun binding _ value => some (binding + value), fun binding _ => some binding⟩

private def oldAttempt : Match ℕ ℕ := ⟨12, [7], [9], [], [42]⟩
private def slot : Directory 1 ℕ ℕ := ⟨fun _ => 512, #[oldAttempt]⟩

theorem empty_descriptor_keeps_matcher_initial_value :
    (decode addBinding slot 0).map (fun found => (found.bindings, found.taken, found.made)) =
      some (5, [], []) := by decide +kernel

theorem stale_reference_is_not_a_reset :
    (decode addBinding slot 1).map Match.taken = some [7] ∧
      (decode addBinding slot 0).map Match.taken = some [] := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.MatchSlots
