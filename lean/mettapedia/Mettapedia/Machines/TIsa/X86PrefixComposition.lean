import Mettapedia.Machines.TIsa.X86BlockCompiler

/-! Prefix frames compose across the original counted fetch function. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86PrefixComposition
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

theorem append [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (registers : Finset Register) (first second : Nat) (before middle : State)
    (firstRun : (X86FuelPrefix.fetches first).run before = .ok () middle)
    (firstFrame : RegisterFrame registers before middle)
    (one : ∀ count ≤ first, ∀ reached, (X86FuelPrefix.fetches count).run before = .ok () reached →
      RegisterFrame registers before reached)
    (two : ∀ count ≤ second, ∀ reached, (X86FuelPrefix.fetches count).run middle = .ok () reached →
      RegisterFrame registers middle reached) :
    ∀ count ≤ first + second, ∀ reached, (X86FuelPrefix.fetches count).run before = .ok () reached →
      RegisterFrame registers before reached := by
  intro count within reached run
  by_cases inside : count ≤ first
  · exact one count inside reached run
  · have divided : count = first + (count - first) := by omega
    rw [divided] at run
    obtain ⟨actual,head,tail⟩ := X86BlockCompiler.fetches_split first (count - first) before reached run
    have same := X86FuelPrefix.fetches_deterministic first before actual middle head firstRun
    subst actual
    exact (firstFrame.trans (two (count - first) (by omega) reached tail)).mono (by simp)

#print axioms append

theorem append_frame [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (registers : Finset Register) (written : Finset Nat) (first second : Nat) (before middle : State)
    (firstRun : (X86FuelPrefix.fetches first).run before = .ok () middle)
    (firstFrame : X86StateFrame.Frame registers written before middle)
    (one : ∀ count ≤ first, ∀ reached, (X86FuelPrefix.fetches count).run before = .ok () reached →
      X86StateFrame.Frame registers written before reached)
    (two : ∀ count ≤ second, ∀ reached, (X86FuelPrefix.fetches count).run middle = .ok () reached →
      X86StateFrame.Frame registers written middle reached) :
    ∀ count ≤ first + second, ∀ reached, (X86FuelPrefix.fetches count).run before = .ok () reached →
      X86StateFrame.Frame registers written before reached := by
  intro count within reached run
  by_cases inside : count ≤ first
  · exact one count inside reached run
  · have divided : count = first + (count - first) := by omega
    rw [divided] at run
    obtain ⟨actual,head,tail⟩ := X86BlockCompiler.fetches_split first (count - first) before reached run
    have same := X86FuelPrefix.fetches_deterministic first before actual middle head firstRun
    subst actual
    exact (firstFrame.trans (two (count - first) (by omega) reached tail)).mono (by simp) (by simp)

#print axioms append_frame
end Mettapedia.Machines.TIsa.X86PrefixComposition
