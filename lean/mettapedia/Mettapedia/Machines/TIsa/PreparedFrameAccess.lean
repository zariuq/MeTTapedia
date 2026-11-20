import Mettapedia.Machines.TIsa.PreparedFrames

/-!
# Bounded access to a word activation

The capability, pointer register, and size of the metadata are inputs
to the load template. A slot is interpreted in the same convention that
licenses the frame.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.PreparedFrameAccess

open P1Source P1WordExecution

structure Convention where
  region : Region
  pointer : Reg
  metadata : Nat

structure FrameLayout (convention : Convention) (state : State) (offset width : Nat) : Prop where
  frames : Usable (state.regions convention.region) (offset + 8 * (convention.metadata + width))
  pointer : (state.registers convention.pointer).toNat =
    (state.regions convention.region).base.toNat + offset
  alignedOffset : offset % 8 = 0
  displacementFits : 8 * (convention.metadata + width) < 2^31

def frameAddress (convention : Convention) (state : State) (offset displacement : Nat) : Nat :=
  (state.regions convention.region).base.toNat + offset + displacement

theorem displacement_word (offset : Nat) (small : offset < 2^31) :
    (BitVec.ofNat 32 offset).toInt = (offset : Int) :=
  BitVec.toInt_ofInt_eq_self (w := 32) (by decide) (n := (offset : Int)) (by omega) (by omega)

theorem FrameLayout.access {convention : Convention} {state : State} {offset width : Nat}
    (layout : FrameLayout convention state offset width)
    (displacement : Nat) (aligned : displacement % 8 = 0)
    (ends : displacement + 8 ≤ 8 * (convention.metadata + width)) :
    QwordAccess (state.regions convention.region) (state.registers convention.pointer)
      (.ofNat 32 displacement) (frameAddress convention state offset displacement) := by
  have extent := layout.frames.enough
  have capAligned := layout.frames.aligned
  have offsetAligned := layout.alignedOffset
  have fits := layout.displacementFits
  refine ⟨layout.frames.fits, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [layout.pointer]; omega
  · rw [layout.pointer]; omega
  · unfold frameAddress
    omega
  · unfold frameAddress
    omega
  · rw [layout.pointer, displacement_word _ (by omega)]
    unfold frameAddress
    omega
  · unfold frameAddress
    omega

def load (convention : Convention) (destination : Reg) (displacement : Nat) : Stmt :=
  .instruction (.load .u64 .word64 convention.region destination convention.pointer (.ofNat 32 displacement))

theorem FrameLayout.loads {convention : Convention} {state : State} {offset width : Nat}
    (layout : FrameLayout convention state offset width)
    (destination : Reg) (displacement : Nat) (aligned : displacement % 8 = 0)
    (inside : displacement + 8 ≤ 8 * (convention.metadata + width)) (word : Word)
    (present : state.memory (frameAddress convention state offset displacement) = some word) :
    execute state (load convention destination displacement) = .continuing (state.write destination word) := by
  rw [load, execute, load_qword _ _ _ _ _ _ _
      (by rw [layout.frames.writable]; decide) (layout.access _ aligned inside) present]

def slotByte (convention : Convention) (slot : Nat) : Nat :=
  PreparedFrames.registerByte convention.metadata 0 slot

theorem FrameLayout.loadsSlot {convention : Convention} {state : State} {offset width : Nat}
    (layout : FrameLayout convention state offset width) (destination : Reg) (slot : Fin width)
    (word : Word) (present : state.memory (frameAddress convention state offset (slotByte convention slot)) =
      some word) :
    execute state (load convention destination (slotByte convention slot)) =
      .continuing (state.write destination word) :=
  layout.loads destination (slotByte convention slot)
    (PreparedFrames.registerByte_aligned convention.metadata slot)
    (PreparedFrames.registerByte_inside convention.metadata slot) word present

end Mettapedia.Machines.TIsa.PreparedFrameAccess
