import Mettapedia.Machines.TIsa.X86MemoryBounds
import Mettapedia.Machines.TIsa.X86BoundsPrefixes

/-!
# Source bounds failures realized by the original native checker

A genuine readonly failure firing supplies descriptor membership and the
failed access guard. Only its observed source cells, the ABI frame pointer
and the architectural entry facts are needed. No destination byte or payload
register observation is required. Native rejection preserves every source
readback, all memory and the architectural profile at every fetched prefix.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86MemoryFailure
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView
local instance : MemoryPrimitives := X86Memory.ordinary

def recipe (write : Bool) (width : P1Source.Width) (layout : X86Bounds.Layout) (pointer : Fin 12) : CellEffects.Recipe Key :=
  P1Memory.boundsFailureRecipe write width layout.region.val pointer
    (X86PositiveImmediate.immediate32 layout.offset).toInt

def count (layout : X86Bounds.Layout) (pointer : Fin 12) (values : Key → Word) : Nat :=
  X86Bounds.boundsSteps layout (values (.capabilityBase layout.region.val))
    (values (.register pointer)) (values (.capabilityLength layout.region.val))

structure Entry (layout : X86Bounds.Layout) (pointer : Fin 12) (keys : Finset Key)
    (modes : Fin 9 → Word) (values : Key → Word) (native : State) where
  origin : X86LegacyFetch.Basis native
  profile : X86Readiness.Profile
  flags : BitVec 32
  mapped : layout.pointer = placed (Registers.canonical .x86_64)
    (Registers.canonical_admitted .x86_64) (Registers.logicalSlot pointer)
  known : ∀ key ∈ keys, readback modes native key = some (values key)
  frameKnown : readback modes native (.register 0) = some (values (.register 0))
  frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size
  frameAligned : (values (.register 0)).toNat % 8 = 0
  holds : profile.Holds native
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  geometry : X86Bounds.Context layout origin.address
  loaded : codeLoaded native origin.address.toInt (X86Bounds.code layout)
  rangeFits : (values (.capabilityBase layout.region.val)).toNat +
    (values (.capabilityLength layout.region.val)).toNat < 2 ^ 64

theorem source_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (write : Bool) (width : P1Source.Width) (layout : X86Bounds.Layout) (pointer : Fin 12)
    (sized : width.bytes = layout.count.val) (keys : Finset Key) (modes : Fin 9 → Word)
    (values : Key → Word) (native : State) (entry : Entry layout pointer keys modes values native)
    (following : World)
    (source : (CellEffects.profile [recipe write width layout pointer]).theory.rewrites (Cells.encode keys values) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    following = Cells.encode keys values ∧
    ∃ after nextFlags, (X86FuelPrefix.fetches (count layout pointer values)).run native = .ok () after ∧
      RegisterFrame X86Bounds.writes native after ∧
      (∀ key, readback modes after key = readback modes native key) ∧
      after.regs.get? .rip = some ((X86Bounds.position entry.origin.address layout.reject).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
      ∀ prefixCount ≤ count layout pointer values, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame X86Bounds.writes native observed := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨included,_mode,access,endpoint⟩ :=
    (P1Memory.bounds_failure_rewrite_iff write width layout.region.val pointer
      (X86PositiveImmediate.immediate32 layout.offset).toInt keys values following).mp source
  have present (key : Key) (member : key ∈ (recipe write width layout pointer).inputs) : key ∈ keys := by
    apply included
    exact Finset.mem_union_right _ (by simpa only [recipe,List.mem_toFinset] using member)
  have basePresent : Memory.Key.capabilityBase layout.region.val ∈ keys :=
    present _ (by simp [recipe,P1Memory.boundsFailureRecipe,Memory.capabilityKeys])
  have lengthPresent : Memory.Key.capabilityLength layout.region.val ∈ keys :=
    present _ (by simp [recipe,P1Memory.boundsFailureRecipe,Memory.capabilityKeys])
  have pointerPresent : Memory.Key.register pointer ∈ keys :=
    present _ (by simp [recipe,P1Memory.boundsFailureRecipe])
  let facts := X86MemoryBounds.facts_observed modes values native layout pointer entry.profile entry.flags entry.mapped
    entry.frameKnown (entry.known _ pointerPresent) (entry.known _ basePresent) (entry.known _ lengthPresent)
    entry.frameArea entry.frameAligned entry.holds entry.flagsKnown entry.quiet
  let input : X86Bounds.Inputs layout native entry.origin := ⟨facts,entry.geometry,entry.loaded⟩
  obtain ⟨after,run,frame,rip,control⟩ := X86Bounds.classifies_control other extra vector layout native entry.origin input
  have failed : Memory.access? input.base input.length input.pointer
      (X86PositiveImmediate.immediate32 layout.offset).toInt layout.count.val = none := by
    simpa only [input, facts, X86MemoryBounds.facts_observed, X86MemoryBounds.facts_at, sized] using access
  have rangeFits : input.base.toNat + input.length.toNat < 2 ^ 64 := by
    simpa only [input, facts, X86MemoryBounds.facts_observed, X86MemoryBounds.facts_at] using entry.rangeFits
  have notFits : ¬ (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat := by
    intro fits
    have accepted := X86BoundsArithmetic.access_of_fits input.base input.length input.pointer layout.offset layout.count rangeFits fits
    rw [failed] at accepted
    contradiction
  rw [if_neg notFits] at rip
  obtain ⟨nextFlags,flagsRead⟩ := X86ControlFlags.flags_present control entry.flags entry.flagsKnown
  refine ⟨endpoint,after,nextFlags,run,frame,X86MemoryBounds.bounds_preserves_readback modes native after frame,rip,
    flagsRead,(frame.registers .log_register_writes (by decide)).trans entry.quiet,control,
    entry.profile.after_control native after _ _ (X86StateFrame.registerOnly frame) X86Bounds.writes_data
      control ⟨nextFlags,flagsRead⟩ entry.holds,?_⟩
  exact X86Bounds.execution_prefix_frame other extra vector layout native entry.origin input

#print axioms source_executes
end Mettapedia.Machines.TIsa.X86MemoryFailure
