import Mettapedia.Machines.TIsa.X86PlacedScalar
import Mettapedia.Machines.TIsa.X86LoopEntry

/-! # The checked first iteration of a prepared loop -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

namespace Mettapedia.Machines.TIsa.X86PlacedLoopStart

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code handlers)

local instance : MemoryPrimitives := X86Memory.ordinary

structure Site where
  start : Nat
  capacity : BitVec 32
  overCap : Nat
  stop : Nat

def Site.capDelta (site : Site) : BitVec 32 := .ofInt 32 ((site.overCap : Int) - (site.start + 15))
def Site.stopDelta (site : Site) : BitVec 32 := .ofInt 32 ((site.stop : Int) - (site.start + 36))

def Checked (image : NativeImage.View) (site : Site) : Prop :=
  site.start + 36 ≤ image.size ∧ site.overCap ≤ image.size ∧ site.stop ≤ image.size ∧
  (site.overCap : Int) = site.start + 15 + site.capDelta.toInt ∧
  (site.stop : Int) = site.start + 36 + site.stopDelta.toInt ∧
  Code image site.start (X86LoopEntry.code 11 0 site.capacity site.capDelta) ∧
  X86PlacedScalar.CompareBranch image (site.start + 18) site.stop .lessUnsigned 11 0 ∧
  Code image (site.start + 27) (X86BranchGate.code 10 site.stopDelta)

instance (image : NativeImage.View) (site : Site) : Decidable (Checked image site) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev writes : Finset Register := X86LoopEntry.writes 11

theorem begins (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : State} {base : BitVec 48} {site : Site}
    (point : At image native base site.start) (checked : Checked image site)
    (index limit : Word) (old : lookup native 11 = some index) (bound : lookup native 0 = some limit)
    (enabled : lookup native 10 = some 1) (positive : 0 < limit.toNat) (fits : limit.toNat ≤ site.capacity.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run native = .ok () after ∧
      RegisterFrame writes native after ∧ lookup after 11 = some 0 ∧
      lookup after 0 = some limit ∧ Nonempty (At image after base (site.start + 36)) := by
  let h := handlers other extra
  obtain ⟨extent, capInside, stopInside, capExact, stopExact, prefixCode, indexCode, enabledCode⟩ := checked
  let start : X86LoopEntry.Inputs native 11 0 :=
    { toBasis := point.basis (by omega)
      indexValue := index
      boundValue := limit
      cap := site.capacity
      flags := point.flags
      indexKnown := old
      boundKnown := bound
      flagsKnown := point.knownFlags
      quiet := point.quiet
      separateIndex := by decide
      separateBound := by decide
      distinct := by decide
      upper := by
        change (address base.toInt site.start).toInt + 18 < (2^47 : Int)
        rw [point.location site.start (by omega)]
        have := point.upper
        omega
      displacement := site.capDelta
      target := address base.toInt site.overCap
      jump := by
        change (address base.toInt site.overCap).toInt = (address base.toInt site.start).toInt + 15 + site.capDelta.toInt
        rw [point.location site.overCap capInside, point.location site.start (by omega)]
        omega
      loaded := point.bytes _ (by omega) _ prefixCode }
  obtain ⟨cleared, flags, began, initialized, zero, retained, flagsKnown, rip, _⟩ :=
    X86LoopEntry.executes_control h extra vector native 11 0 start
  change (@X86FuelPrefix.fetches h vector (if limit.toNat ≤ site.capacity.toNat then 4 else 3)).run native =
    .ok () cleared at began
  change lookup cleared 11 = some (if limit.toNat ≤ site.capacity.toNat then 0 else index) at zero
  change cleared.regs.get? .rip = some
    ((if limit.toNat ≤ site.capacity.toNat then address (address base.toInt site.start).toInt 18
      else address base.toInt site.overCap).signExtend 64) at rip
  rw [if_pos fits] at began zero rip
  rw [point.relative_address _ _ (by omega)] at rip
  let atIndex := point.advance initialized (X86LoopEntry.writes_data 11) rip flags flagsKnown
  have passes : Comparison.lessUnsigned.evaluate (0#64) limit = true := by
    simp only [Comparison.evaluate, BitVec.lt_def, decide_eq_true_eq]
    exact positive
  obtain ⟨allowed, indexRun, indexFrame, ⟨atEnabled⟩⟩ :=
    X86PlacedScalar.compare_branch other extra vector atIndex .lessUnsigned 11 0 indexCode 0 limit zero retained
  have landing : (if Comparison.lessUnsigned.evaluate (0#64) limit then site.start + 18 + 9 else site.stop) =
      site.start + 27 := by rw [if_pos passes]
  have testAt : At image allowed base (site.start + 27) := landing ▸ atEnabled
  let clearAndCheck := initialized.trans indexFrame
  let gate : X86BranchGate.Inputs allowed 10 :=
    { toBasis := testAt.basis (by omega)
      value := 1
      flags := testAt.flags
      valueKnown := (clearAndCheck.lookup 10 (by decide)).trans enabled
      flagsKnown := testAt.knownFlags
      quiet := testAt.quiet
      upper := by
        change (address base.toInt (site.start + 27)).toInt + 9 < (2^47 : Int)
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      displacement := site.stopDelta
      target := address base.toInt site.stop
      jump := by
        change (address base.toInt site.stop).toInt =
          (address base.toInt (site.start + 27)).toInt + 9 + site.stopDelta.toInt
        rw [point.location site.stop stopInside, point.location _ (by omega)]
        omega
      loaded := testAt.bytes _ (by omega) _ enabledCode }
  obtain ⟨after, finalFlags, tested, testFrame, _, finalKnown, finalRip⟩ :=
    X86BranchGate.executes h extra vector allowed 10 gate
  change after.regs.get? .rip = some ((if (1#64) = (0#64) then address base.toInt site.stop
    else address (address base.toInt (site.start + 27)).toInt 9).signExtend 64) at finalRip
  rw [if_neg (by decide : (1#64) ≠ (0#64)), point.relative_address _ _ (by omega),
    show site.start + 27 + 9 = site.start + 36 by omega] at finalRip
  have ran := @X86FuelPrefix.fetches_then h vector 4 2 native cleared allowed began indexRun
  refine ⟨after, @X86FuelPrefix.fetches_then h vector 6 2 native allowed after ran tested,
    (clearAndCheck.trans testFrame).mono (by decide),
    ((indexFrame.trans testFrame).lookup 11 (by decide)).trans zero,
    ((indexFrame.trans testFrame).lookup 0 (by decide)).trans retained,
    ⟨testAt.advance testFrame X86BranchGate.writes_data finalRip finalFlags finalKnown⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedLoopStart

