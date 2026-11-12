import Mettapedia.Machines.TIsa.NativeRefinement
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86StateFrame

/-!
# Native block layout and source/WP composition from local templates

A specification supplies existing source actions, their native representation,
actual template bytes/counts, readiness and explicit register/byte footprints.
A local certificate proves each template with the original x86 fetch function,
including every instruction prefix. It does not assume a whole compiler result.

The common compiler concatenates unit-result source calls. Its program-indexed
representation pins canonical code placement and protects the complete block
from declared writes. Layout, code preservation, exact-count composition and
prefix frames are proved once for every certified library. Source semantics
and WP are the established GSLT definitions; no extra runtime is introduced.

Conditional/loop lowering, non-unit replies, admission and public return/ABI
composition retain separate obligations. Concrete libraries must construct the
local certificates and provide inhabited source/native controls.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BlockCompiler

open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

local instance : MemoryPrimitives := X86Memory.ordinary

universe u s
variable {Op : Type u} {Source : Type s}

abbrev Program (Op : Type u) := Prog Op (fun _ => Unit) Unit

structure Spec (Op : Type u) (Source : Type s) where
  action : Op → Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action Source Unit
  represents : Source → State → Prop
  ready : State → Prop
  bytes : Op → List Nat
  count : Op → Nat
  registerWrites : Finset Register
  byteWrites : Finset Nat

noncomputable def code (spec : Spec Op Source) : Program Op → List Nat
  | .ret _ => []
  | .call op next => spec.bytes op ++ code spec (next ())

def steps (spec : Spec Op Source) : Program Op → Nat
  | .ret _ => 0
  | .call op next => spec.count op + steps spec (next ())

theorem code_bind (spec : Spec Op Source) (program : Program Op) (next : Unit → Program Op) :
    code spec (program.bind next) = code spec program ++ code spec (next ()) := by
  induction program with
  | ret value => cases value; rfl
  | call op later ih => simp only [Prog.bind, code, ih (), List.append_assoc]

theorem steps_bind (spec : Spec Op Source) (program : Program Op) (next : Unit → Program Op) :
    steps spec (program.bind next) = steps spec program + steps spec (next ()) := by
  induction program with
  | ret value => cases value; simp only [Prog.bind, steps, Nat.zero_add]
  | call op later ih => simp only [Prog.bind, steps, ih (), Nat.add_assoc]

theorem code_prim (spec : Spec Op Source) (op : Op) : code spec (Prog.prim op) = spec.bytes op := by
  simp only [Prog.prim, code, List.append_nil]

theorem steps_prim (spec : Spec Op Source) (op : Op) : steps spec (Prog.prim op) = spec.count op := by
  simp only [Prog.prim, steps, Nat.add_zero]

structure At (spec : Spec Op Source) (stop : Int) (program : Program Op) (source : Source) (native : State) where
  origin : X86LegacyFetch.Basis native
  placed : origin.address.toInt = stop - (code spec program).length
  upper : stop + 3 < (2 ^ 47 : Int)
  represented : spec.represents source native
  ready : spec.ready native
  loaded : codeLoaded native origin.address.toInt (code spec program)
  outside : ∀ index byte, (code spec program)[index]? = some byte →
    ((address origin.address.toInt index).signExtend 52).toNat ∉ spec.byteWrites

def Observed (spec : Spec Op Source) (stop : Int) (_ : Unit) (source : Source) (native : State) : Prop :=
  spec.represents source native ∧ spec.ready native ∧
    native.regs.get? .rip = some ((BitVec.ofInt 48 stop).signExtend 64)

theorem head_byte (spec : Spec Op Source) (op : Op) (next : Unit → Program Op)
    (index byte : Nat) (present : (spec.bytes op)[index]? = some byte) :
    (code spec (.call op next))[index]? = some byte := by
  rw [code, List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem tail_byte (spec : Spec Op Source) (op : Op) (next : Unit → Program Op) (index : Nat) :
    (code spec (.call op next))[(spec.bytes op).length + index]? = (code spec (next ()))[index]? := by
  rw [code, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

section Machine
variable [OtherOpcodeHandlers] [VectorOpcodeHandlers]

structure Correct (spec : Spec Op Source) : Prop where
  dataOnly : spec.registerWrites ⊆ dataRegisters
  execute : ∀ op source following native (origin : X86LegacyFetch.Basis native),
    (spec.action op).Safe source → (spec.action op).Step source () following →
    spec.represents source native → spec.ready native →
    origin.address.toInt + (((spec.bytes op).length + 3 : Nat) : Int) < (2 ^ 47 : Int) →
    codeLoaded native origin.address.toInt (spec.bytes op) →
    (∀ index byte, (spec.bytes op)[index]? = some byte →
      ((address origin.address.toInt index).signExtend 52).toNat ∉ spec.byteWrites) →
    ∃ after, (X86FuelPrefix.fetches (spec.count op)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      spec.represents following after ∧ spec.ready after ∧
      after.regs.get? .rip = some ((address origin.address.toInt (spec.bytes op).length).signExtend 64) ∧
      ∀ count ≤ spec.count op, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        X86StateFrame.Frame spec.registerWrites spec.byteWrites native observed

noncomputable def machine (spec : Spec Op Source) : NativeRefinement.Machine State where
  executes count before after := (X86FuelPrefix.fetches count).run before = .ok () after
  zero := X86FuelPrefix.fetches_zero
  append := fun {first second before middle after} one two =>
    X86FuelPrefix.fetches_then first second before middle after one two
  deterministic := fun {count before left right} one two =>
    X86FuelPrefix.fetches_deterministic count before left right one two
  frame := X86StateFrame.Frame spec.registerWrites spec.byteWrites
  frame_refl := X86StateFrame.Frame.refl _ _
  frame_trans := by
    intro before middle after first second
    exact (first.trans second).mono (by simp) (by simp)

theorem primitive (spec : Spec Op Source) (correct : Correct spec) (stop : Int)
    (op : Op) (next : Unit → Program Op) (source following : Source) (native : State)
    (input : At spec stop (.call op next) source native)
    (safe : (spec.action op).Safe source) (sourceStep : (spec.action op).Step source () following) :
    ∃ after, (X86FuelPrefix.fetches (spec.count op)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      Nonempty (At spec stop (next ()) following after) ∧
      ∀ count ≤ spec.count op, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        X86StateFrame.Frame spec.registerWrites spec.byteWrites native observed := by
  have totalUpper : input.origin.address.toInt + (((code spec (.call op next)).length + 3 : Nat) : Int) <
      (2 ^ 47 : Int) := by have := input.placed; have := input.upper; omega
  have headUpper : input.origin.address.toInt + (((spec.bytes op).length + 3 : Nat) : Int) <
      (2 ^ 47 : Int) := by
    have size : (code spec (.call op next)).length = (spec.bytes op).length + (code spec (next ())).length := by
      rw [code, List.length_append]
    omega
  obtain ⟨after, executed, framed, represented, ready, pointer, prefixes⟩ :=
    correct.execute op source following native input.origin safe sourceStep input.represented input.ready headUpper
      (by intro index byte present; exact input.loaded index byte (head_byte spec op next index byte present))
      (by intro index byte present; exact input.outside index byte (head_byte spec op next index byte present))
  let origin := X86StateFrame.rebase native after input.origin framed correct.dataOnly
    (extent := (code spec (.call op next)).length + 3) totalUpper (spec.bytes op).length
    (by rw [code, List.length_append]; omega) pointer
  have originInt : origin.address.toInt = input.origin.address.toInt + (spec.bytes op).length := by
    exact address_toInt _ (by simpa using BitVec.le_toInt input.origin.address) totalUpper _ (by rw [code, List.length_append]; omega)
  have shifted (index : Nat) : address origin.address.toInt index =
      address input.origin.address.toInt ((spec.bytes op).length + index) := by
    rw [originInt]
    simp only [address, Int.natCast_add, Int.add_assoc]
  refine ⟨after, executed, framed, ?_, prefixes⟩
  refine ⟨{
    origin := origin
    placed := ?_
    upper := input.upper
    represented := represented
    ready := ready
    loaded := ?_
    outside := ?_ }⟩
  · rw [originInt]
    have placed := input.placed
    rw [code, List.length_append] at placed
    omega
  · intro index byte present
    have inWhole : (code spec (.call op next))[(spec.bytes op).length + index]? = some byte :=
      (tail_byte spec op next index).trans present
    rw [shifted]
    exact framed.codeLoaded _ _ input.loaded input.outside _ _ inWhole
  · intro index byte present
    rw [shifted]
    exact input.outside _ _ ((tail_byte spec op next index).trans present)

theorem counted_boundary (spec : Spec Op Source) (correct : Correct spec) (stop : Int) :
    NativeRefinement.CountedBoundary spec.action (machine spec)
      (fun program source native => Nonempty (At spec stop program source native))
      (Observed spec stop) (fun program _ => steps spec program) where
  returned value source native represented := by
    obtain ⟨input⟩ := represented
    refine ⟨native, X86FuelPrefix.fetches_zero native, X86StateFrame.Frame.refl _ _ _,
      input.represented, input.ready, ?_⟩
    have placed : input.origin.address.toInt = stop := by
      simpa only [code, List.length_nil, Int.natCast_zero, sub_zero] using input.placed
    rw [← placed, BitVec.ofInt_toInt]
    exact input.origin.rip
  primitive op next source reply following native safe represented sourceStep := by
    cases reply
    obtain ⟨input⟩ := represented
    obtain ⟨after, executed, framed, nextInput, _⟩ := primitive spec correct stop op next source following native input safe sourceStep
    exact ⟨spec.count op, after, executed, framed, nextInput, rfl⟩

theorem compile_wp (spec : Spec Op Source) (correct : Correct spec)
    (progress : ∀ op, (spec.action op).Progress) (stop : Int) (program : Program Op)
    (source : Source) (native : State) (input : At spec stop program source native)
    (post : Unit → Source → Prop) (wp : program.wp spec.action post source) :
    ∃ following after, program.Runs spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (steps spec program)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧ Observed spec stop () following after := by
  obtain ⟨⟨⟩, following, after, run, holds, executed, framed, observed⟩ :=
    (counted_boundary spec correct stop).wp_native progress program post source native wp ⟨input⟩
  exact ⟨following, after, run, holds, executed, framed, observed⟩

theorem fetches_split (first second : Nat) (before after : State)
    (run : (X86FuelPrefix.fetches (first + second)).run before = .ok () after) :
    ∃ middle, (X86FuelPrefix.fetches first).run before = .ok () middle ∧
      (X86FuelPrefix.fetches second).run middle = .ok () after := by
  rw [X86FuelPrefix.fetches_add, run_bind] at run
  cases result : (X86FuelPrefix.fetches first).run before with
  | error error failed => rw [result] at run; contradiction
  | ok value middle =>
      cases value
      rw [result] at run
      exact ⟨middle, rfl, run⟩

theorem prefix_executes (spec : Spec Op Source) (correct : Correct spec)
    (progress : ∀ op, (spec.action op).Progress) (stop : Int) (program : Program Op)
    (source : Source) (native : State) (input : At spec stop program source native)
    (safe : program.Safe spec.action source) (count : Nat) (within : count ≤ steps spec program) :
    ∃ after, (X86FuelPrefix.fetches count).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after := by
  induction program generalizing source native count with
  | ret value =>
      have zero : count = 0 := by simpa only [steps, Nat.le_zero] using within
      subst count
      exact ⟨native, X86FuelPrefix.fetches_zero native, X86StateFrame.Frame.refl _ _ _⟩
  | call op next ih =>
      obtain ⟨⟨⟩, following, sourceStep⟩ := progress op source safe.1
      obtain ⟨middle, first, firstFrame, ⟨nextInput⟩, prefixes⟩ :=
        primitive spec correct stop op next source following native input safe.1 sourceStep
      by_cases inside : count ≤ spec.count op
      · have divided : spec.count op = count + (spec.count op - count) := by omega
        rw [divided] at first
        obtain ⟨after, run, _⟩ := fetches_split count (spec.count op - count) native middle first
        exact ⟨after, run, prefixes count inside after run⟩
      · have tailWithin : count - spec.count op ≤ steps spec (next ()) := by
          simp only [steps] at within
          omega
        obtain ⟨after, rest, restFrame⟩ := ih () following middle nextInput
          (safe.2 () following sourceStep) (count - spec.count op) tailWithin
        refine ⟨after, ?_, (firstFrame.trans restFrame).mono (by simp) (by simp)⟩
        have combined := X86FuelPrefix.fetches_then (spec.count op) (count - spec.count op) native middle after first rest
        simpa only [Nat.add_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge inside))] using combined

theorem prefix_frame (spec : Spec Op Source) (correct : Correct spec)
    (progress : ∀ op, (spec.action op).Progress) (stop : Int) (program : Program Op)
    (source : Source) (native after : State) (input : At spec stop program source native)
    (safe : program.Safe spec.action source) (count : Nat) (within : count ≤ steps spec program)
    (run : (X86FuelPrefix.fetches count).run native = .ok () after) :
    X86StateFrame.Frame spec.registerWrites spec.byteWrites native after := by
  obtain ⟨proved, executed, framed⟩ := prefix_executes spec correct progress stop program source native input safe count within
  have same := X86FuelPrefix.fetches_deterministic count native proved after executed run
  subst after
  exact framed

theorem compile_reflects (spec : Spec Op Source) (correct : Correct spec)
    (progress : ∀ op, (spec.action op).Progress) (stop : Int) (program : Program Op)
    (source : Source) (native after : State) (input : At spec stop program source native)
    (post : Unit → Source → Prop) (wp : program.wp spec.action post source)
    (run : (X86FuelPrefix.fetches (steps spec program)).run native = .ok () after) :
    ∃ following, program.Runs spec.action source () following ∧ post () following ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧ Observed spec stop () following after := by
  obtain ⟨⟨⟩, following, sourceRun, holds, framed, observed⟩ :=
    (counted_boundary spec correct stop).wp_native_reflects progress program post source native wp ⟨input⟩ after run
  exact ⟨following, sourceRun, holds, framed, observed⟩

end Machine
end Mettapedia.Machines.TIsa.X86BlockCompiler
