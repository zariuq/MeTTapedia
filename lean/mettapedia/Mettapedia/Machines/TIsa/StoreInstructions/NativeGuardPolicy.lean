import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardOperands

/-!
# Decisive observations in a native guard scan

Presence needs an assured witness. Absence stops on any
possible witness. A count cannot be exact once a possible
but unassured occurrence is encountered. The native counter
decrements only after checking that it is positive.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardPolicy

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Reads Controls CodeApart Encoding footprint)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeGuardWorkspace (Frame)
open IndexedGuard (Query)
open SolverGuardTrichotomy (Observation)
open NativeGuardDecision (word)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Decision
  | continue (remaining : ℕ)
  | stop (answer : Bool)
  deriving DecidableEq

def choose (query : Query) (remaining : ℕ) (observed : Observation) : Decision :=
  match query, observed with
  | .any, .assured => .stop true
  | .absent, .possible | .absent, .assured => .stop false
  | .count _, .possible => .stop false
  | .count _, .assured => if remaining = 0 then .stop false else .continue (remaining - 1)
  | _, _ => .continue remaining

def adjust (q : Query) (remaining : ℕ) : Query :=
  match q with | .count _ => .count remaining | _ => q

def scan := SymbolicGuardScan.scan Observation.must Observation.may

theorem scan_cons (query : Query) (remaining : ℕ) (seen : Observation) (rest : List Observation) :
    scan (adjust query remaining) (seen :: rest) =
      match choose query remaining seen with
      | .stop answer => answer
      | .continue n => scan (adjust query n) rest := by
  cases query <;> cases seen <;> cases remaining <;> simp [scan, adjust, choose, SymbolicGuardScan.scan,
    SymbolicGuardScan.countRemaining, Observation.must, Observation.may]

def width : Query → ℕ
  | .count _ => 47
  | _ => 9

def stackCode : List ℕ := registerCode 0x89 4 6
def loadCode : List ℕ := X86DataLoad.code true 0 6 120
def subCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 13 0
def encoding : Encoding := .direct 6 (by decide) (by decide)
def storeCode : List ℕ := encoding.bytes 0 120
def wire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 0, by decide, by decide⟩

def emit (q : Query) (start pass fail : ℕ) : List ℕ :=
  match q with
  | .any => NativeDecisions.compareBytes .lessEqualUnsigned 0 13 start pass
  | .absent => NativeDecisions.compareBytes .equal 0 12 start fail
  | .count _ =>
    NativeDecisions.compareBytes .notEqual 0 12 start (start + 47) ++
      (NativeDecisions.compareBytes .lessUnsigned 13 0 (start + 9) fail ++
        (stackCode ++ (loadCode ++ (NativeDecisions.compareBytes .lessUnsigned 12 0 (start + 28) fail ++ (subCode ++ storeCode)))))

theorem emit_size (q : Query) (start pass fail : ℕ) : (emit q start pass fail).length = width q := by
  cases q <;> simp only [emit, width, NativeDecisions.compare_size, List.length_append,
    show stackCode.length = 3 from rfl, show loadCode.length = 7 from rfl,
    show subCode.length = 3 from rfl, show storeCode.length = 7 from rfl]

structure DecrementPlaced (image : NativeImage.View) (start fail : ℕ) : Prop where
  extent : start + 29 ≤ image.size
  stack : Code image start stackCode
  load : Code image (start + 3) loadCode
  test : CompareBranch image (start + 10) fail .lessUnsigned 12 0
  sub : Code image (start + 19) subCode
  store : Code image (start + 22) storeCode

inductive Placed (image : NativeImage.View) : Query → ℕ → ℕ → ℕ → Prop
  | any {start pass fail : ℕ} : CompareBranch image start pass .lessEqualUnsigned 0 13 → Placed image .any start pass fail
  | absent {start pass fail : ℕ} : CompareBranch image start fail .equal 0 12 → Placed image .absent start pass fail
  | count {n start pass fail : ℕ} :
      CompareBranch image start (start + 47) .notEqual 0 12 →
      CompareBranch image (start + 9) fail .lessUnsigned 13 0 →
      DecrementPlaced image (start + 18) fail → Placed image (.count n) start pass fail

theorem placed_of_emitted (image : NativeImage.View) (q : Query) (start pass fail : ℕ)
    (space : start + width q ≤ image.size) (passed : pass ≤ image.size) (failed : fail ≤ image.size)
    (short : image.size < 2 ^ 31) (code : Code image start (emit q start pass fail)) : Placed image q start pass fail := by
  cases q with
  | any => exact .any (NativeDecisions.compare_placed image _ _ _ _ _ space passed short code)
  | absent => exact .absent (NativeDecisions.compare_placed image _ _ _ _ _ space failed short code)
  | count n =>
    change start + 47 ≤ image.size at space
    obtain ⟨zero, rest⟩ := NativeWords.code_append (show Code image start
      (NativeDecisions.compareBytes .notEqual 0 12 start (start + 47) ++ _) from code)
    rw [NativeDecisions.compare_size] at rest
    obtain ⟨maybe, rest⟩ := NativeWords.code_append rest
    rw [NativeDecisions.compare_size] at rest
    obtain ⟨stack, rest⟩ := NativeWords.code_append rest
    obtain ⟨load, rest⟩ := NativeWords.code_append rest
    change Code image (start + 28) _ at rest
    obtain ⟨test, rest⟩ := NativeWords.code_append rest
    rw [NativeDecisions.compare_size] at rest
    obtain ⟨sub, store⟩ := NativeWords.code_append rest
    exact .count (NativeDecisions.compare_placed image _ _ _ _ _ (by omega) space short zero)
      (NativeDecisions.compare_placed image _ _ _ _ _ (by omega) failed short maybe)
      ⟨space, stack, load, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) failed short test, sub, store⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rsi, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def counterBytes (frame : Frame) : Finset ℕ := footprint (frame.cell 15).address

private theorem fetched_decrement (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start fail : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (code : DecrementPlaced image start fail)
    (frame : Frame) (stack : lookup before 4 = some frame.pointer) (remaining : ℕ) (fits : remaining < 2 ^ 64)
    (counter : Reads before (frame.cell 15).address (BitVec.ofNat 64 remaining))
    (zero : lookup before 12 = some 0) (one : lookup before 13 = some 1) (apart : CodeApart image base (counterBytes frame)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (counterBytes frame) before after ∧
      if remaining = 0 then Nonempty (At image after base fail)
      else Reads after (frame.cell 15).address (BitVec.ofNat 64 (remaining - 1)) ∧ Nonempty (At image after base (start + 29)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  let n := BitVec.ofNat 64 remaining
  have exactN : n.toNat = remaining := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  obtain ⟨a, entered, move, known, ⟨atLoad⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer stack code.stack
  have moved := X86StateFrame.registerOnly move
  obtain ⟨b, read, loadFrame, count, ⟨atTest⟩⟩ := (NativeAgendaRead.fieldSource frame 15).fetch
    (handlers other extra) vector wire n atLoad (controls.transport moved (by decide)) known
    (counter.preserved moved (by simp)) (show start + 10 ≤ image.size by omega) code.load
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at read
  have throughRead := moved.trans loadFrame
  obtain ⟨c, checked, cmp, ⟨atBranch⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector (show At image b base (start + 10) from atTest)
    .lessUnsigned 12 0 code.test 0 n ((throughRead.lookup 12 (by decide)).trans zero) count
  change At image c base (if decide (0 < n.toNat) then start + 19 else fail) at atBranch
  rw [exactN] at atBranch
  have first := throughRead.trans (X86StateFrame.registerOnly cmp)
  have throughCheck := X86FuelPrefix.fetches_then 2 2 before b c (X86FuelPrefix.fetches_then 1 1 before a b entered read) checked
  by_cases empty : remaining = 0
  · have halt : At image c base fail := by simpa [empty] using atBranch
    exact ⟨c, 4, throughCheck, first.mono (by decide) (by simp), by simpa [empty] using Nonempty.intro halt⟩
  · have positive : 0 < remaining := Nat.pos_of_ne_zero empty
    have atSub : At image c base (start + 19) := by simpa [positive] using atBranch
    obtain ⟨d, subtracted, sub, next, ⟨atStore⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector atSub (by omega) .sub 13 0 n 1
      ((first.lookup 13 (by decide)).trans one) ((cmp.lookup 0 (by decide)).trans count) code.sub
    have arith : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
    rw [arith] at subtracted
    have lower : (1 : Word) ≤ n := by rw [BitVec.le_def, exactN]; exact positive
    have repr : n - 1 = BitVec.ofNat 64 (remaining - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le lower, exactN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rfl
    have throughSub := first.trans (X86StateFrame.registerOnly sub)
    obtain ⟨after, written, stored, counterAfter, endpoint⟩ := X86PlacedMemory.stores (handlers other extra)
      vector (show At image d base (start + 22) from atStore) (controls.transport throughSub (by decide))
      encoding 0 120 frame.pointer (BitVec.ofNat 64 (remaining - 1)) (frame.cell 15)
      (((loadFrame.trans (X86StateFrame.registerOnly cmp)).trans (X86StateFrame.registerOnly sub)).lookup 6 (by decide) |>.trans known)
      (repr ▸ next) extent code.store apart
    refine ⟨after, 6, X86FuelPrefix.fetches_then 5 1 before d after
      (X86FuelPrefix.fetches_then 4 1 before c d throughCheck subtracted) written,
      (throughSub.trans stored).mono (by decide) (by simp [counterBytes]), ?_⟩
    rw [if_neg empty]
    exact ⟨counterAfter, endpoint⟩

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start pass fail : ℕ} {before : Native}
    (query : Query) (point : At image before base start) (controls : Controls before) (code : Placed image query start pass fail)
    (frame : Frame) (stack : lookup before 4 = some frame.pointer) (remaining : ℕ) (fits : remaining < 2 ^ 64)
    (counter : Reads before (frame.cell 15).address (BitVec.ofNat 64 remaining))
    (observed : Observation) (tag : lookup before 0 = some (word observed))
    (zero : lookup before 12 = some 0) (one : lookup before 13 = some 1) (apart : CodeApart image base (counterBytes frame)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (counterBytes frame) before after ∧
      match choose query remaining observed with
      | .stop answer => Nonempty (At image after base (if answer then pass else fail))
      | .continue next => Reads after (frame.cell 15).address (BitVec.ofNat 64 next) ∧
          Nonempty (At image after base (start + width query)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  cases code with
  | any check =>
    obtain ⟨after, ran, compared, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .lessEqualUnsigned 0 13 check _ _ tag one
    have framed := X86StateFrame.registerOnly compared
    refine ⟨after, 2, ran, framed.mono (by decide) (by simp), ?_⟩
    cases observed with
    | impossible => exact ⟨counter.preserved framed (by simp), ⟨endpoint⟩⟩
    | possible => exact ⟨counter.preserved framed (by simp), ⟨endpoint⟩⟩
    | assured => exact ⟨endpoint⟩
  | absent check =>
    obtain ⟨after, ran, compared, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .equal 0 12 check _ _ tag zero
    have framed := X86StateFrame.registerOnly compared
    refine ⟨after, 2, ran, framed.mono (by decide) (by simp), ?_⟩
    cases observed with
    | impossible => exact ⟨counter.preserved framed (by simp), ⟨endpoint⟩⟩
    | possible => exact ⟨endpoint⟩
    | assured => exact ⟨endpoint⟩
  | @count n start pass fail openMatch distinguish decrement =>
    obtain ⟨a, checked, compared, ⟨first⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .notEqual 0 12 openMatch _ _ tag zero
    have framed := X86StateFrame.registerOnly compared
    cases observed with
    | impossible =>
      exact ⟨a, 2, checked, framed.mono (by decide) (by simp), counter.preserved framed (by simp), ⟨first⟩⟩
    | possible =>
      obtain ⟨b, decided, comparison, endpoint⟩ := X86PlacedScalar.compare_branch
        (X86PlacedFrameAddress.nativeBase other) extra vector first .lessUnsigned 13 0 distinguish 1 1
        ((compared.lookup 13 (by decide)).trans one) ((compared.lookup 0 (by decide)).trans tag)
      exact ⟨b, 4, X86FuelPrefix.fetches_then 2 2 before a b checked decided,
        (X86StateFrame.registerOnly (compared.trans comparison)).mono (by decide) (by simp), endpoint⟩
    | assured =>
      obtain ⟨b, decided, comparison, ⟨atDecrement⟩⟩ := X86PlacedScalar.compare_branch
        (X86PlacedFrameAddress.nativeBase other) extra vector first .lessUnsigned 13 0 distinguish 1 2
        ((compared.lookup 13 (by decide)).trans one) ((compared.lookup 0 (by decide)).trans tag)
      have thru := X86StateFrame.registerOnly (compared.trans comparison)
      obtain ⟨after, steps, changed, changedFrame, endpoint⟩ := fetched_decrement other extra vector
        (show At image b base (start + 18) from atDecrement)
        (controls.transport thru (by decide)) decrement frame ((thru.lookup 4 (by decide)).trans stack) remaining fits
        (counter.preserved thru (by simp)) ((thru.lookup 12 (by decide)).trans zero)
        ((thru.lookup 13 (by decide)).trans one) apart
      refine ⟨after, 4 + steps, X86FuelPrefix.fetches_then 4 steps before b after
        (X86FuelPrefix.fetches_then 2 2 before a b checked decided) changed,
        (thru.trans changedFrame).mono (by decide) (by simp), ?_⟩
      by_cases empty : remaining = 0
      · simpa only [choose, if_pos empty, Bool.false_eq_true, if_false] using endpoint
      · simpa only [choose, if_neg empty, width] using endpoint

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardPolicy
