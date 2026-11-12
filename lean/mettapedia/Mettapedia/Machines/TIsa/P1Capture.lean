import Mettapedia.Machines.TIsa.NativeImage
import Mettapedia.Machines.TIsa.P1SourceCodec

/-!
# Pure coherence checks for actual p1 captures

Source re-encoding binds the constructor tree to its entry, region and cost
metadata. Recorded span paths resolve to the expected source constructors;
wrapper bytes and contiguous extents are checked against the actual image.
These checks do not establish instruction decoding or native refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1Capture

open P1Source
open Algorithms.MeTTa.Simple.Parser (SExpr)

structure Boundary where
  frameBytes : Nat
  baseWord : String
  lengthWord : String
  resultWords : List Nat
  outcomes : List Nat
  registers : List String
  scratch : List String
  saved : List String
  frameRegister : String
  resultRegister : String
  entryOffset : Nat
  deriving DecidableEq, Repr

def Boundary.check (boundary : Boundary) : Bool :=
  decide (boundary.frameBytes = 192 ∧ boundary.baseWord = "2r" ∧
    boundary.lengthWord = "2r+1" ∧ boundary.resultWords = [18, 19, 20, 21, 22, 23] ∧
    boundary.outcomes = [0, 1, 2, 3, 4] ∧
    boundary.registers = ["rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11", "rax", "rbx", "r12", "r13"] ∧
    boundary.scratch = ["r14", "r15"] ∧ boundary.saved = ["rbx", "r12", "r13", "r14", "r15"] ∧
    boundary.frameRegister = "rdi" ∧ boundary.resultRegister = "rax" ∧ boundary.entryOffset = 0)

structure Span where
  offset : Nat
  length : Nat
  kind : String
  path : Option (List Nat)
  deriving DecidableEq, Repr

def instructionTemplate : Instr → String
  | .immediate .. => "IMM" | .move .. => "MOV" | .binary .. => "BIN"
  | .shift .. => "SHIFT" | .extract .. => "EXTRACT" | .compare .. => "CMP"
  | .select .. => "SELECT" | .address .. => "ADDR" | .load .. => "LOAD"
  | .loadFrame .. => "LOAD-FRAME" | .store .. => "STORE"

def Span.sourceCheck (span : Span) (source : Stmt) : Bool :=
  match span.path with
  | none => ["PROLOGUE", "FAILURE", "EPILOGUE"].contains span.kind
  | some path => match source.atPath path with
    | some (.instruction instruction) => span.kind == instructionTemplate instruction
    | some (.branch ..) => span.kind == "IF" || span.kind == "IF-ELSE"
    | some (.counted ..) => ["LOOP-ENTRY", "LOOP-HEAD", "LOOP-LATCH"].contains span.kind
    | some (.early ..) => ["LOOP-ENTRY", "EARLY-LOOP-HEAD", "EARLY-LOOP-LATCH"].contains span.kind
    | some (.ret ..) => span.kind == "RETURN"
    | some (.fund _) => span.kind == "FUND"
    | _ => false

structure Program where
  name : String
  id : Nat
  source : P1Source.Program
  printed : SExpr
  regions : List RegionDecl
  entry : List EntryReg
  fundPoints : Nat
  maximumReceipt : Word
  maximumFits : Bool
  size : Nat
  data : Lean.RArray Nat
  digest : String
  spans : List Span

def Program.sourceCheck (program : Program) : Bool :=
  decide (encodeProgram program.source = some program.printed ∧
    program.source.regions = program.regions ∧
    program.source.entry = program.entry.filter (fun entry => entry.register != 0) ∧
    (program.entry.map EntryReg.register).Nodup ∧
    (⟨0, .u64, 0⟩ : EntryReg) ∈ program.entry ∧
    program.source.body.fundPoints = program.fundPoints ∧
    program.source.body.reportedBound = program.maximumReceipt ∧
    program.source.body.boundFits = program.maximumFits)

def Program.view (program : Program) : NativeImage.View :=
  ⟨program.size, fun offset =>
    if offset < program.size then
      let value : Nat := Lean.RArray.get program.data offset
      if Nat.ble value 255 then some (BitVec.ofNat 8 value) else none
    else none⟩

def Program.imageCheckOn (program : Program) (view : NativeImage.View) : Bool :=
  19 ≤ program.size &&
    view.size == program.size &&
    NativeImage.readRange? view 0 9 == some NativeImage.prologue &&
    NativeImage.readRange? view (program.size - 10) 10 == some NativeImage.epilogue &&
    NativeImage.spanEnd? 0 (program.spans.map fun span => ⟨span.offset, span.length, span.kind⟩) == some program.size &&
    program.spans.all (fun span => span.sourceCheck program.source.body)

def Program.imageCheck (program : Program) : Bool := program.imageCheckOn program.view

theorem Program.printed_exact (program : Program) (checked : program.sourceCheck = true) :
    encodeProgram program.source = some program.printed := (of_decide_eq_true checked).1

theorem Program.cost_exact (program : Program) (checked : program.sourceCheck = true) :
    program.source.body.fundPoints = program.fundPoints ∧
      program.source.body.reportedBound = program.maximumReceipt ∧
      program.source.body.boundFits = program.maximumFits :=
  (of_decide_eq_true checked).2.2.2.2.2

theorem Program.regions_exact (program : Program) (checked : program.sourceCheck = true) :
    program.source.regions = program.regions := (of_decide_eq_true checked).2.1

/-- The overflow witness, not a saturated word alone, licenses an exact natural bound. -/
theorem Program.natural_cost_exact (program : Program) (checked : program.sourceCheck = true)
    (fits : program.maximumFits = true) :
    program.maximumReceipt.toNat = program.source.body.costBound := by
  obtain ⟨_, bound, flag⟩ := program.cost_exact checked
  rw [← bound]
  exact program.source.body.reportedBound_exact (flag.trans fits)

theorem Program.span_source_checked (program : Program) (checked : program.imageCheck = true)
    (span : Span) (member : span ∈ program.spans) : span.sourceCheck program.source.body = true :=
  List.all_eq_true.mp ((Bool.and_eq_true _ _).mp checked).2 span member

structure Bundle where
  boundary : Boundary
  declaredCount : Nat
  programs : List Program

end Mettapedia.Machines.TIsa.P1Capture
