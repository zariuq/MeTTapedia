import Mettapedia.Machines.TIsa.P1Source
import Algorithms.MeTTa.Simple.Parser

/-!
# Checked structural decoding of the p1 source spelling

The byte reader is the existing explicit PeTTa S-expression reader. Structural
decoding retains every printed constructor and field and checks finite payload
ranges. Re-encoding must reproduce the parsed tree exactly. The checked-reader
theorem concerns that structural boundary; byte lexing, C printing and semantic
admission retain separate contracts. Runtime probes exercise the text reader.

UNINIT remains source data, but has no C printer spelling today; encoding that
annotation declines rather than silently inventing a type.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.P1Source
open Algorithms.MeTTa.Simple.Parser (SExpr)

def atom (n : Nat) : SExpr := .atom (toString n)
def natural? : SExpr → Option Nat
  | .atom text => text.toNat?
  | _ => none
def bounded? (bound : Nat) (value : SExpr) : Option (Fin bound) := do
  let n ← natural? value
  if h : n < bound then some ⟨n, h⟩ else none
def reg? := bounded? 12
def region? := bounded? 9
def word? (value : SExpr) : Option Word := do
  let n ← natural? value
  if n < 2 ^ 64 then some (BitVec.ofNat 64 n) else none
def u32? (value : SExpr) : Option (BitVec 32) := do
  let n ← natural? value
  if n < 2 ^ 32 then some (BitVec.ofNat 32 n) else none
def displacement? : SExpr → Option (BitVec 32)
  | .atom text => do
      let n ← text.toInt?
      if -(2 ^ 31 : Int) ≤ n ∧ n < 2 ^ 31 then some (BitVec.ofInt 32 n) else none
  | _ => none

def typeName? : TypeTag → Option SExpr
  | .uninit => none
  | .u64 => some (.atom "TyU64")
  | .u32z => some (.atom "TyU32Z")
  | .i32s => some (.atom "TyI32S")
  | .boolean => some (.atom "TyBool")
  | .pointer => some (.atom "TyPtr")
def type? : SExpr → Option TypeTag
  | .atom "TyU64" => some .u64
  | .atom "TyU32Z" => some .u32z
  | .atom "TyI32S" => some .i32s
  | .atom "TyBool" => some .boolean
  | .atom "TyPtr" => some .pointer
  | _ => none

def binName : Binary → String
  | .add => "BinAdd" | .sub => "BinSub" | .band => "BinAnd"
  | .bor => "BinOr" | .bxor => "BinXor" | .mulLo => "BinMulLo"
def bin? : SExpr → Option Binary
  | .atom "BinAdd" => some .add | .atom "BinSub" => some .sub | .atom "BinAnd" => some .band
  | .atom "BinOr" => some .bor | .atom "BinXor" => some .bxor | .atom "BinMulLo" => some .mulLo
  | _ => none
def shiftName : Shift → String
  | .left => "ShiftLeft" | .rightUnsigned => "ShiftRightU" | .rightSigned => "ShiftRightS"
def shift? : SExpr → Option Shift
  | .atom "ShiftLeft" => some .left | .atom "ShiftRightU" => some .rightUnsigned
  | .atom "ShiftRightS" => some .rightSigned | _ => none
def condName : Comparison → String
  | .equal => "CondEq" | .notEqual => "CondNe" | .lessUnsigned => "CondUlt"
  | .lessEqualUnsigned => "CondUle" | .lessSigned => "CondSlt" | .lessEqualSigned => "CondSle"
def cond? : SExpr → Option Comparison
  | .atom "CondEq" => some .equal | .atom "CondNe" => some .notEqual
  | .atom "CondUlt" => some .lessUnsigned | .atom "CondUle" => some .lessEqualUnsigned
  | .atom "CondSlt" => some .lessSigned | .atom "CondSle" => some .lessEqualSigned
  | _ => none
def width? (value : SExpr) : Option Width := do
  match ← natural? value with
  | 1 => some .byte | 4 => some .word32 | 8 => some .word64 | _ => none
def outcome? (value : SExpr) : Option ExitStatus := do
  match ← natural? value with
  | 0 => some .refused | 1 => some .completed | 2 => some .unsupported
  | 3 => some .invalidInput | 4 => some .exhausted | _ => none

def encodeOperand : Operand → SExpr
  | .register r => .list [.atom "OpReg", atom r.val]
  | .immediate value => .list [.atom "OpImm", atom value.toNat]
def operand? : SExpr → Option Operand
  | .list [.atom "OpReg", r] => (reg? r).map Operand.register
  | .list [.atom "OpImm", value] => (word? value).map Operand.immediate
  | _ => none
def encodeIndex : Option Reg → SExpr
  | none => .atom "NONE" | some r => .list [.atom "SOME", atom r.val]
def index? : SExpr → Option (Option Reg)
  | .atom "NONE" => some none
  | .list [.atom "SOME", r] => (reg? r).map some
  | _ => none

def encodeInstr : Instr → Option SExpr
  | .immediate ty dst value => do
      pure (.list [.atom "TImm", ← typeName? ty, atom dst.val, atom value.toNat])
  | .move ty dst source => do
      pure (.list [.atom "TMov", ← typeName? ty, atom dst.val, atom source.val])
  | .binary op ty dst left right => do
      pure (.list [.atom "TBin", .atom (binName op), ← typeName? ty, atom dst.val, atom left.val, atom right.val])
  | .shift op ty dst source amount => do
      pure (.list [.atom "TShift", .atom (shiftName op), ← typeName? ty, atom dst.val, atom source.val, atom amount])
  | .extract ty dst source low width => do
      pure (.list [.atom "TExtract", ← typeName? ty, atom dst.val, atom source.val, atom low, atom width])
  | .compare condition ty dst left right => do
      pure (.list [.atom "TCmp", .atom (condName condition), ← typeName? ty, atom dst.val, atom left.val, encodeOperand right])
  | .select ty dst condition yes no => do
      pure (.list [.atom "TSelect", ← typeName? ty, atom dst.val, atom condition.val, atom yes.val, atom no.val])
  | .address region dst base index scale disp =>
      some (.list [.atom "TAddr", atom region.val, atom dst.val, atom base.val, encodeIndex index,
        atom scale.val, .atom (toString disp.toInt)])
  | .load ty width region dst base disp => do
      pure (.list [.atom "TLoad", ← typeName? ty, atom width.bytes, atom region.val, atom dst.val,
        atom base.val, .atom (toString disp.toInt)])
  | .loadFrame ty dst slot => do
      pure (.list [.atom "TLoadFrame", ← typeName? ty, atom dst.val, atom slot.val])
  | .store width region base disp source =>
      some (.list [.atom "TStore", atom width.bytes, atom region.val, atom base.val,
        .atom (toString disp.toInt), atom source.val])

def instr? : SExpr → Option Instr
  | .list [.atom "TImm", ty, dst, value] => do
      pure (.immediate (← type? ty) (← reg? dst) (← word? value))
  | .list [.atom "TMov", ty, dst, source] => do
      pure (.move (← type? ty) (← reg? dst) (← reg? source))
  | .list [.atom "TBin", op, ty, dst, left, right] => do
      pure (.binary (← bin? op) (← type? ty) (← reg? dst) (← reg? left) (← reg? right))
  | .list [.atom "TShift", op, ty, dst, source, amount] => do
      let amount ← natural? amount
      if amount < 256 then pure (.shift (← shift? op) (← type? ty) (← reg? dst) (← reg? source) amount) else none
  | .list [.atom "TExtract", ty, dst, source, low, width] => do
      let low ← natural? low
      let width ← natural? width
      if low < 256 ∧ width < 256 then pure (.extract (← type? ty) (← reg? dst) (← reg? source) low width) else none
  | .list [.atom "TCmp", condition, ty, dst, left, right] => do
      pure (.compare (← cond? condition) (← type? ty) (← reg? dst) (← reg? left) (← operand? right))
  | .list [.atom "TSelect", ty, dst, condition, yes, no] => do
      pure (.select (← type? ty) (← reg? dst) (← reg? condition) (← reg? yes) (← reg? no))
  | .list [.atom "TAddr", region, dst, base, index, scale, disp] => do
      pure (.address (← region? region) (← reg? dst) (← reg? base) (← index? index)
        (← bounded? 4 scale) (← displacement? disp))
  | .list [.atom "TLoad", ty, width, region, dst, base, disp] => do
      pure (.load (← type? ty) (← width? width) (← region? region) (← reg? dst) (← reg? base) (← displacement? disp))
  | .list [.atom "TLoadFrame", ty, dst, slot] => do
      pure (.loadFrame (← type? ty) (← reg? dst) (← bounded? 24 slot))
  | .list [.atom "TStore", width, region, base, disp, source] => do
      pure (.store (← width? width) (← region? region) (← reg? base) (← displacement? disp) (← reg? source))
  | _ => none

def encodeStmt : Stmt → Option SExpr
  | .skip => some (.atom "TSkip")
  | .instruction value => do pure (.list [.atom "TInstr", ← encodeInstr value])
  | .seq first second => do pure (.list [.atom "TSeq", ← encodeStmt first, ← encodeStmt second])
  | .branch condition yes no => do pure (.list [.atom "TIf", atom condition.val, ← encodeStmt yes, ← encodeStmt no])
  | .counted index bound cap body => do
      pure (.list [.atom "TCountLoop", atom index.val, atom bound.val, atom cap.toNat, ← encodeStmt body])
  | .early index bound continuation cap body => do
      pure (.list [.atom "TEarlyLoop", atom index.val, atom bound.val, atom continuation.val,
        atom cap.toNat, ← encodeStmt body])
  | .ret outcome source => some (.list [.atom "TReturn", atom outcome.word.toNat, atom source.val])
  | .fund units => some (.list [.atom "TFund", atom units.toNat])

def stmt? : SExpr → Option Stmt
  | .atom "TSkip" => some .skip
  | .list [.atom "TInstr", value] => (instr? value).map Stmt.instruction
  | .list [.atom "TSeq", first, second] => do pure (.seq (← stmt? first) (← stmt? second))
  | .list [.atom "TIf", condition, yes, no] => do pure (.branch (← reg? condition) (← stmt? yes) (← stmt? no))
  | .list [.atom "TCountLoop", index, bound, cap, body] => do
      pure (.counted (← reg? index) (← reg? bound) (← u32? cap) (← stmt? body))
  | .list [.atom "TEarlyLoop", index, bound, continuation, cap, body] => do
      pure (.early (← reg? index) (← reg? bound) (← reg? continuation) (← u32? cap) (← stmt? body))
  | .list [.atom "TReturn", outcome, source] => do pure (.ret (← outcome? outcome) (← reg? source))
  | .list [.atom "TFund", units] => (u32? units).map Stmt.fund
  | _ => none
termination_by expression => sizeOf expression

def Mode.number : Mode → Nat
  | .absent => 0 | .readOnly => 1 | .readWrite => 2
def mode? (expression : SExpr) : Option Mode := do
  match ← natural? expression with
  | 0 => some .absent | 1 => some .readOnly | 2 => some .readWrite | _ => none
def encodeRegion (region : RegionDecl) : SExpr :=
  .list [atom region.mode.number, atom region.minimum.toNat, atom region.alignment.toNat]
def regionDecl? : SExpr → Option RegionDecl
  | .list [mode, minimum, alignment] => do pure ⟨← mode? mode, ← u32? minimum, ← u32? alignment⟩
  | _ => none
def encodeEntry (entry : EntryReg) : Option SExpr := do
  pure (.list [atom entry.register.val, ← typeName? entry.ty, atom entry.region.val])
def entry? : SExpr → Option EntryReg
  | .list [register, ty, region] => do pure ⟨← reg? register, ← type? ty, ← region? region⟩
  | _ => none
def encodeProgram (program : Program) : Option SExpr := do
  pure (.list [.atom "TProg", .list (program.regions.map encodeRegion),
    .list (← program.entry.mapM encodeEntry), ← encodeStmt program.body])
def program? : SExpr → Option Program
  | .list [.atom "TProg", .list regions, .list entry, body] => do
      if regions.length ≤ 9 then
        pure ⟨← regions.mapM regionDecl?, ← entry.mapM entry?, ← stmt? body⟩
      else none
  | _ => none

def readText (text : String) : Except String Program :=
  match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta text with
  | .error error => .error error.render
  | .ok raw => match program? raw with
    | none => .error "invalid p1 program fields"
    | some result =>
        if encodeProgram result = some raw then .ok result
        else .error "p1 program round-trip changed fields"

theorem readText_exact {text : String} {program : Program}
    (read : readText text = .ok program) :
    ∃ raw, Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta text = .ok raw ∧
      program? raw = some program ∧ encodeProgram program = some raw := by
  unfold readText at read
  cases parsed : Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta text with
  | error error => simp [parsed] at read
  | ok raw =>
      cases decoded : program? raw with
      | none => simp [parsed, decoded] at read
      | some candidate =>
          by_cases exact : encodeProgram candidate = some raw
          · simp [parsed, decoded, exact] at read
            subst program
            exact ⟨raw, rfl, decoded, exact⟩
          · simp [parsed, decoded, exact] at read

namespace Controls
def sample : String :=
  "(TProg ((1 32 8) (2 32 8)) ((1 TyPtr 0) (2 TyPtr 1)) (TSeq (TFund 3) (TReturn 1 1)))"

#eval (readText sample).isOk
#eval (readText "(TProg () () (TInstr (TImm TyU64 12 0)))").isOk
#eval (readText "(TProg () () (TFund 4294967296))").isOk
#eval (readText "(TProg () () (TInstr (TStore 2 0 1 0 1)))").isOk
#eval (readText "(TProg () () (TInstr (TAddr 0 1 1 NONE 4 0)))").isOk

#eval (instr? (.list [.atom "TImm", .atom "TyU64", .atom "12", .atom "0"])).isNone
#eval (stmt? (.list [.atom "TFund", .atom "4294967296"])).isNone
#eval (instr? (.list [.atom "TStore", .atom "2", .atom "0", .atom "1", .atom "0", .atom "1"])).isNone
end Controls

end Mettapedia.Machines.TIsa.P1Source

#print axioms Mettapedia.Machines.TIsa.P1Source.readText_exact
