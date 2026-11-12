import Mettapedia.Machines.TIsa.JsonImport
import Mettapedia.Machines.TIsa.P1Capture

/-!
# Elaboration adapter for actual p1 source programs and emitted images

The p1-v2 schema is separate from the old p0 image schema. This adapter quotes
ordinary source, boundary and byte data for the pure checks in P1Capture.
Byte parsing and C printing retain their own contracts; hashes identify
artifacts, not semantics. Missing p0 branch records are never fabricated.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1JsonImport

open Lean Elab Term P1Capture P1Source
open Algorithms.MeTTa.Simple.Parser (SExpr)

deriving instance ToExpr for Binary
deriving instance ToExpr for Shift
deriving instance ToExpr for Comparison
deriving instance ToExpr for ExitStatus
deriving instance ToExpr for TypeTag
deriving instance ToExpr for Width
deriving instance ToExpr for Operand
deriving instance ToExpr for Instr
deriving instance ToExpr for Stmt
deriving instance ToExpr for Mode
deriving instance ToExpr for RegionDecl
deriving instance ToExpr for EntryReg
deriving instance ToExpr for P1Source.Program

private partial def sourceExpr : SExpr → Expr
  | .atom token => mkApp (mkConst ``SExpr.atom) (toExpr token)
  | .list items => mkApp (mkConst ``SExpr.list)
      (items.foldr (fun item tail => mkApp3 (mkConst ``List.cons [0])
        (mkConst ``SExpr) (sourceExpr item) tail)
        (mkApp (mkConst ``List.nil [0]) (mkConst ``SExpr)))

private instance : ToExpr SExpr where
  toExpr := sourceExpr
  toTypeExpr := mkConst ``SExpr

deriving instance ToExpr for Boundary
deriving instance ToExpr for Span
deriving instance ToExpr for P1Capture.Program
deriving instance ToExpr for Bundle

private def require (condition : Bool) (reason : String) : Except String Unit :=
  if condition then .ok () else .error reason

private def nat (json : Json) (field : String) : Except String Nat := json.getObjValAs? Nat field
private def text (json : Json) (field : String) : Except String String := json.getObjValAs? String field
private def array (json : Json) (field : String) : Except String (List Json) :=
  (json.getObjVal? field >>= Json.getArr?).map Array.toList
private def strings (json : Json) (field : String) : Except String (List String) := do
  (← array json field).mapM Json.getStr?

private def boundary (json : Json) : Except String Boundary := do
  let frame ← json.getObjVal? "frame"
  let outcomes ← json.getObjVal? "outcome_codes"
  let x86 ← json.getObjVal? "x86_64"
  pure ⟨← nat frame "bytes", ← text frame "region_base_word", ← text frame "region_len_word",
    ← ["status_word", "ret_val_word", "fuel_budget_word", "fuel_used_word", "arg0_word", "arg1_word"].mapM (nat frame),
    ← ["REFUSED", "FIRED", "UNSUPPORTED", "INVALID_INPUT", "EXHAUSTED"].mapM (nat outcomes),
    ← strings x86 "vregs", ← strings x86 "scratch", ← strings x86 "saved_by_prologue",
    ← text x86 "frame_register", ← text x86 "ret_val_register", ← nat x86 "entry_offset"⟩

private def hexNatural (digits : String) : Except String Nat :=
  digits.toList.foldlM (fun value digit => do
    let n := digit.toNat
    let nibble ← if 48 ≤ n && n ≤ 57 then pure (n - 48)
      else if 97 ≤ n && n ≤ 102 then pure (n - 87) else throw "invalid hexadecimal digit"
    pure (16 * value + nibble)) 0

private def word (digits : String) : Except String Word := do
  require (digits.startsWith "0x" && digits.length == 18) "expected a full-width hexadecimal word"
  pure (BitVec.ofNat 64 (← hexNatural (String.ofList (digits.toList.drop 2))))

private def typeTag (name : String) : Except String TypeTag :=
  match name with
  | "U64" => .ok .u64 | "U32Z" => .ok .u32z | "I32S" => .ok .i32s
  | "BOOL" => .ok .boolean | "PTR" => .ok .pointer
  | _ => .error "unknown entry-register type"

private def region (json : Json) : Except String RegionDecl := do
  let mode ← match ← text json "mode" with
    | "NONE" => pure Mode.absent | "RO" => pure Mode.readOnly | "RW" => pure Mode.readWrite
    | _ => throw "unknown region mode"
  let minimum ← nat json "min_byte_len"
  let alignment ← nat json "align_bytes"
  require (minimum < 2 ^ 32 && alignment < 2 ^ 32) "region field exceeds 32 bits"
  pure ⟨mode, BitVec.ofNat 32 minimum, BitVec.ofNat 32 alignment⟩

private def entry (json : Json) : Except String EntryReg := do
  let register ← nat json "reg_id"
  let ty ← typeTag (← text json "ty")
  let region ← if ty == .pointer then nat json "region_id" else pure 0
  if r : register < 12 then
    if p : region < 9 then pure ⟨⟨register, r⟩, ty, ⟨region, p⟩⟩
    else throw "entry pointer region out of range"
  else throw "entry register out of range"

private def span (json : Json) : Except String Span := do
  let path ← match json.getObjVal? "path" with
    | .error _ => pure none
    | .ok value => do
      let value ← value.getStr?
      if value.isEmpty then pure (some []) else
        let parts ← (value.splitOn ".").mapM fun part =>
          match part.toNat? with
          | some n => pure n | none => throw "invalid source path"
        pure (some parts)
  pure ⟨← nat json "offset", ← nat json "length", ← text json "template", path⟩

private def program (json : Json) : Except String P1Capture.Program := do
  let spelling ← text json "program_sexpr"
  let source ← P1Source.readText spelling
  let printed ← match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
      MeTTailCore.MeTTaSyntax.petta spelling with
    | .ok raw => pure raw | .error error => throw error.render
  let regions ← (← array json "regions").zipIdx.mapM fun (value, index) => do
    require ((← nat value "region_id") == index) "nonconsecutive region IDs"
    region value
  let entries ← (← array json "entry_regs").mapM entry
  let cost ← json.getObjVal? "cost"
  let image ← json.getObjVal? "image"
  let hex ← text image "bytes_hex"
  require (hex.utf8ByteSize % 2 == 0) "odd number of hexadecimal digits"
  let bytes ← (List.range (hex.utf8ByteSize / 2)).mapM fun index =>
    match NativeImage.hexByte? hex index with
    | some byte => pure byte.toNat | none => throw "invalid byte image"
  let size ← nat image "byte_len"
  require (size == bytes.length && 0 < size) "byte-image extent mismatch"
  let bytes := bytes.toArray
  let data := if positive : 0 < bytes.size then Lean.RArray.ofArray bytes positive else .leaf 0
  let result : P1Capture.Program := ⟨← text json "program_name", ← nat json "program_id",
    source, printed, regions, entries, ← nat cost "fund_points", ← word (← text cost "max_receipt"),
    ← cost.getObjValAs? Bool "max_receipt_fits", size, data, ← text image "sha256",
    ← (← array image "spans").mapM span⟩
  require result.sourceCheck ("p1 source metadata mismatch: " ++ result.name)
  require result.imageCheck ("p1 image/span mismatch: " ++ result.name)
  pure result

def bundle (json : Json) : Except String Bundle := do
  require ((← text json "schema") == "tisa-x86-p1-programs-v2" &&
    (← nat json "schema_version") == 2 && (← text json "profile") == "t-isa-p1")
    "unknown p1 manifest schema"
  let header ← boundary json
  require header.check "p1 ABI boundary mismatch"
  let programs ← (← array json "programs").mapM program
  let declared ← nat json "program_count"
  require (declared == programs.length) "program count mismatch"
  require (decide (programs.map P1Capture.Program.name).Nodup) "duplicate program name"
  require (decide (programs.map P1Capture.Program.id).Nodup) "duplicate program ID"
  pure ⟨header, declared, programs⟩

elab "tisa_p1_bundle% " file:str : term => do
  let contents ← IO.FS.readFile (System.FilePath.mk file.getString)
  match Json.parse contents >>= bundle with
  | .error reason => throwError "p1 native capture: {reason}"
  | .ok data => return toExpr data

end Mettapedia.Machines.TIsa.P1JsonImport
