import Lean
import Lean.Data.RArray
import Mettapedia.Machines.TIsa.TheoryData
import Mettapedia.Machines.TIsa.Layout
import Mettapedia.Machines.TIsa.NativeImage

/-!
# External JSON adapter for actual native rule tables

The importer runs during elaboration and quotes ordinary data constructors.
Core matching, compilation and resource semantics do not import this module
or execute JSON. Redundant FL and rendered-plan fields are cross-checked.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.JsonImport

open Lean Elab Term RuleTable TheoryData

deriving instance ToExpr for Atom
deriving instance ToExpr for Pattern
deriving instance ToExpr for Rule
deriving instance ToExpr for Coordinate
deriving instance ToExpr for Source
deriving instance ToExpr for Guard
deriving instance ToExpr for Shape
deriving instance ToExpr for Plan
deriving instance ToExpr for Role
deriving instance ToExpr for Entry
deriving instance ToExpr for ScalarType
deriving instance ToExpr for Registers.Placement
deriving instance ToExpr for LayoutField
deriving instance ToExpr for Layout
deriving instance ToExpr for NativeBoundary
deriving instance ToExpr for NativeImage.Patch
deriving instance ToExpr for NativeImage.Span
deriving instance ToExpr for NativeImage.TemplateSample

private def naturalTreeExpr : Lean.RArray Nat → Expr
  | .leaf value => mkApp2 (mkConst ``Lean.RArray.leaf [0]) (mkConst ``Nat) (mkRawNatLit value)
  | .branch pivot left right => mkApp4 (mkConst ``Lean.RArray.branch [0]) (mkConst ``Nat)
      (mkRawNatLit pivot) (naturalTreeExpr left) (naturalTreeExpr right)

instance : ToExpr (Lean.RArray Nat) where
  toExpr := naturalTreeExpr
  toTypeExpr := mkApp (mkConst ``Lean.RArray [0]) (mkConst ``Nat)

deriving instance ToExpr for NativeImage.Image

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def word (text : String) : Except String RuleTable.Word := do
  require (text.startsWith "0x" && text.length == 18) "expected exact 16-digit hexadecimal word"
  let value ← text.toList.drop 2 |>.foldlM (fun value digit => do
    let number := digit.toNat
    let nibble ← if 48 ≤ number && number ≤ 57 then pure (number - 48)
      else if 97 ≤ number && number ≤ 102 then pure (number - 87)
      else throw "invalid hexadecimal digit"
    pure (16 * value + nibble)) 0
  require (value < 2 ^ 64) "word exceeds 64 bits"
  pure (BitVec.ofNat 64 value)

private def array (json : Json) (key : String) : Except String (List Json) :=
  (json.getObjVal? key >>= Json.getArr?).map Array.toList

private def nat (json : Json) (key : String) : Except String Nat := json.getObjValAs? Nat key
private def string (json : Json) (key : String) : Except String String := json.getObjValAs? String key
private def boolean (json : Json) (key : String) : Except String Bool := json.getObjValAs? Bool key

private def atom (json : Json) : Except String Atom := do
  match ← string json "kind" with
  | "var" => pure (.variable (← nat json "var"))
  | "const" => pure (.literal (← word (← string json "u64_payload_hex")))
  | _ => throw "unsupported source atom"

private def pattern (json : Json) : Except String Pattern := do
  let tag ← nat json "wtag"
  let constructor ← nat json "con_id"
  let space ← nat json "space_id"
  require (space < 256 && constructor < 2 ^ 23) "tag coordinate out of range"
  require (tag == ((constructor <<< 9) ||| (space <<< 1) ||| 1)) "inconsistent constructor/space tag"
  let arguments ← array json "args"
  require ((← nat json "arity") == arguments.length) "source arity differs from payload"
  let fields ← arguments.zipIdx.mapM fun (argument, index) => do
    require ((← nat argument "arg_idx") == index) "source argument positions are not consecutive"
    atom argument
  pure ⟨tag, fields⟩

private def source (json : Json) : Except String Source := do
  match ← string json "kind" with
  | "field" => pure (.field ⟨← nat json "premise", ← nat json "field"⟩)
  | "literal" => pure (.literal (← word (← string json "u64_payload_hex")))
  | _ => throw "unsupported gather source"

private def renderedPlan (json : Json) : Except String Plan := do
  let inputs ← (← array json "inputs").mapM fun shape =>
    return (⟨← nat shape "tag", ← nat shape "arity"⟩ : Shape)
  let guards ← (← array json "guards").mapM fun guard =>
    return (⟨← source (← guard.getObjVal? "left"), ← source (← guard.getObjVal? "right")⟩ : Guard)
  pure ⟨inputs, guards, ← nat json "output_tag", ← (← array json "output_fields").mapM source⟩

private def flatPlan (json : Json) (premises : List Pattern) : Except String Plan := do
  require (← boolean json "ordinary") "non-ordinary FL plan"
  let tags ← (← array json "ktag").mapM Json.getNat?
  require (tags == premises.map Pattern.tag) "FL premise tags differ from source tags"
  let constants ← (← array json "constants").mapM fun constant => do
    word (← string constant "u64_payload_hex")
  require ((← nat json "nconst") == constants.length) "FL constant count mismatch"
  let read (i j : Nat) : Except String Source :=
    if i = premises.length then
      match constants[j]? with
      | some value => pure (.literal value)
      | none => throw "FL constant coordinate out of range"
    else match premises[i]? with
      | some premise =>
          if j < premise.fields.length then pure (.field ⟨i, j⟩)
          else throw "FL field coordinate out of range"
      | none => throw "FL premise coordinate out of range"
  let guards ← (← array json "guards").zipIdx.mapM fun (guard, index) => do
    let i ← nat guard "i"
    let j ← nat guard "j"
    let i0 ← nat guard "i0"
    let j0 ← nat guard "j0"
    require ((← nat guard "guard_idx") == index) "FL guard index mismatch"
    require (i < 256 && j < 256 && i0 < 256 && j0 < 256) "FL packed guard exceeds byte coordinates"
    require ((← nat guard "packed_guard") == (i ||| (j <<< 8) ||| (i0 <<< 16) ||| (j0 <<< 24)))
      "FL packed guard mismatch"
    pure (⟨← read i j, ← read i0 j0⟩ : Guard)
  require ((← nat json "nguard") == guards.length) "FL guard count mismatch"
  let output ← (← array json "make_coords").zipIdx.mapM fun (coordinate, index) => do
    let i ← nat coordinate "mi"
    let j ← nat coordinate "mj"
    require ((← nat coordinate "out_arg") == index) "FL output position mismatch"
    require (i < 256 && j < 256) "FL packed output exceeds byte coordinates"
    require ((← nat coordinate "packed_make") == (i ||| (j <<< 8))) "FL packed output mismatch"
    read i j
  require ((← nat json "mar") == output.length) "FL output arity mismatch"
  pure ⟨premises.map Pattern.shape, guards, ← nat json "mtag", output⟩

private def entry (json : Json) : Except String Entry := do
  for field in ["ntake", "nabsent", "ncount", "ntell", "nneq"] do
    require ((← nat json field) == 0) "entry outside pure keep/make fragment"
  require ((← json.getObjValAs? Int "fresh") == -1) "fresh-name rule outside profile"
  require (← boolean json "pure") "non-pure rule outside profile"
  let id ← nat json "rule_id"
  let name ← string json "name"
  let variableCount ← nat json "nvars"
  let context ← array json "context_vars"
  require (context.length == variableCount) "context-variable count mismatch"
  for (binder, index) in context.zipIdx do
    require ((← nat binder "var") == index && (← nat binder "sort_id") == 1 &&
      (← nat binder "bound") == 0) "context outside unbound ID-word profile"
    require ((← word (← string binder "avoid_mask_hex")) == 0) "nonempty avoidance constraint"
  let premises ← (← array json "keep_premises").mapM pattern
  require ((← nat json "nkeep") == premises.length) "premise count mismatch"
  let conclusion ← pattern (← json.getObjVal? "make_conclusion")
  let role ← string json "role"
  match role with
  | "privileged_leaf_publisher" =>
      require ((← boolean json "mflat") && !(← boolean json "flat") && premises.isEmpty)
        "invalid publisher profile"
      require ((← json.getObjVal? "compiled_flat") == .null &&
        (← json.getObjVal? "rule_table_plan") == .null) "publisher contains a premise plan"
      pure ⟨id, name, .publisher, variableCount, ⟨premises, conclusion⟩, none⟩
  | "premise_bearing_flat_rule" =>
      require ((← boolean json "flat") && !(← boolean json "mflat")) "invalid premise profile"
      let compiled ← flatPlan (← json.getObjVal? "compiled_flat") premises
      let rendered ← renderedPlan (← json.getObjVal? "rule_table_plan")
      require (compiled == rendered) "rendered plan disagrees with actual FL coordinates"
      require (compiled.outputTag == conclusion.tag && compiled.outputFields.length == conclusion.fields.length)
        "FL conclusion shape differs from source"
      pure ⟨id, name, .premise, variableCount, ⟨premises, conclusion⟩, some compiled⟩
  | _ => throw "unknown rule role"

def theory (json : Json) : Except String (List Entry) := do
  require ((← string json "schema") == "tcalc.lean_theory_and_tisa_contract.v1" &&
    (← nat json "schema_version") == 1) "unknown theory schema"
  require ((← string json "profile_version") == "t-isa-p0-v1") "unknown native profile"
  (← array json "rules").mapM entry

private def registerNames : Registers.Architecture → List String
  | .x86_64 => ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] ++
      (List.range' 8 8).map (fun index => "r" ++ toString index)
  | .aarch64 => (List.range 32).map (fun index => "x" ++ toString index)
  | .rv64 => ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1"] ++
      (List.range 8).map (fun index => "a" ++ toString index) ++
      (List.range' 2 10).map (fun index => "s" ++ toString index) ++ ["t3", "t4", "t5", "t6"]

private def registers (architecture : Registers.Architecture) (values : List Json) :
    Except String (List Nat) :=
  values.mapM fun value => do
    let name ← value.getStr?
    let names := registerNames architecture
    require (names.contains name) "unknown architectural register"
    pure (names.idxOf name)

private def scalarType (name : String) : Except String ScalarType := do
  if name == "U64" then return .u64
  if name.startsWith "Ptr(" && name.endsWith ")" then
    match (name.toList.drop 4 |>.take (name.length - 5) |> String.ofList).toNat? with
    | some region => return .pointer region
    | none => throw "malformed pointer region"
  throw "unsupported runtime-frame field type"

private def hexBytes : List Char → Except String (List (BitVec 8))
  | [] => pure []
  | high :: low :: later => do
      let text := "0x00000000000000" ++ String.ofList [high, low]
      let byte ← word text
      pure (byte.extractLsb' 0 8 :: (← hexBytes later))
  | [_] => throw "odd-length byte image"

def boundary (json : Json) : Except String NativeBoundary := do
  require ((← string json "semantic_authority") == "tcalc_resource_interaction_take_keep_make")
    "native boundary has another semantic authority"
  let frame ← json.getObjVal? "runtime_frame_layout"
  let fields ← (← array frame "fields").mapM fun field => do
    pure (⟨← string field "name", ← nat field "offset", ← nat field "size",
      ← scalarType (← string field "type")⟩ : LayoutField)
  let frameLayout : Layout := ⟨← nat frame "sizeof_bytes", ← nat frame "alignof_bytes", fields⟩
  let tuple ← json.getObjVal? "tuple_layout"
  require ((← nat tuple "arg_count") == 3 && (← nat tuple "max_arity") == 3) "unknown tuple arity"
  let argumentOffset ← nat tuple "args_offset"
  let argumentStride ← nat tuple "arg_stride_bytes"
  let arguments := (List.range 3).map fun index =>
    (⟨"arg" ++ toString index, argumentOffset + index * argumentStride, 8, .u64⟩ : LayoutField)
  let tupleFields :=
    (⟨"tag", ← nat tuple "tag_offset", ← nat tuple "tag_width_bytes", .u32z⟩ : LayoutField) ::
    ⟨"pad", ← nat tuple "pad_offset", ← nat tuple "pad_width_bytes", .u32z⟩ :: arguments
  let tupleLayout : Layout := ⟨← nat tuple "sizeof_bytes", ← nat tuple "alignof_bytes", tupleFields⟩
  let abi ← json.getObjVal? "abi_contract"
  require ((← nat abi "num_logical_registers") == 12) "unknown logical register count"
  let logical ← (← array abi "logical_registers").mapM Json.getStr?
  require (logical == (List.range 12).map (fun index => "v" ++ toString index)) "logical register order mismatch"
  let scratch ← abi.getObjVal? "scratch_registers"
  require ((← array scratch "logical") == [Json.str "s0", Json.str "s1"]) "scratch register order mismatch"
  let x86 ← registers .x86_64 ((← array abi "x86_64_registers") ++ (← array scratch "x86_64"))
  let aarch64 ← registers .aarch64 ((← array abi "aarch64_registers") ++ (← array scratch "aarch64"))
  let rv64 ← registers .rv64 ((← array abi "rv64_registers") ++ (← array scratch "rv64"))
  let saved ← registers .x86_64 (← array abi "x86_64_wrapper_saved")
  pure ⟨frameLayout, tupleLayout, ⟨x86, saved⟩, ⟨aarch64, []⟩, ⟨rv64, []⟩,
    ← hexBytes (← string abi "x86_64_wrapper_prologue_bytes_hex").toList,
    ← hexBytes (← string abi "x86_64_wrapper_epilogue_bytes_hex").toList⟩

private def smallHex (text : String) : Except String Nat := do
  require (text.startsWith "0x" && 2 < text.length && text.length ≤ 18) "invalid bounded hexadecimal field"
  let padded := "0x" ++ String.ofList (List.replicate (18 - text.length) '0') ++
    String.ofList (text.toList.drop 2)
  pure (← word padded).toNat

private def patch (json : Json) : Except String NativeImage.Patch := do
  let opcode ← smallHex (← string json "cc_op")
  require (opcode < 256) "branch opcode exceeds one byte"
  pure ⟨← nat json "opcode_offset", ← nat json "disp_offset", ← nat json "next_ip",
    ← nat json "target_offset", BitVec.ofNat 8 opcode, opcode != 233,
    ← json.getObjValAs? Int "rel32", ← boolean json "patched"⟩

private def image (json : Json) : Except String NativeImage.Image := do
  require ((← nat json "schema_version") == 1) "unknown program-image schema"
  require ((← string json "verification_status") == "pending_formal_proof") "unrecognized image evidence status"
  let artifact ← json.getObjVal? "x86_64_artifact"
  require ((← string artifact "target_profile") == "P0_BASELINE_X86_64") "image outside baseline profile"
  let hex ← string artifact "bytes_hex"
  require (hex.utf8ByteSize % 2 == 0 && hex.toByteArray.data.all (fun byte => (NativeImage.hexDigit? byte).isSome))
    "invalid image hexadecimal bytes"
  let byteLength := hex.utf8ByteSize / 2
  require ((← nat artifact "byte_len") == byteLength) "image byte length mismatch"
  let bytes := (← hexBytes hex.toList).toArray.map BitVec.toNat
  let data := if positive : 0 < bytes.size then Lean.RArray.ofArray bytes positive else .leaf 0
  let spans ← (← array artifact "emitted_spans").zipIdx.mapM fun (span, index) => do
    require ((← nat span "span_idx") == index) "nonconsecutive template span index"
    pure (⟨← nat span "byte_offset", ← nat span "byte_len", ← string span "kind"⟩ : NativeImage.Span)
  let branches ← (← array artifact "patched_branches").zipIdx.mapM fun (branch, index) => do
    require ((← nat branch "branch_idx") == index) "nonconsecutive branch index"
    patch branch
  require ((← nat artifact "branch_count") == branches.length) "branch count mismatch"
  let epilogue ← nat artifact "epilogue_offset"
  require ((← nat artifact "epilogue_len") + epilogue == byteLength) "epilogue extent mismatch"
  require ((← nat artifact "prologue_offset") == 0 &&
    (← nat artifact "prologue_len") == (← nat artifact "body_offset")) "prologue extent mismatch"
  pure ⟨← string json "program_name", ← nat json "program_id", byteLength, data,
    ← nat artifact "body_offset", epilogue, spans, branches⟩

def nativeImages (json : Json) : Except String (List NativeImage.Image) := do
  require ((← string json "schema") == "tisa-x86-programs-bundle-v1" &&
    (← string json "profile") == "t-isa-core-v1") "unknown native image bundle"
  let programs ← array json "programs"
  require ((← nat json "program_count") == programs.length) "program count mismatch"
  programs.mapM image

private def movCapture (json : Json) : Except String (List Nat × List (Nat × Nat × List Nat)) := do
  require ((← string json "schema") == "tisa-mov-helper-v1") "unknown MOV helper capture"
  let registers ← (← array json "registers").mapM Json.getNat?
  require (registers.all (· < 16)) "invalid physical register"
  let rows ← (← array json "rows").mapM fun row => do
    let destination ← nat row "dst"
    let source ← nat row "src"
    let bytes ← (← array row "bytes").mapM Json.getNat?
    require (destination < registers.length && source < registers.length) "invalid MOV register slot"
    require (bytes.all (· ≤ 255)) "invalid instruction byte"
    pure (destination, source, bytes)
  pure (registers, rows)

private def templateCapture (json : Json) :
    Except String (List Nat × List NativeImage.TemplateSample) := do
  require ((← string json "schema") == "tisa-template-capture-v1") "unknown template capture"
  let registers ← (← array json "registers").mapM Json.getNat?
  require (registers.all (· < 16)) "invalid physical register"
  let samples ← (← array json "samples").mapM fun sample => do
    let inputs ← (← array sample "inputs").mapM Json.getNat?
    let bytes ← (← array sample "bytes").mapM Json.getNat?
    require (bytes.all (· ≤ 255)) "invalid template byte"
    let spans ← (← array sample "spans").mapM fun span =>
      return (⟨← nat span "offset", ← nat span "length", ← string span "kind"⟩ : NativeImage.Span)
    pure (⟨inputs, bytes, spans, ← nat sample "scratch_mask"⟩ : NativeImage.TemplateSample)
  pure (registers, samples)

private def hostingInventory (json : Json) : Except String (List (Nat × List String × List String)) := do
  require ((← string json "schema") == "tisa-x86-programs-bundle-v1") "unknown native bundle"
  (← array json "programs").mapM fun program => do
    let protocol ← program.getObjVal? "hosting_protocol"
    let carriers ← (← array protocol "carrier_rules").mapM Json.getStr?
    let controls ← (← array protocol "control_rules").mapM Json.getStr?
    pure (← nat program "program_id", carriers, controls)

elab "tisa_hosting_inventory% " file:str : term => do
  let text ← IO.FS.readFile (System.FilePath.mk file.getString)
  match Json.parse text >>= hostingInventory with
  | .error reason => throwError "native hosting inventory: {reason}"
  | .ok data => return toExpr data

elab "tisa_mov_capture% " file:str : term => do
  let text ← IO.FS.readFile (System.FilePath.mk file.getString)
  match Json.parse text >>= movCapture with
  | .error reason => throwError "native MOV capture: {reason}"
  | .ok data => return toExpr data

elab "tisa_template_capture% " file:str : term => do
  let text ← IO.FS.readFile (System.FilePath.mk file.getString)
  match Json.parse text >>= templateCapture with
  | .error reason => throwError "native template capture: {reason}"
  | .ok data =>
      let element := toTypeExpr NativeImage.TemplateSample
      let listType := toTypeExpr (List NativeImage.TemplateSample)
      let bytesType := toTypeExpr (List Nat)
      let spansType := toTypeExpr (List NativeImage.Span)
      let bytesAppend := mkApp (mkConst ``List.append [0]) (toTypeExpr Nat)
      let nil := mkApp (mkConst ``List.nil [0]) element
      let cons := mkApp (mkConst ``List.cons [0]) element
      let mut remaining := data.2
      let mut chunks := []
      let mut sharedPrefixes : List (List Nat × Expr) := []
      let mut sharedSpans : List (List NativeImage.Span × Expr) := []
      while !remaining.isEmpty do
        let chunk := remaining.take 32
        remaining := remaining.drop 32
        let mut values := []
        for sample in chunk do
          let prefixLength := match sample.spans.head? with
            | some span => if span.kind == "FUEL_STEP" && span.offset == 0 then span.length else 0
            | none => 0
          let fuelPrefix := sample.bytes.take prefixLength
          let prefixExpr ← match sharedPrefixes.find? (fun entry => entry.1 == fuelPrefix) with
            | some entry => pure entry.2
            | none =>
              let named ← Meta.mkAuxDefinition (← mkAuxDeclName (kind := `native_prefix))
                bytesType (toExpr fuelPrefix) (compile := false)
              sharedPrefixes := (fuelPrefix, named) :: sharedPrefixes
              pure named
          let spansExpr ← match sharedSpans.find? (fun entry => decide (entry.1 = sample.spans)) with
            | some entry => pure entry.2
            | none =>
              let named ← Meta.mkAuxDefinition (← mkAuxDeclName (kind := `native_sample_spans))
                spansType (toExpr sample.spans) (compile := false)
              sharedSpans := (sample.spans, named) :: sharedSpans
              pure named
          let bytes := mkApp2 bytesAppend prefixExpr (toExpr (sample.bytes.drop prefixLength))
          let value := mkApp4 (mkConst ``NativeImage.TemplateSample.mk)
            (toExpr sample.inputs) bytes spansExpr (toExpr sample.scratchMask)
          values := value :: values
        let body := values.foldl (fun later value => mkApp2 cons value later) nil
        let named ← Meta.mkAuxDefinition (← mkAuxDeclName (kind := `native_samples))
          listType body (compile := false)
        chunks := named :: chunks
      let append := mkApp (mkConst ``List.append [0]) element
      let samples := chunks.foldl (fun later chunk => mkApp2 append chunk later) nil
      return mkApp4 (mkConst ``Prod.mk [0, 0]) (toTypeExpr (List Nat)) listType
        (toExpr data.1) samples

/-- Parsing yields literal data terms; no JSON parser is in their runtime meaning. -/
elab "tisa_theory% " file:str : term => do
  let text ← IO.FS.readFile (System.FilePath.mk file.getString)
  match Json.parse text >>= theory with
  | .error reason => throwError "native rule table: {reason}"
  | .ok entries => return toExpr entries

elab "tisa_boundary% " file:str : term => do
  let text ← IO.FS.readFile (System.FilePath.mk file.getString)
  match Json.parse text >>= boundary with
  | .error reason => throwError "native layout and register boundary: {reason}"
  | .ok data => return toExpr data

elab "tisa_images% " file:str : term => do
  let text ← IO.FS.readFile (System.FilePath.mk file.getString)
  match Json.parse text >>= nativeImages with
  | .error reason => throwError "native program images: {reason}"
  | .ok data =>
      let mut values := []
      for value in data do
        let bytes ← Meta.mkAuxDefinition (← mkAuxDeclName (kind := `native_bytes))
          (toTypeExpr (Lean.RArray Nat)) (toExpr value.data) (compile := false)
        let spans ← Meta.mkAuxDefinition (← mkAuxDeclName (kind := `native_spans))
          (toTypeExpr (List NativeImage.Span)) (toExpr value.spans) (compile := false)
        let branches ← Meta.mkAuxDefinition (← mkAuxDeclName (kind := `native_branches))
          (toTypeExpr (List NativeImage.Patch)) (toExpr value.branches) (compile := false)
        let body := mkAppN (mkConst ``NativeImage.Image.mk) #[
          toExpr value.name, toExpr value.id, toExpr value.size, bytes,
          toExpr value.bodyOffset, toExpr value.epilogueOffset, spans, branches]
        let named ← Meta.mkAuxDefinition (← mkAuxDeclName (kind := `native_image))
          (toTypeExpr NativeImage.Image) body (compile := false)
        values := named :: values
      let element := toTypeExpr NativeImage.Image
      let empty := mkApp (mkConst ``List.nil [0]) element
      let cons := mkApp (mkConst ``List.cons [0]) element
      return values.foldl (fun later value => mkApp2 cons value later) empty

end Mettapedia.Machines.TIsa.JsonImport
