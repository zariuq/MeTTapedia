import Mathlib.Data.BitVec

/-!
# Exact wire format for compiled finite-Horn plans

The generic CeTTa compiled-plan loader consumes a compact binary carrier.  This
module specifies that carrier independently of the compiler and runtime:

* `CGP1` framing;
* little-endian `UInt32` and signed 64-bit fields;
* length-prefixed, NUL-free byte strings;
* node, child, rule, and body tables; and
* exact rejection of truncation, trailing bytes, and malformed text framing.

The carrier deliberately contains no guest vocabulary.  It is a physical
boundary below an admitted finite-Horn lowering, not a second language
semantics.  Full node-forest and rule-forest admission remain properties of the
compiled-plan validator; the local shape check here is named narrowly so it
cannot be mistaken for that stronger result.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat

abbrev Reader (alpha : Type) := List UInt8 -> Option (alpha × List UInt8)

/-! ## Exact scalar encodings -/

def encodeUInt32LE (value : UInt32) : List UInt8 :=
  let bits := value.toBitVec
  [ UInt8.ofBitVec (bits.extractLsb' 0 8)
  , UInt8.ofBitVec (bits.extractLsb' 8 8)
  , UInt8.ofBitVec (bits.extractLsb' 16 8)
  , UInt8.ofBitVec (bits.extractLsb' 24 8) ]

def readUInt32LE : Reader UInt32
  | byte0 :: byte1 :: byte2 :: byte3 :: rest =>
      some
        (UInt32.ofBitVec
          (byte3.toBitVec ++ byte2.toBitVec ++
            byte1.toBitVec ++ byte0.toBitVec), rest)
  | _ => none

@[simp] theorem readUInt32LE_encodeUInt32LE
    (value : UInt32) (rest : List UInt8) :
    readUInt32LE (encodeUInt32LE value ++ rest) = some (value, rest) := by
  simp only [encodeUInt32LE, List.cons_append, List.nil_append, readUInt32LE]
  congr 2
  apply UInt32.eq_iff_toBitVec_eq.mpr
  simp only
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 24 = 16 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 16 = 8 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 8 = 0 + 8)]
  exact BitVec.extractLsb'_eq_self

def encodeInt64LE (value : Int64) : List UInt8 :=
  let bits := value.toBitVec
  [ UInt8.ofBitVec (bits.extractLsb' 0 8)
  , UInt8.ofBitVec (bits.extractLsb' 8 8)
  , UInt8.ofBitVec (bits.extractLsb' 16 8)
  , UInt8.ofBitVec (bits.extractLsb' 24 8)
  , UInt8.ofBitVec (bits.extractLsb' 32 8)
  , UInt8.ofBitVec (bits.extractLsb' 40 8)
  , UInt8.ofBitVec (bits.extractLsb' 48 8)
  , UInt8.ofBitVec (bits.extractLsb' 56 8) ]

def readInt64LE : Reader Int64
  | byte0 :: byte1 :: byte2 :: byte3 ::
      byte4 :: byte5 :: byte6 :: byte7 :: rest =>
      some
        (Int64.ofBitVec
          (byte7.toBitVec ++ byte6.toBitVec ++
            byte5.toBitVec ++ byte4.toBitVec ++
            byte3.toBitVec ++ byte2.toBitVec ++
            byte1.toBitVec ++ byte0.toBitVec), rest)
  | _ => none

@[simp] theorem readInt64LE_encodeInt64LE
    (value : Int64) (rest : List UInt8) :
    readInt64LE (encodeInt64LE value ++ rest) = some (value, rest) := by
  simp only [encodeInt64LE, List.cons_append, List.nil_append, readInt64LE]
  congr 2
  apply Int64.eq_iff_toBitVec_eq.mpr
  simp only [Int64.toBitVec_ofBitVec]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 56 = 48 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 48 = 40 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 40 = 32 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 32 = 24 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 24 = 16 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 16 = 8 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 8 = 0 + 8)]
  exact BitVec.extractLsb'_eq_self

/-! ## NUL-free length-prefixed byte strings -/

def TextEncodable (bytes : List UInt8) : Prop :=
  bytes.length < UInt32.size ∧ (0 : UInt8) ∉ bytes

def encodeText (bytes : List UInt8) : List UInt8 :=
  encodeUInt32LE (UInt32.ofNat bytes.length) ++ bytes

def readText : Reader (List UInt8) := fun input => do
  let (length, rest) <- readUInt32LE input
  if length.toNat <= rest.length then
    let payload := rest.take length.toNat
    if (0 : UInt8) ∈ payload then
      none
    else
      some (payload, rest.drop length.toNat)
  else
    none

@[simp] theorem readText_encodeText
    (bytes rest : List UInt8) (encodable : TextEncodable bytes) :
    readText (encodeText bytes ++ rest) = some (bytes, rest) := by
  have lengthExact : (UInt32.ofNat bytes.length).toNat = bytes.length := by
    simp [Nat.mod_eq_of_lt encodable.1]
  simp [encodeText, readText, lengthExact, encodable.2]

/-! ## Node and rule records -/

structure Node where
  kind : UInt8
  childOffset : UInt32
  childCount : UInt32
  integerValue : Int64
  variableSlot : UInt32
  text : List UInt8
  deriving DecidableEq, Inhabited, Repr

structure Rule where
  head : UInt32
  bodyOffset : UInt32
  bodyCount : UInt32
  variableCount : UInt32
  name : List UInt8
  deriving DecidableEq, Repr

def encodeNode (node : Node) : List UInt8 :=
  [node.kind] ++
    encodeUInt32LE node.childOffset ++
    encodeUInt32LE node.childCount ++
    encodeInt64LE node.integerValue ++
    encodeUInt32LE node.variableSlot ++
    encodeText node.text

def readByte : Reader UInt8
  | byte :: rest => some (byte, rest)
  | [] => none

def readNode : Reader Node := fun input => do
  let (kind, rest1) <- readByte input
  let (childOffset, rest2) <- readUInt32LE rest1
  let (childCount, rest3) <- readUInt32LE rest2
  let (integerValue, rest4) <- readInt64LE rest3
  let (variableSlot, rest5) <- readUInt32LE rest4
  let (text, rest) <- readText rest5
  some
    ({ kind, childOffset, childCount, integerValue, variableSlot, text }, rest)

@[simp] theorem readNode_encodeNode
    (node : Node) (rest : List UInt8)
    (encodable : TextEncodable node.text) :
    readNode (encodeNode node ++ rest) = some (node, rest) := by
  simp [encodeNode, readNode, readByte, encodable]

def encodeRule (rule : Rule) : List UInt8 :=
  encodeUInt32LE rule.head ++
    encodeUInt32LE rule.bodyOffset ++
    encodeUInt32LE rule.bodyCount ++
    encodeUInt32LE rule.variableCount ++
    encodeText rule.name

def readRule : Reader Rule := fun input => do
  let (head, rest1) <- readUInt32LE input
  let (bodyOffset, rest2) <- readUInt32LE rest1
  let (bodyCount, rest3) <- readUInt32LE rest2
  let (variableCount, rest4) <- readUInt32LE rest3
  let (name, rest) <- readText rest4
  some ({ head, bodyOffset, bodyCount, variableCount, name }, rest)

@[simp] theorem readRule_encodeRule
    (rule : Rule) (rest : List UInt8)
    (encodable : TextEncodable rule.name) :
    readRule (encodeRule rule ++ rest) = some (rule, rest) := by
  simp [encodeRule, readRule, encodable]

/-! ## Complete `CGP1` packets -/

structure Program where
  nodes : List Node
  children : List UInt32
  rules : List Rule
  bodies : List UInt32
  deriving DecidableEq, Repr

def readMany (read : Reader alpha) : Nat -> Reader (List alpha)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (head, rest) <- read input
      let (tail, suffix) <- readMany read count rest
      some (head :: tail, suffix)

theorem readMany_encodeList
    (read : Reader alpha) (encode : alpha -> List UInt8)
    (roundTrip : forall value rest,
      read (encode value ++ rest) = some (value, rest))
    (values : List alpha) (rest : List UInt8) :
    readMany read values.length (values.flatMap encode ++ rest) =
      some (values, rest) := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [readMany, roundTrip, inductionHypothesis]

theorem readMany_encodeNodes
    (nodes : List Node) (rest : List UInt8)
    (encodable : forall node, node ∈ nodes -> TextEncodable node.text) :
    readMany readNode nodes.length (nodes.flatMap encodeNode ++ rest) =
      some (nodes, rest) := by
  induction nodes with
  | nil => rfl
  | cons node nodes inductionHypothesis =>
      have headEncodable := encodable node (by simp)
      have tailEncodable :
          forall candidate, candidate ∈ nodes -> TextEncodable candidate.text := by
        intro candidate member
        exact encodable candidate (by simp [member])
      simp [readMany, headEncodable,
        inductionHypothesis tailEncodable]

theorem readMany_encodeRules
    (rules : List Rule) (rest : List UInt8)
    (encodable : forall rule, rule ∈ rules -> TextEncodable rule.name) :
    readMany readRule rules.length (rules.flatMap encodeRule ++ rest) =
      some (rules, rest) := by
  induction rules with
  | nil => rfl
  | cons rule rules inductionHypothesis =>
      have headEncodable := encodable rule (by simp)
      have tailEncodable :
          forall candidate, candidate ∈ rules -> TextEncodable candidate.name := by
        intro candidate member
        exact encodable candidate (by simp [member])
      simp [readMany, headEncodable,
        inductionHypothesis tailEncodable]

def magic : List UInt8 := [67, 71, 80, 49]

def readMagic : Reader Unit
  | 67 :: 71 :: 80 :: 49 :: rest => some ((), rest)
  | _ => none

def Program.Encodable (program : Program) : Prop :=
  program.nodes.length < UInt32.size ∧
  program.children.length < UInt32.size ∧
  program.rules.length < UInt32.size ∧
  program.bodies.length < UInt32.size ∧
  (forall node, node ∈ program.nodes -> TextEncodable node.text) ∧
  (forall rule, rule ∈ program.rules -> TextEncodable rule.name)

def encodeProgram (program : Program) : List UInt8 :=
  magic ++
    encodeUInt32LE (UInt32.ofNat program.nodes.length) ++
    encodeUInt32LE (UInt32.ofNat program.children.length) ++
    encodeUInt32LE (UInt32.ofNat program.rules.length) ++
    encodeUInt32LE (UInt32.ofNat program.bodies.length) ++
    program.nodes.flatMap encodeNode ++
    program.children.flatMap encodeUInt32LE ++
    program.rules.flatMap encodeRule ++
    program.bodies.flatMap encodeUInt32LE

def readProgram : Reader Program := fun input => do
  let (_, rest0) <- readMagic input
  let (nodeCount, rest1) <- readUInt32LE rest0
  let (childCount, rest2) <- readUInt32LE rest1
  let (ruleCount, rest3) <- readUInt32LE rest2
  let (bodyCount, rest4) <- readUInt32LE rest3
  let (nodes, rest5) <- readMany readNode nodeCount.toNat rest4
  let (children, rest6) <- readMany readUInt32LE childCount.toNat rest5
  let (rules, rest7) <- readMany readRule ruleCount.toNat rest6
  let (bodies, rest) <- readMany readUInt32LE bodyCount.toNat rest7
  some ({ nodes, children, rules, bodies }, rest)

def decodeProgram? (bytes : List UInt8) : Option Program :=
  match readProgram bytes with
  | some (program, []) => some program
  | _ => none

theorem readProgram_encodeProgram
    (program : Program) (rest : List UInt8)
    (encodable : program.Encodable) :
    readProgram (encodeProgram program ++ rest) = some (program, rest) := by
  rcases encodable with
    ⟨nodesFit, childrenFit, rulesFit, bodiesFit,
      nodesEncodable, rulesEncodable⟩
  have nodesExact :
      (UInt32.ofNat program.nodes.length).toNat = program.nodes.length := by
    simp [Nat.mod_eq_of_lt nodesFit]
  have childrenExact :
      (UInt32.ofNat program.children.length).toNat =
        program.children.length := by
    simp [Nat.mod_eq_of_lt childrenFit]
  have rulesExact :
      (UInt32.ofNat program.rules.length).toNat = program.rules.length := by
    simp [Nat.mod_eq_of_lt rulesFit]
  have bodiesExact :
      (UInt32.ofNat program.bodies.length).toNat = program.bodies.length := by
    simp [Nat.mod_eq_of_lt bodiesFit]
  have readNodes := readMany_encodeNodes program.nodes
    (program.children.flatMap encodeUInt32LE ++
      (program.rules.flatMap encodeRule ++
        (program.bodies.flatMap encodeUInt32LE ++ rest)))
    nodesEncodable
  have readChildren := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE
    program.children
    (program.rules.flatMap encodeRule ++
      (program.bodies.flatMap encodeUInt32LE ++ rest))
  have readRules := readMany_encodeRules program.rules
    (program.bodies.flatMap encodeUInt32LE ++ rest) rulesEncodable
  have readBodies := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE
    program.bodies rest
  simp [encodeProgram, readProgram, magic, readMagic, nodesExact, childrenExact,
    rulesExact, bodiesExact]
  rw [readNodes]
  simp only [Option.bind_some]
  rw [readChildren]
  simp only [Option.bind_some]
  rw [readRules]
  simp only [Option.bind_some]
  rw [readBodies]
  simp

@[simp] theorem decodeProgram?_encodeProgram
    (program : Program) (encodable : program.Encodable) :
    decodeProgram? (encodeProgram program) = some program := by
  have readExact : readProgram (encodeProgram program) = some (program, []) := by
    simpa using readProgram_encodeProgram program [] encodable
  unfold decodeProgram?
  rw [readExact]

/-! ## Narrow local-shape admission and cross-runtime canaries -/

def bytesNonempty (bytes : List UInt8) : Bool := !bytes.isEmpty

def bytesNulFree (bytes : List UInt8) : Bool := decide ((0 : UInt8) ∉ bytes)

/-- Executable form of the exact physical-representability boundary.  This is
separate from structural plan admission: it proves that table counts and text
lengths survive the `UInt32` carrier without truncation. -/
def textEncodable? (bytes : List UInt8) : Bool :=
  decide (bytes.length < UInt32.size) && bytesNulFree bytes

def Program.encodable? (program : Program) : Bool :=
  decide (program.nodes.length < UInt32.size) &&
  decide (program.children.length < UInt32.size) &&
  decide (program.rules.length < UInt32.size) &&
  decide (program.bodies.length < UInt32.size) &&
  program.nodes.all (fun node => textEncodable? node.text) &&
  program.rules.all (fun rule => textEncodable? rule.name)

theorem textEncodable?_eq_true_iff (bytes : List UInt8) :
    textEncodable? bytes = true ↔ TextEncodable bytes := by
  simp [textEncodable?, TextEncodable, bytesNulFree]

theorem Program.encodable?_eq_true_iff (program : Program) :
    program.encodable? = true ↔ program.Encodable := by
  simp only [Program.encodable?, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, textEncodable?_eq_true_iff, Program.Encodable]
  tauto

def scalarNodeFieldsAreZero (node : Node) : Bool :=
  node.childOffset == 0 && node.childCount == 0 &&
    node.integerValue == 0 && node.variableSlot == 0

/-- Per-record scalar invariants enforced by the C loader.  Child-table
ownership, depth, and rule-forest coverage are intentionally not claimed here. -/
def Node.locallyValid (node : Node) : Bool :=
  bytesNulFree node.text &&
  match node.kind.toNat with
  | 1 => bytesNonempty node.text && scalarNodeFieldsAreZero node
  | 2 => node.text.isEmpty && node.childOffset == 0 &&
      node.childCount == 0 && node.integerValue == 0
  | 3 => node.childOffset == 0 && node.childCount == 0 &&
      node.integerValue == 0 && node.variableSlot == 0
  | 4 => node.text.isEmpty && node.childOffset == 0 &&
      node.childCount == 0 && node.variableSlot == 0
  | 5 => bytesNonempty node.text && node.integerValue == 0 &&
      node.variableSlot == 0
  | _ => false

def Rule.locallyValid (rule : Rule) : Bool :=
  bytesNonempty rule.name && bytesNulFree rule.name

def Program.headerAndLocalShapesValid (program : Program) : Bool :=
  !program.nodes.isEmpty && !program.rules.isEmpty &&
    program.nodes.all Node.locallyValid &&
    program.rules.all Rule.locallyValid

def canaryNode : Node :=
  { kind := 5
    childOffset := 0
    childCount := 0
    integerValue := 0
    variableSlot := 0
    text := [114, 101, 97, 100, 121] }

def canaryRule : Rule :=
  { head := 0
    bodyOffset := 0
    bodyCount := 0
    variableCount := 0
    name := [114, 101, 97, 100, 121, 45, 114, 117, 108, 101] }

def canaryProgram : Program :=
  { nodes := [canaryNode]
    children := []
    rules := [canaryRule]
    bodies := [] }

def canaryBytes : List UInt8 :=
  [ 67, 71, 80, 49,
    1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    5, 0, 0, 0, 114, 101, 97, 100, 121,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    10, 0, 0, 0, 114, 101, 97, 100, 121, 45, 114, 117, 108, 101 ]

theorem canaryProgram_encodable : canaryProgram.Encodable := by
  simp [Program.Encodable, canaryProgram, canaryNode, canaryRule,
    TextEncodable]
  decide

theorem encodeProgram_canaryProgram :
    encodeProgram canaryProgram = canaryBytes := by decide

theorem decodeProgram?_canaryBytes :
    decodeProgram? canaryBytes = some canaryProgram := by
  rw [← encodeProgram_canaryProgram]
  exact decodeProgram?_encodeProgram canaryProgram canaryProgram_encodable

theorem canaryProgram_local_shapes_valid :
    canaryProgram.headerAndLocalShapesValid = true := by decide

theorem decodeProgram?_rejects_trailing_canary_byte :
    decodeProgram? (canaryBytes ++ [0]) = none := by decide

theorem decodeProgram?_rejects_corrupt_canary_magic :
    decodeProgram? (0 :: canaryBytes.tail) = none := by decide

def nulTextProgram : Program :=
  { canaryProgram with
    nodes := [{ canaryNode with text := [0] }] }

theorem decodeProgram?_rejects_nul_text :
    decodeProgram? (encodeProgram nulTextProgram) = none := by decide

def unknownKindProgram : Program :=
  { canaryProgram with
    nodes := [{ canaryNode with kind := 0 }] }

theorem unknown_kind_packet_decodes :
    decodeProgram? (encodeProgram unknownKindProgram) = some unknownKindProgram := by
  exact decodeProgram?_encodeProgram unknownKindProgram (by
    simp [Program.Encodable, unknownKindProgram, canaryProgram,
      canaryNode, canaryRule, TextEncodable]
    decide)

theorem unknown_kind_fails_local_shape_admission :
    unknownKindProgram.headerAndLocalShapesValid = false := by decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
