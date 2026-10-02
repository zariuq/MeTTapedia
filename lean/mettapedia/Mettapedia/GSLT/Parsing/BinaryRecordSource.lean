import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
import Mettapedia.GSLT.Parsing.BinaryRecordCodec
import Init.Data.List.Sort.Lemmas

/-!
# Binary definitions in canonical GSLT source

This admission uses the existing occurrence-preserving source decoder and its
closed signature validation. It then recognizes the deterministic binary
fragment: exactly one word codec and distinct byte opcodes with ordered,
uniquely named operands. The guest-package projection retains its complete
binary component; operational-source admission is a separate boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.BinaryRecordSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing.BinaryRecordCodec
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Source Rewrite Operator)

private def natural? : SExpr → Option Nat
  | .atom token => token.toNat?
  | _ => none

def operand? : SExpr → Option OperandLayout
  | .list [.atom "word", .atom role] => some ⟨.word, role⟩
  | .list [.atom "counted-bytes", .atom role] => some ⟨.countedBytes, role⟩
  | .list [.atom "counted-words", .atom role] => some ⟨.countedWords, role⟩
  | _ => none

def operandList? : SExpr → Option (List OperandLayout)
  | .atom "nil" => some []
  | .list [.atom "cons", head, tail] => do
      let operand ← operand? head
      let rest ← operandList? tail
      if operand.role ∈ rest.map OperandLayout.role then none
      else some (operand :: rest)
  | _ => none
termination_by expression => sizeOf expression
decreasing_by
  simp only [SExpr.list.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
  omega

def encodeOperand (operand : OperandLayout) : SExpr :=
  .list [.atom (match operand.kind with
    | .word => "word"
    | .countedBytes => "counted-bytes"
    | .countedWords => "counted-words"), .atom operand.role]

def encodeOperands : List OperandLayout → SExpr
  | [] => .atom "nil"
  | operand :: rest => .list [.atom "cons", encodeOperand operand, encodeOperands rest]

theorem operand?_encodeOperand (operand : OperandLayout) :
    operand? (encodeOperand operand) = some operand := by
  cases operand with
  | mk kind role => cases kind <;> rfl

theorem operandList?_encodeOperands (operands : List OperandLayout)
    (unique : (operands.map OperandLayout.role).Nodup) :
    operandList? (encodeOperands operands) = some operands := by
  induction operands with
  | nil => simp [encodeOperands, operandList?]
  | cons operand rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [encodeOperands, operandList?, operand?_encodeOperand, ih unique.2]
      change (if operand.role ∈ rest.map OperandLayout.role then none
        else some (operand :: rest)) = some (operand :: rest)
      rw [if_neg unique.1]

inductive Definition where
  | codec (value : WordCodec)
  | opcode (value : OpcodeLayout)
  deriving DecidableEq, Repr

def definition? (rewrite : Rewrite) : Option Definition :=
  if !rewrite.body.isEmpty then none else
  match rewrite.head with
  | .list [.atom "binary-word-codec", .atom _,
      .list [.atom "prefix-word-le64", inlineSyntax, payloadSyntax, .atom policy]] => do
      let inlineMax ← natural? inlineSyntax
      let payloadMax ← natural? payloadSyntax
      let shortest ← if policy == "permissive" then some false
        else if policy == "shortest" then some true else none
      let codec : WordCodec := ⟨inlineMax, payloadMax, shortest⟩
      if codec.Valid then some (.codec codec) else none
  | .list [.atom "binary-opcode", opcodeSyntax, .atom label, operandsSyntax] => do
      let opcode ← natural? opcodeSyntax
      let operands ← operandList? operandsSyntax
      if opcode ≤ 255 then some (.opcode ⟨opcode, label, operands⟩) else none
  | _ => none

def encodeCodec (name : String) (codec : WordCodec) : Rewrite :=
  { name := name
    head := .list [.atom "binary-word-codec", .atom "word64",
      .list [.atom "prefix-word-le64", .atom (toString codec.inlineMax),
        .atom (toString codec.payloadMax),
        .atom (if codec.requireShortest then "shortest" else "permissive")]]
    body := [] }

def encodeOpcode (name : String) (opcode : OpcodeLayout) : Rewrite :=
  { name := name
    head := .list [.atom "binary-opcode", .atom (toString opcode.opcode), .atom opcode.label,
      encodeOperands opcode.operands]
    body := [] }

theorem definition?_encodeCodec (name : String) (codec : WordCodec) (valid : codec.Valid) :
    definition? (encodeCodec name codec) = some (.codec codec) := by
  cases codec with
  | mk inlineMax payloadMax requireShortest =>
      cases requireShortest <;>
        simp [encodeCodec, definition?, natural?, Nat.toNat?_repr, valid]

theorem definition?_encodeOpcode (name : String) (opcode : OpcodeLayout)
    (bounded : opcode.opcode ≤ 255)
    (unique : (opcode.operands.map OperandLayout.role).Nodup) :
    definition? (encodeOpcode name opcode) = some (.opcode opcode) := by
  simp [encodeOpcode, definition?, natural?, Nat.toNat?_repr,
    operandList?_encodeOperands opcode.operands unique, bounded]

theorem definitionList?_encodedOpcodes (opcodes : List (String × OpcodeLayout))
    (valid : ∀ item ∈ opcodes, item.2.opcode ≤ 255 ∧
      (item.2.operands.map OperandLayout.role).Nodup) :
    (opcodes.map fun item => encodeOpcode item.1 item.2).mapM definition? =
      some (opcodes.map fun item => Definition.opcode item.2) := by
  induction opcodes with
  | nil => rfl
  | cons item rest ih =>
      have first := valid item (by simp)
      have tail := ih (fun member inRest => valid member (by simp [inRest]))
      simp [definition?_encodeOpcode item.1 item.2 first.1 first.2, tail]

def operatorAllowed (operator : Operator) : Bool :=
  match operator.name with
  | "binary-word-codec" | "cons" => operator.arity == 2
  | "prefix-word-le64" | "binary-opcode" => operator.arity == 3
  | "word" | "counted-bytes" | "counted-words" => operator.arity == 1
  | _ => false

def assemble? (definitions : List Definition) : Option Grammar := do
  let codecs := definitions.filterMap fun definition => match definition with
    | .codec value => some value
    | _ => none
  let opcodes := definitions.filterMap fun definition => match definition with
    | .opcode value => some value
    | _ => none
  match codecs with
  | [codec] =>
      if opcodes.isEmpty || !(opcodes.map OpcodeLayout.opcode).Nodup then none
      else some ⟨codec, opcodes.mergeSort (fun left right => left.opcode ≤ right.opcode)⟩
  | _ => none

theorem assemble?_codec_sorted (codec : WordCodec) (opcodes : List OpcodeLayout)
    (nonempty : opcodes ≠ []) (unique : (opcodes.map OpcodeLayout.opcode).Nodup)
    (ordered : opcodes.Pairwise (fun left right => left.opcode ≤ right.opcode)) :
    assemble? (.codec codec :: opcodes.map Definition.opcode) = some ⟨codec, opcodes⟩ := by
  have sorted : opcodes.mergeSort (fun left right => left.opcode ≤ right.opcode) = opcodes :=
    List.mergeSort_of_pairwise (l := opcodes)
      (le := fun (left right : OpcodeLayout) => decide (left.opcode ≤ right.opcode))
      (by simpa using ordered)
  simp [assemble?, List.filterMap_map, nonempty, unique, sorted]

def classify? (source : Source) : Option Grammar := do
  if !(Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.compositionValid [source]) ||
      !source.equations.isEmpty || !source.operators.all operatorAllowed ||
      !(source.operators.map (fun operator => (operator.name, operator.arity))).Nodup then none
  else
    let definitions ← source.rewrites.mapM definition?
    assemble? definitions

def admit? (expression : SExpr) : Option Grammar := do
  let source ← Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decode expression
  classify? source

def projectBinary? : SExpr → Option SExpr
  | .list [.atom "gslt-native-guest-v1", .atom _,
      .list [.atom "binary-reader", binary],
      .list [.atom "operations", .list (.atom "gslt-native-ops-v1" :: _)]] => some binary
  | .list [.atom "gslt-native-guest-v1", .atom _,
      .list [.atom "operations", .list (.atom "gslt-native-ops-v1" :: _)],
      .list [.atom "binary-reader", binary]] => some binary
  | _ => none

def guestBinary? (expression : SExpr) : Option Grammar :=
  (projectBinary? expression).bind admit?

def guestBinaryText? (text : String) : Option Grammar :=
  match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta text with
  | .error _ => none
  | .ok expression => guestBinary? expression

def binaryText? (text : String) : Option Grammar :=
  match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta text with
  | .error _ => none
  | .ok expression => admit? expression

theorem binaryText?_of_parsed (text : String) (expression : SExpr) (grammar : Grammar)
    (parsed : Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
      MeTTailCore.MeTTaSyntax.petta text = .ok expression)
    (admitted : admit? expression = some grammar) : binaryText? text = some grammar := by
  unfold binaryText?
  rw [parsed]
  exact admitted

theorem no_binary_without_projection {expression : SExpr}
    (refused : projectBinary? expression = none) : guestBinary? expression = none := by
  simp [guestBinary?, refused]

theorem no_binary_without_admission {expression binary : SExpr}
    (projected : projectBinary? expression = some binary) (refused : admit? binary = none) :
    guestBinary? expression = none := by
  simp [guestBinary?, projected, refused]

example : operandList? (.list [.atom "cons", .list [.atom "word", .atom "slot"],
    .list [.atom "cons", .list [.atom "counted-bytes", .atom "bytes"], .atom "nil"]]) =
    some [⟨.word, "slot"⟩, ⟨.countedBytes, "bytes"⟩] := by
  simp [operandList?, operand?]

example : operandList? (.list [.atom "cons", .list [.atom "word", .atom "slot"],
    .list [.atom "cons", .list [.atom "word", .atom "slot"], .atom "nil"]]) = none := by
  simp [operandList?, operand?]

example : projectBinary? (.list [.atom "gslt-native-guest-v1", .atom "Example",
    .list [.atom "binary-reader", .atom "first"],
    .list [.atom "binary-reader", .atom "second"]]) = none := rfl

end Mettapedia.GSLT.Parsing.BinaryRecordSource
