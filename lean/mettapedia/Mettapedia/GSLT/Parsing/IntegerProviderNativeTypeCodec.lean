import Mettapedia.GSLT.Parsing.SourceIntegerProviderNativeType

/-!
# Structured export of inferred integer-provider completion types

The wire uses the existing MeTTa S-expression carrier. It retains ordered
source syntax and each inferred equation occurrence, relation, comparison
polarity, and successor flag. The versioned binary tag denotes the existing
two-integer, zero-or-one echoed-answer completion type, not an arbitrary type
label supplied by a caller.

Inference reads the existing structured source equations directly; this
module introduces neither an intermediate program nor a grammar calculus.
The structured codec and source authentication below do not prove a byte
parser, source-to-target compiler, or fixed-width integer implementation.
Source binding is exact semantic S-expression syntax, not original whitespace
or comment bytes. The embedded sources are compile-time input, not a runtime
rule table.
-/

namespace Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeCodec

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open SourceIntegerProvider
open SourceIntegerProviderNativeType

def encodePolarity : Bool → SExpr
  | false => .atom "less"
  | true => .atom "not-less"

def decodePolarity : SExpr → Option Bool
  | .atom "less" => some false
  | .atom "not-less" => some true
  | _ => none

def encodeSuccessor : Bool → SExpr
  | false => .atom "direct"
  | true => .atom "successor"

def decodeSuccessor : SExpr → Option Bool
  | .atom "direct" => some false
  | .atom "successor" => some true
  | _ => none

@[simp] theorem decodePolarity_encode (value : Bool) :
    decodePolarity (encodePolarity value) = some value := by cases value <;> rfl

@[simp] theorem decodeSuccessor_encode (value : Bool) :
    decodeSuccessor (encodeSuccessor value) = some value := by cases value <;> rfl

def encodeInfo (info : BinaryTypeInfo) : SExpr :=
  .list [.atom "binary-integer-completion-v1", .atom (toString info.occurrence),
    .atom info.relation, encodePolarity info.notLess, encodeSuccessor info.successor]

private def decodeInfoRaw : SExpr → Option BinaryTypeInfo
  | .list [.atom "binary-integer-completion-v1", .atom occurrence, .atom relation,
      polarity, successor] => do
      return ⟨← occurrence.toNat?, relation, ← decodePolarity polarity, ← decodeSuccessor successor⟩
  | _ => none

/-- Re-encoding excludes noncanonical occurrence tokens, such as leading zeros.
This is exact structured decoding, not forgiving reinterpretation. -/
def decodeInfo (wire : SExpr) : Option BinaryTypeInfo := do
  let info ← decodeInfoRaw wire
  if encodeInfo info = wire then some info else none

@[simp] theorem decodeInfo_encode (info : BinaryTypeInfo) :
    decodeInfo (encodeInfo info) = some info := by
  rcases info with ⟨occurrence, relation, notLess, successor⟩
  simp [decodeInfo, decodeInfoRaw, encodeInfo, Nat.toNat?_repr]

theorem encodeInfo_of_decode {wire : SExpr} {info : BinaryTypeInfo}
    (decoded : decodeInfo wire = some info) : encodeInfo info = wire := by
  cases raw : decodeInfoRaw wire with
  | none => simp [decodeInfo, raw] at decoded
  | some result =>
      by_cases canonical : encodeInfo result = wire
      · have same : result = info := by simpa [decodeInfo, raw, canonical] using decoded
        simpa [same] using canonical
      · simp [decodeInfo, raw, canonical] at decoded

theorem encodeInfo_injective : Function.Injective encodeInfo := by
  intro left right same
  have decoded := congrArg decodeInfo same
  simpa using decoded

structure Packet where
  sourceSyntax : List SExpr
  types : List BinaryTypeInfo
  deriving DecidableEq, Repr

def encodePacket (packet : Packet) : SExpr :=
  .list [.atom "integer-provider-native-types-v1",
    .list (.atom "source-composition" :: packet.sourceSyntax),
    .list (.atom "types" :: packet.types.map encodeInfo)]

private def decodePacketRaw : SExpr → Option Packet
  | .list [.atom "integer-provider-native-types-v1",
      .list (.atom "source-composition" :: sources), .list (.atom "types" :: rows)] => do
      return ⟨sources, ← decodeList decodeInfo rows⟩
  | _ => none

def decodePacket (wire : SExpr) : Option Packet := do
  let packet ← decodePacketRaw wire
  if encodePacket packet = wire then some packet else none

@[simp] theorem decodePacket_encode (packet : Packet) :
    decodePacket (encodePacket packet) = some packet := by
  rcases packet with ⟨sources, types⟩
  simp [decodePacket, decodePacketRaw, encodePacket,
    decodeList_map_encode decodeInfo encodeInfo decodeInfo_encode]

theorem encodePacket_of_decode {wire : SExpr} {packet : Packet}
    (decoded : decodePacket wire = some packet) : encodePacket packet = wire := by
  cases raw : decodePacketRaw wire with
  | none => simp [decodePacket, raw] at decoded
  | some result =>
      by_cases canonical : encodePacket result = wire
      · have same : result = packet := by simpa [decodePacket, raw, canonical] using decoded
        simpa [same] using canonical
      · simp [decodePacket, raw, canonical] at decoded

theorem encodePacket_injective : Function.Injective encodePacket := by
  intro left right same
  have decoded := congrArg decodePacket same
  simpa using decoded

/-- Decode and validate the actual ordered source composition. The selected
provider meaning does not interpret authored equational congruence, so a
nonempty equation section is refused. No provider relation list or alternate
program representation is an input or output. -/
def decodeSource? (rawSources : List SExpr) : Option (List Source) := do
  let sources ← decodeList decode rawSources
  if compositionValid sources && sources.all (fun source => source.equations.isEmpty)
    then some sources else none

theorem decodedSource_equations_empty {rawSources : List SExpr} {sources : List Source}
    (decoded : decodeSource? rawSources = some sources) :
    ∀ source ∈ sources, source.equations = [] := by
  cases parsed : decodeList decode rawSources with
  | none => simp [decodeSource?, parsed] at decoded
  | some actual =>
      have result : compositionValid actual = true ∧
          (actual.all fun source => source.equations.isEmpty) = true ∧ actual = sources := by
        simpa [decodeSource?, parsed, and_assoc] using decoded
      rcases result with ⟨_, emptyEquations, rfl⟩
      simpa using List.all_eq_true.mp emptyEquations

def inferredInfos (sources : List Source) : List BinaryTypeInfo :=
  (inferBinaryTypes sources).map BinaryJudgment.info

def inferPacket? (rawSources : List SExpr) : Option Packet := do
  let sources ← decodeSource? rawSources
  return ⟨rawSources, inferredInfos sources⟩

/-- Exact source syntax and the whole inferred occurrence list are checked.
Dropping, inserting, reordering, or changing an inferred row cannot pass unless
it produces exactly the independently recomputed result for this composition. -/
def Authentic (expectedSource : List SExpr) (packet : Packet) : Prop :=
  match decodeSource? expectedSource with
  | none => False
  | some program => packet.sourceSyntax = expectedSource ∧ packet.types = inferredInfos program

instance (expectedSource : List SExpr) (packet : Packet) : Decidable (Authentic expectedSource packet) := by
  unfold Authentic
  split <;> infer_instance

def authenticate (expectedSource : List SExpr) (packet : Packet) : Bool :=
  decide (Authentic expectedSource packet)

theorem authenticate_iff (expectedSource : List SExpr) (packet : Packet) :
    authenticate expectedSource packet = true ↔ Authentic expectedSource packet := by
  simp [authenticate]

theorem inferred_packet_authentic {rawSources : List SExpr} {packet : Packet}
    (inferred : inferPacket? rawSources = some packet) : Authentic rawSources packet := by
  cases elaborated : decodeSource? rawSources with
  | none => simp [inferPacket?, elaborated] at inferred
  | some program =>
      have same : (⟨rawSources, inferredInfos program⟩ : Packet) = packet := by
        simpa [inferPacket?, elaborated] using inferred
      simp [Authentic, elaborated, ← same]

theorem authenticated_source_exact {rawSources : List SExpr} {packet : Packet}
    (accepted : authenticate rawSources packet = true) : packet.sourceSyntax = rawSources := by
  have authentic := (authenticate_iff rawSources packet).mp accepted
  cases elaborated : decodeSource? rawSources with
  | none => simp [Authentic, elaborated] at authentic
  | some program => exact (show _ ∧ _ by simpa [Authentic, elaborated] using authentic).1

/-- Every exported occurrence retains the established OSLF completion type.
This theorem does not assert whole-program clause uniqueness or native bounds. -/
theorem inferred_info_echo {sources : List Source} {info : BinaryTypeInfo}
    (member : info ∈ inferredInfos sources) :
    ∃ names, inputNamesAt? sources info.occurrence = some names ∧
      ∀ (env : Env) (left right : Int),
        lookup? env names.1 = some left → lookup? env names.2 = some right →
        satisfiesNative (echoNativeType (binaryQuery info.relation left right))
          (.request (sources, env) ⟨info.occurrence, binaryCall info.relation left right⟩) := by
  obtain ⟨judgment, _, equal⟩ := List.mem_map.mp member
  subst info
  exact ⟨judgment.names, judgment.names_at, judgment.echo_type⟩

/-- The same source evidence determines which of the two possible completions
occurs. Cardinality alone is not a substitute for guard truth or polarity. -/
theorem inferred_info_exact_execution {sources : List Source} {info : BinaryTypeInfo}
    (member : info ∈ inferredInfos sources) :
    ∃ names, inputNamesAt? sources info.occurrence = some names ∧
      ∀ (env : Env) (left right : Int),
        lookup? env names.1 = some left → lookup? env names.2 = some right →
        runAt? (sources, env) ⟨info.occurrence, binaryCall info.relation left right⟩ =
          some (binaryAnswers info.relation info.notLess info.successor left right) := by
  obtain ⟨judgment, _, equal⟩ := List.mem_map.mp member
  subst info
  exact ⟨judgment.names, judgment.names_at, judgment.run sources⟩

theorem authenticated_types_exact {rawSources : List SExpr} {packet : Packet}
    {program : List Source} (elaborated : decodeSource? rawSources = some program)
    (accepted : authenticate rawSources packet = true) : packet.types = inferredInfos program := by
  have authentic := (authenticate_iff rawSources packet).mp accepted
  exact (show _ ∧ _ by simpa [Authentic, elaborated] using authentic).2

theorem authenticated_info_echo {rawSources : List SExpr} {packet : Packet}
    {sources : List Source} {info : BinaryTypeInfo}
    (elaborated : decodeSource? rawSources = some sources)
    (accepted : authenticate rawSources packet = true) (member : info ∈ packet.types) :
    ∃ names, inputNamesAt? sources info.occurrence = some names ∧
      ∀ (env : Env) (left right : Int),
        lookup? env names.1 = some left → lookup? env names.2 = some right →
        satisfiesNative (echoNativeType (binaryQuery info.relation left right))
          (.request (sources, env) ⟨info.occurrence, binaryCall info.relation left right⟩) := by
  rw [authenticated_types_exact elaborated accepted] at member
  exact inferred_info_echo member

theorem authenticated_info_exact_execution {rawSources : List SExpr} {packet : Packet}
    {sources : List Source} {info : BinaryTypeInfo}
    (decoded : decodeSource? rawSources = some sources)
    (accepted : authenticate rawSources packet = true) (member : info ∈ packet.types) :
    ∃ names, inputNamesAt? sources info.occurrence = some names ∧
      ∀ (env : Env) (left right : Int),
        lookup? env names.1 = some left → lookup? env names.2 = some right →
        runAt? (sources, env) ⟨info.occurrence, binaryCall info.relation left right⟩ =
          some (binaryAnswers info.relation info.notLess info.successor left right) := by
  rw [authenticated_types_exact decoded accepted] at member
  exact inferred_info_exact_execution member

theorem changed_source_rejected (expected : List SExpr) (packet : Packet)
    (different : packet.sourceSyntax ≠ expected) : authenticate expected packet = false := by
  cases accepted : authenticate expected packet with
  | false => rfl
  | true => exact False.elim (different (authenticated_source_exact accepted))

theorem changed_types_rejected {rawSources : List SExpr} {packet : Packet}
    {program : List Source} (elaborated : decodeSource? rawSources = some program)
    (different : packet.types ≠ inferredInfos program) : authenticate rawSources packet = false := by
  cases accepted : authenticate rawSources packet with
  | false => rfl
  | true => exact False.elim (different (authenticated_types_exact elaborated accepted))

example : encodePacket ⟨[.atom "1"], []⟩ ≠ encodePacket ⟨[.atom "1.0"], []⟩ := by
  simp [encodePacket]

example : decodePacket (encodePacket ⟨[],
    [⟨4, "same", false, false⟩, ⟨5, "same", false, false⟩]⟩) =
    some ⟨[], [⟨4, "same", false, false⟩, ⟨5, "same", false, false⟩]⟩ :=
  decodePacket_encode _

#print axioms authenticated_info_echo
#print axioms authenticated_info_exact_execution
#print axioms decodedSource_equations_empty

end Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeCodec
