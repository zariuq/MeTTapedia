import Mettapedia.GSLT.Parsing.PlainBnfScalarOperandTransport
import Mettapedia.GSLT.Parsing.GeneratedPeTTaNativeTypeBinding
import Mettapedia.GSLT.Parsing.GeneratedPeTTaSemidetLet
import Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarListExecution

/-!
# Connected selected Integer NativeType refinement

Authenticated source occurrence judgments supply the provider occurrence bound.
The actual two complementary scalar rules transport that bound to the
generated scalar worker, where the actual scalar-list result binder consumes
it. Source and target inventories remain the existing authenticated/proved
inventories; no provider returns a computed scalar diagnostic.

This is a selected finite generated-body result. Source authentication and
exact occurrence premises do not establish the C packet decoder, arbitrary
edited wire normalization, dynamic program extension, or native first-answer
execution adequacy. Mathematical Integer operands include negative values.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfSelectedNativeTypeRefinement

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Source)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open SourceIntegerProviderNativeType

/-- The selected source row determines polarity; the packet supplies its
position in a possibly larger, ordered source composition. -/
def selectedInfo (index : Fin 2) (occurrence : Nat) : BinaryTypeInfo :=
  ⟨occurrence,
    if index.val = 0 then "ground-integer-less" else "ground-integer-not-less",
    index.val != 0, false⟩

/-- Exact execution of the selected source occurrence is the actual provider
query observation. This uses the unique matching provider inventory already
proved for the authored provider source, not just the packet's row count. -/
theorem provider_occurrence_agreement (sources : List Source) (index : Fin 2)
    (occurrence : Nat)
    (selected : equationAt? sources occurrence = equationSides? (PlainBnfScalarOrderSource.providerRow index))
    (left right : Int) :
    runAt? (sources, PlainBnfScalarOrderSource.integerEnv left right)
      ⟨occurrence, binaryCall (selectedInfo index occurrence).relation left right⟩ =
    PlainBnfScalarOrderSource.providerAnswers? (binaryQuery (selectedInfo index occurrence).relation left right) := by
  have authentic : (selectedInfo index occurrence).Authentic sources ("?left", "?right") := by
    rw [PlainBnfScalarOrderSource.provider_sides] at selected
    fin_cases index <;>
      simpa [BinaryTypeInfo.Authentic, selectedInfo,
        SourceIntegerProvider.sourceVariableToken] using selected
  have ran := BinaryJudgment.run sources
    ⟨selectedInfo index occurrence, ("?left", "?right"), authentic⟩
    (PlainBnfScalarOrderSource.integerEnv left right) left right
    (by simp [PlainBnfScalarOrderSource.integerEnv])
    (by simp [PlainBnfScalarOrderSource.integerEnv, SourceIntegerProvider.lookup?])
  change runAt? (sources, PlainBnfScalarOrderSource.integerEnv left right)
    ⟨occurrence, binaryCall (selectedInfo index occurrence).relation left right⟩ =
      some (binaryAnswers (selectedInfo index occurrence).relation (index.val != 0) false left right)
    at ran
  rw [ran]
  fin_cases index
  · simpa [selectedInfo, binaryAnswers, binaryCondition, binaryQuery] using
      (PlainBnfScalarOrderSource.provider_less left right).symm
  · simpa [selectedInfo, binaryAnswers, binaryCondition, binaryQuery] using
      (PlainBnfScalarOrderSource.provider_not_less left right).symm

/-- Authentication is consumed as a completion predicate, then reflected
through actual source execution to a bound on the provider's full stream. -/
theorem authenticated_provider_occurrences
    {rawSources : List SExpr} {packet : IntegerProviderNativeTypeCodec.Packet} {sources : List Source}
    (decoded : IntegerProviderNativeTypeCodec.decodeSource? rawSources = some sources)
    (accepted : IntegerProviderNativeTypeCodec.authenticate rawSources packet = true)
    (index : Fin 2) (occurrence : Nat)
    (member : selectedInfo index occurrence ∈ packet.types)
    (selected : equationAt? sources occurrence = equationSides? (PlainBnfScalarOrderSource.providerRow index))
    (left right : Int) (answers : List SExpr)
    (completed : PlainBnfScalarOrderSource.providerAnswers?
      (binaryQuery (selectedInfo index occurrence).relation left right) = some answers) :
    answers.length ≤ 1 := by
  obtain ⟨names, namesAt, echo⟩ := IntegerProviderNativeTypeCodec.authenticated_info_echo decoded accepted member
  have actualNames : inputNamesAt? sources occurrence = some ("?left", "?right") := by
    rw [PlainBnfScalarOrderSource.provider_sides] at selected
    simp [inputNamesAt?, selected, binaryShape]
  have namesEq : names = ("?left", "?right") := by
    simpa only [selectedInfo, actualNames, Option.some.injEq] using namesAt.symm
  subst names
  have typed := echo (PlainBnfScalarOrderSource.integerEnv left right) left right
    (by simp [PlainBnfScalarOrderSource.integerEnv])
    (by simp [SourceIntegerProvider.lookup?, PlainBnfScalarOrderSource.integerEnv])
  have execution : source.Evaluates (sources, PlainBnfScalarOrderSource.integerEnv left right)
      ⟨occurrence, binaryCall (selectedInfo index occurrence).relation left right⟩
      (sources, PlainBnfScalarOrderSource.integerEnv left right) answers := by
    apply (source_iff_runAt _ _ _ _).mpr
    exact ⟨rfl, (provider_occurrence_agreement sources index occurrence selected left right).trans
      completed⟩
  exact (GeneratedPeTTaNativeTypeBinding.native_completion_binding _ _ _ typed).2
    _ _ execution |>.2.1

private theorem rule_length (index : Fin 2) (left right : Int) (origin : SExpr)
    (bound : ∀ answers, PlainBnfScalarOrderSource.providerAnswers?
      (binaryQuery (selectedInfo index 0).relation left right) = some answers →
        answers.length ≤ 1)
    (answers : List SExpr)
    (completed : PlainBnfScalarOrderSource.ruleAnswers? (PlainBnfScalarOrderSource.scalarRow index) left right origin = some answers) :
    answers.length ≤ 1 := by
  have shape : PlainBnfScalarOrderSource.ruleAnswers? (PlainBnfScalarOrderSource.scalarRow index) left right origin =
      (PlainBnfScalarOrderSource.providerAnswers? (binaryQuery (selectedInfo index 0).relation left right)).map
        (fun values => values.map (fun _ => if index.val = 0 then
          SExpr.atom "BNFDiagnosticsNilV1" else PlainBnfGeneratedScalarOrderExecution.diagnostic left right origin)) := by
    unfold PlainBnfScalarOrderSource.ruleAnswers?
    rw [PlainBnfScalarOrderSource.scalarRow_head, PlainBnfScalarOrderSource.scalarRow_body]
    fin_cases index <;>
      simp [SourceSExprPatternInstantiation.instantiate?,
        SourceSExprPatternInstantiation.instantiateList?, PlainBnfScalarOrderSource.sourceEnv,
        SourceIntegerProvider.sourceVariableToken, PlainBnfScalarOrderSource.relation, selectedInfo,
        binaryQuery, PlainBnfGeneratedScalarOrderExecution.diagnostic, Option.map_eq_bind]
  rw [shape] at completed
  obtain ⟨values, evaluated, rfl⟩ := Option.map_eq_some_iff.mp completed
  simpa using bound values evaluated

/-- Two individually semideterministic rules are not generally
semideterministic together. Here the actual guards are complementary, so only
one rule can contribute; its occurrence bound comes from the NativeType. -/
theorem authenticated_scalar_occurrences
    {rawSources : List SExpr} {packet : IntegerProviderNativeTypeCodec.Packet} {sources : List Source}
    (decoded : IntegerProviderNativeTypeCodec.decodeSource? rawSources = some sources)
    (accepted : IntegerProviderNativeTypeCodec.authenticate rawSources packet = true)
    (occurrences : Fin 2 → Nat)
    (member : ∀ index, selectedInfo index (occurrences index) ∈ packet.types)
    (selected : ∀ index, equationAt? sources (occurrences index) =
      equationSides? (PlainBnfScalarOrderSource.providerRow index))
    (left right : Int) (origin : SExpr) (answers : List SExpr)
    (completed : PlainBnfScalarOrderSource.sourceAnswers? left right origin = some answers) :
    answers.length ≤ 1 := by
  have bound (index : Fin 2) := rule_length index left right origin
    (fun values evaluated => authenticated_provider_occurrences decoded accepted index
      (occurrences index) (member index) (selected index) left right values evaluated)
  unfold PlainBnfScalarOrderSource.sourceAnswers? at completed
  rw [PlainBnfScalarOrderSource.scalarRows_exact] at completed
  by_cases increasing : left < right
  · have inactive : PlainBnfScalarOrderSource.ruleAnswers? (PlainBnfScalarOrderSource.scalarRow 1) left right origin = some [] := by
      rw [PlainBnfScalarOrderSource.second_rule_answers]
      simp [show ¬ right ≤ left by omega]
    simp only [List.mapM_cons, List.mapM_nil, inactive] at completed
    cases active : PlainBnfScalarOrderSource.ruleAnswers? (PlainBnfScalarOrderSource.scalarRow 0) left right origin with
    | none => simp [active] at completed
    | some values =>
        have same : values = answers := by simpa [active] using completed
        exact same ▸ bound 0 values active
  · have inactive : PlainBnfScalarOrderSource.ruleAnswers? (PlainBnfScalarOrderSource.scalarRow 0) left right origin = some [] := by
      rw [PlainBnfScalarOrderSource.first_rule_answers]
      simp [increasing]
    simp only [List.mapM_cons, List.mapM_nil, inactive] at completed
    cases active : PlainBnfScalarOrderSource.ruleAnswers? (PlainBnfScalarOrderSource.scalarRow 1) left right origin with
    | none => simp [active] at completed
    | some values =>
        have same : values = answers := by simpa [active] using completed
        exact same ▸ bound 1 values active

/-- The actual generated scalar execution transports the source-inferred
occurrence bound, including duplicate occurrences rather than value sets. -/
theorem authenticated_generated_occurrences
    {rawSources : List SExpr} {packet : IntegerProviderNativeTypeCodec.Packet} {sources : List Source}
    (decoded : IntegerProviderNativeTypeCodec.decodeSource? rawSources = some sources)
    (accepted : IntegerProviderNativeTypeCodec.authenticate rawSources packet = true)
    (occurrences : Fin 2 → Nat)
    (member : ∀ index, selectedInfo index (occurrences index) ∈ packet.types)
    (selected : ∀ index, equationAt? sources (occurrences index) =
      equationSides? (PlainBnfScalarOrderSource.providerRow index))
    (depth : Nat) (typed : Bool) (left right : Int) (origin : SExpr)
    (answers : List SExpr)
    (completed : GeneratedPeTTaGroundExecution.run (depth + 4) PlainBnfGeneratedScalarOrderSyntax.program PlainBnfGeneratedScalarOrderExecution.dataHeads
      (PlainBnfGeneratedScalarOrderExecution.call typed left right origin) = .complete answers) :
    answers.length ≤ 1 := by
  obtain ⟨sourceAnswers, executed, rfl⟩ :=
    (PlainBnfGeneratedScalarOrderExecution.completed_source_iff depth typed left right origin answers).mp completed
  simpa using authenticated_scalar_occurrences decoded accepted occurrences member selected
    left right origin sourceAnswers executed

open GeneratedPeTTaGroundExecution (eval run dataTemplates reserved)
open GeneratedPeTTaTemplateInstantiation (instantiate? instantiateList?)
open PlainBnfGeneratedScalarOrderSyntax (program callerSchema callerValue)
open PlainBnfGeneratedScalarOrderExecution (dataHeads call)

/-- The three operands are the very templates projected from the actual
scalar-list caller. Instantiating them does not re-evaluate opaque origin data. -/
theorem selected_callee_eval (depth : Nat) (env : Bindings) (typed : Bool)
    (left right : Int) (origin : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 1) program dataHeads env (PlainBnfScalarOperandTransport.generatedCallee typed) =
      run depth program dataHeads (call typed left right origin) := by
  rw [PlainBnfScalarOperandTransport.generated_callee_shape]
  have closed : instantiateList? env [.atom "$head", .atom "$next", .atom "$origin"] =
      some [.atom (toString left), .atom (toString right), origin] := by
    simp [GeneratedPeTTaTemplateInstantiation.instantiateList_cons, first, second, location]
  have data : dataTemplates dataHeads [.atom "$head", .atom "$next", .atom "$origin"] =
      true := rfl
  cases typed <;>
    simp [PlainBnfGeneratedScalarOrderSyntax.symbol, eval, reserved, data, closed, run, call]

/-- Connected selected control law. The authenticated provider NativeTypes
produce the scalar answer-occurrence bound consumed by the actual generated
literal-to-once let change. Both sides use the extracted caller schema/value,
the same caller environment and continuation, and aligned expression depth.
The whole Outcome is equal, including continuation exhaustion or refusal. -/
theorem authenticated_actual_caller_let
    {rawSources : List SExpr} {packet : IntegerProviderNativeTypeCodec.Packet}
    {sources : List Source}
    (decoded : IntegerProviderNativeTypeCodec.decodeSource? rawSources = some sources)
    (accepted : IntegerProviderNativeTypeCodec.authenticate rawSources packet = true)
    (occurrences : Fin 2 → Nat)
    (member : ∀ index, selectedInfo index (occurrences index) ∈ packet.types)
    (selected : ∀ index, equationAt? sources (occurrences index) =
      equationSides? (PlainBnfScalarOrderSource.providerRow index))
    (depth : Nat) (env : Bindings) (left right : Int) (origin continuation : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) := by
  have same : eval (depth + 5) program dataHeads env
      (PlainBnfScalarOperandTransport.generatedCallee false) =
    eval (depth + 5) program dataHeads env
      (PlainBnfScalarOperandTransport.generatedCallee true) := by
    rw [show depth + 5 = (depth + 4) + 1 by omega,
      selected_callee_eval _ _ _ _ _ _ first second location,
      selected_callee_eval _ _ _ _ _ _ first second location]
    exact (PlainBnfGeneratedScalarOrderExecution.raw_typed_same depth left right origin).symm
  have small (answers : List SExpr)
      (completed : eval (depth + 5) program dataHeads env
        (PlainBnfScalarOperandTransport.generatedCallee false) = .complete answers) :
      answers.length ≤ 1 := by
    rw [show depth + 5 = (depth + 4) + 1 by omega,
      selected_callee_eval _ _ _ _ _ _ first second location] at completed
    exact authenticated_generated_occurrences decoded accepted occurrences member selected
      depth false left right origin answers completed
  have result := GeneratedPeTTaSemidetLet.transported_literal_once_let (depth + 5)
    program dataHeads env
    [.atom PlainBnfGeneratedScalarOrderSyntax.tag, .atom "$orderDiagnostics"]
    (PlainBnfScalarOperandTransport.generatedCallee false)
    (PlainBnfScalarOperandTransport.generatedCallee true) continuation same small
  simpa only [PlainBnfGeneratedScalarOrderSyntax.caller_schema,
    PlainBnfGeneratedScalarOrderSyntax.raw_caller_value,
    PlainBnfGeneratedScalarOrderSyntax.typed_caller_value,
    PlainBnfScalarOperandTransport.generated_callee_shape,
    GeneratedPeTTaSemidetLet.literal, GeneratedPeTTaSemidetLet.once,
    show depth + 5 + 2 = depth + 7 by omega] using result

open GeneratedPeTTaIntegerProviderBridge (providerSource sourceSyntax)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT

/-- The concrete local source specimen is the actual six-row provider source,
not a hand-selected two-row replacement. Selected positions are its first two
rows; the four other rows remain in the authenticated source inventory. -/
theorem actual_provider_occurrence (index : Fin 2) :
    equationAt? [providerSource] index.val =
      equationSides? (PlainBnfScalarOrderSource.providerRow index) := by
  rw [← GeneratedPeTTaIntegerProviderBridge.sourceSides_from_admitted]
  fin_cases index <;> rfl

theorem actual_provider_authentic (index : Fin 2) :
    (selectedInfo index index.val).Authentic [providerSource] ("?left", "?right") := by
  have selected := actual_provider_occurrence index
  rw [PlainBnfScalarOrderSource.provider_sides] at selected
  fin_cases index <;>
    simpa [BinaryTypeInfo.Authentic, selectedInfo, SourceIntegerProvider.sourceVariableToken]
      using selected

/-- Inference is actually executed at the retrieved source occurrence. -/
theorem actual_provider_inferred (index : Fin 2) :
    inferBinaryTypeAt [providerSource] index.val =
      some ⟨selectedInfo index index.val, ("?left", "?right"), actual_provider_authentic index⟩ :=
  inferBinaryTypeAt_complete _ _ (actual_provider_authentic index)

theorem actual_source_composition_decoded :
    IntegerProviderNativeTypeCodec.decodeSource? [sourceSyntax] = some [providerSource] := by
  have one : "1".toNat? = some 1 := Nat.toNat?_repr 1
  have two : "2".toNat? = some 2 := Nat.toNat?_repr 2
  have three : "3".toNat? = some 3 := Nat.toNat?_repr 3
  have valid : compositionValid [providerSource] = true := by
    simp [providerSource, sourceSyntax, decode, decodeList, decodeOperator, decodeRewrite,
      atomToken?, one, two, three, compositionValid, Source.hasValidSchema,
      Source.termsValidIn, compositionOperators, compositionRewriteNames, rewriteName,
      Rewrite.hasValidShape, termSupported, termsSupported, hasOperator]
  have emptyEquations : providerSource.equations = [] := by
    simp [providerSource, sourceSyntax, decode, decodeList, decodeOperator, decodeRewrite,
      atomToken?, one, two, three]
  simp [IntegerProviderNativeTypeCodec.decodeSource?,
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decodeList,
    GeneratedPeTTaIntegerProviderBridge.providerSource_decoded, valid, emptyEquations]

/-- The packet is the output of the existing source inference. It is a Lean
structured specimen, not a claim about a physical C-produced packet. -/
def actualPacket : IntegerProviderNativeTypeCodec.Packet :=
  ⟨[sourceSyntax], IntegerProviderNativeTypeCodec.inferredInfos [providerSource]⟩

theorem actual_packet_inferred :
    IntegerProviderNativeTypeCodec.inferPacket? [sourceSyntax] = some actualPacket := by
  simp [IntegerProviderNativeTypeCodec.inferPacket?, actual_source_composition_decoded, actualPacket]

theorem actual_packet_authenticated :
    IntegerProviderNativeTypeCodec.authenticate [sourceSyntax] actualPacket = true :=
  (IntegerProviderNativeTypeCodec.authenticate_iff _ _).mpr
    (IntegerProviderNativeTypeCodec.inferred_packet_authentic actual_packet_inferred)

theorem actual_packet_member (index : Fin 2) :
    selectedInfo index index.val ∈ actualPacket.types := by
  exact List.mem_map.mpr
    ⟨⟨selectedInfo index index.val, ("?left", "?right"), actual_provider_authentic index⟩,
      BinaryJudgment.in_inferred _, rfl⟩

/-- Decoding the actual inferred packet preserves its selected source license;
that decoded license, rather than a bare roundtrip equality, drives the caller
refinement. This explicitly uses the existing structured NativeType codec. -/
theorem actual_packet_caller_let
    (packet : IntegerProviderNativeTypeCodec.Packet)
    (decodedPacket : IntegerProviderNativeTypeCodec.decodePacket
      (IntegerProviderNativeTypeCodec.encodePacket actualPacket) = some packet)
    (depth : Nat) (env : Bindings) (left right : Int) (origin continuation : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) := by
  have same : actualPacket = packet := by simpa using decodedPacket
  subst packet
  exact authenticated_actual_caller_let actual_source_composition_decoded
    actual_packet_authenticated Fin.val actual_packet_member actual_provider_occurrence
    depth env left right origin continuation first second location

/-- Structural input admission supplies the actual Integer operands before
semantic validation. Their original token spelling is retained in the
observation; the caller law applies to the canonical value image only.
`originWire` is a shared opaque observation, not an assumed physical codec. -/
theorem checked_pair_caller_let
    {input left right origin : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {declarationOccurrence scalarPosition : Nat}
    (checked : PlainBnfInputCarrier.Checked input "BnfGrammarInput")
    (pair : PlainBnfInputCarrier.InputScalarPair input
      declarationOccurrence scalarPosition left right origin)
    (originWire : SExpr) :
    ∃ leftToken rightToken leftValue rightValue,
      left = .apply leftToken [] ∧ right = .apply rightToken [] ∧
      leftToken.toInt? = some leftValue ∧ rightToken.toInt? = some rightValue ∧
      ∀ (depth : Nat) (env : Bindings) (continuation : SExpr),
        instantiate? env (.atom "$head") = some (.atom (toString leftValue)) →
        instantiate? env (.atom "$next") = some (.atom (toString rightValue)) →
        instantiate? env (.atom "$origin") = some originWire →
        eval (depth + 7) program dataHeads env
          (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
        eval (depth + 7) program dataHeads env
          (.list [.atom "let", callerSchema true, callerValue true, continuation]) := by
  obtain ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed⟩ :=
    PlainBnfInputCarrier.input_pair_integer_values checked pair
  exact ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed,
    fun depth env continuation first second location =>
      actual_packet_caller_let actualPacket
        (IntegerProviderNativeTypeCodec.decodePacket_encode _) depth env leftValue rightValue
        originWire continuation first second location⟩

/-- Signed native values use the existing canonical representation relation;
no sign is erased and no C printer or arithmetic implementation is assumed. -/
theorem signed_pair_caller_let (depth : Nat) (env : Bindings) (left right : Int64)
    (origin continuation : SExpr)
    (first : instantiate? env (.atom "$head") =
      some (PlainBnfScalarOperandTransport.signedValue left))
    (second : instantiate? env (.atom "$next") =
      some (PlainBnfScalarOperandTransport.signedValue right))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) program dataHeads env
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) :=
  actual_packet_caller_let actualPacket (IntegerProviderNativeTypeCodec.decodePacket_encode _)
    depth env left.toInt right.toInt origin continuation first second location

private theorem scalar_list_profile_extension :
    GeneratedPeTTaDataHeadExtension.Extends dataHeads
      PlainBnfGeneratedScalarListExecution.dataHeads := by
  intro head present
  simpa only [PlainBnfGeneratedScalarListExecution.dataHeads, List.contains_append,
    Bool.or_eq_true] using Or.inl (Or.inl (Or.inr present))

/-- The actual ScalarList constructor profile admits the actual result
binder; the following let equality is not two rejected binders. -/
theorem scalar_list_schema_inert (typed : Bool) :
    GeneratedPeTTaGroundExecution.inertBinder program
      PlainBnfGeneratedScalarListExecution.dataHeads (callerSchema typed) = true :=
  GeneratedPeTTaDataHeadExtension.inertBinder_mono scalar_list_profile_extension _ _
    (PlainBnfGeneratedScalarOrderExecution.actual_schema_inert typed)

/-- Execute the same actual caller callee under ScalarList's full existing
constructor profile. Completed execution is preserved by the established
data-head extension theorem, with no program or source-row changes. -/
theorem scalar_list_callee_agreement (depth : Nat) (env : Bindings) (typed : Bool)
    (left right : Int) (origin : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 5) program PlainBnfGeneratedScalarListExecution.dataHeads env
      (PlainBnfScalarOperandTransport.generatedCallee typed) =
    run (depth + 4) program dataHeads (call typed left right origin) := by
  have completed : eval (depth + 5) program dataHeads env
      (PlainBnfScalarOperandTransport.generatedCallee typed) =
      .complete [PlainBnfGeneratedScalarOrderExecution.answer left right origin] := by
    rw [show depth + 5 = (depth + 4) + 1 by omega,
      selected_callee_eval _ _ _ _ _ _ first second location,
      PlainBnfGeneratedScalarOrderExecution.run_exact]
  rw [PlainBnfGeneratedScalarOrderExecution.run_exact]
  exact GeneratedPeTTaDataHeadExtension.eval_completed scalar_list_profile_extension
    _ _ _ _ _ completed

/-- The connected NativeType law under the actual larger ScalarList profile.
It preserves the exact second-let schema/value projections, existing caller
bindings, and any continuation Outcome. No full-loop or native-runtime
adequacy premise is supplied implicitly by changing the constructor profile. -/
theorem authenticated_scalar_list_caller_let
    {rawSources : List SExpr} {packet : IntegerProviderNativeTypeCodec.Packet}
    {sources : List Source}
    (decoded : IntegerProviderNativeTypeCodec.decodeSource? rawSources = some sources)
    (accepted : IntegerProviderNativeTypeCodec.authenticate rawSources packet = true)
    (occurrences : Fin 2 → Nat)
    (member : ∀ index, selectedInfo index (occurrences index) ∈ packet.types)
    (selected : ∀ index, equationAt? sources (occurrences index) =
      equationSides? (PlainBnfScalarOrderSource.providerRow index))
    (depth : Nat) (env : Bindings) (left right : Int) (origin continuation : SExpr)
    (first : instantiate? env (.atom "$head") = some (.atom (toString left)))
    (second : instantiate? env (.atom "$next") = some (.atom (toString right)))
    (location : instantiate? env (.atom "$origin") = some origin) :
    eval (depth + 7) program PlainBnfGeneratedScalarListExecution.dataHeads env
      (.list [.atom "let", callerSchema false, callerValue false, continuation]) =
    eval (depth + 7) program PlainBnfGeneratedScalarListExecution.dataHeads env
      (.list [.atom "let", callerSchema true, callerValue true, continuation]) := by
  have same : eval (depth + 5) program PlainBnfGeneratedScalarListExecution.dataHeads env
      (PlainBnfScalarOperandTransport.generatedCallee false) =
    eval (depth + 5) program PlainBnfGeneratedScalarListExecution.dataHeads env
      (PlainBnfScalarOperandTransport.generatedCallee true) := by
    rw [scalar_list_callee_agreement _ _ _ _ _ _ first second location,
      scalar_list_callee_agreement _ _ _ _ _ _ first second location]
    exact (PlainBnfGeneratedScalarOrderExecution.raw_typed_same depth left right origin).symm
  have small (answers : List SExpr)
      (completed : eval (depth + 5) program PlainBnfGeneratedScalarListExecution.dataHeads env
        (PlainBnfScalarOperandTransport.generatedCallee false) = .complete answers) :
      answers.length ≤ 1 := by
    rw [scalar_list_callee_agreement _ _ _ _ _ _ first second location] at completed
    exact authenticated_generated_occurrences decoded accepted occurrences member selected
      depth false left right origin answers completed
  have result := GeneratedPeTTaSemidetLet.transported_literal_once_let (depth + 5)
    program PlainBnfGeneratedScalarListExecution.dataHeads env
    [.atom PlainBnfGeneratedScalarOrderSyntax.tag, .atom "$orderDiagnostics"]
    (PlainBnfScalarOperandTransport.generatedCallee false)
    (PlainBnfScalarOperandTransport.generatedCallee true) continuation same small
  simpa only [PlainBnfGeneratedScalarOrderSyntax.caller_schema,
    PlainBnfGeneratedScalarOrderSyntax.raw_caller_value,
    PlainBnfGeneratedScalarOrderSyntax.typed_caller_value,
    PlainBnfScalarOperandTransport.generated_callee_shape,
    GeneratedPeTTaSemidetLet.literal, GeneratedPeTTaSemidetLet.once,
    show depth + 5 + 2 = depth + 7 by omega] using result

/-- A real scalar-list cons environment after the first Unicode check. The
head diagnostic is empty because scalar zero is valid; the next scalar is one.
Existing input bindings and the first diagnostic remain in the caller frame. -/
def successfulCallerEnv : Bindings :=
  ("$headDiagnostics", SourceSExprPatternCodec.encode (.atom "BNFDiagnosticsNilV1")) ::
    PlainBnfGeneratedScalarListSyntax.consEnv 0 1
      (PlainBnfGeneratedScalarListSyntax.scalars []) (.atom "origin")

private theorem successful_operand_head : instantiate? successfulCallerEnv (.atom "$head") =
    some (.atom (toString (0 : Int))) := by
  simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, successfulCallerEnv,
    PlainBnfGeneratedScalarListSyntax.consEnv, GeneratedPeTTaResultBinding.variableToken]

private theorem successful_operand_next : instantiate? successfulCallerEnv (.atom "$next") =
    some (.atom (toString (1 : Int))) := by
  simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, successfulCallerEnv,
    PlainBnfGeneratedScalarListSyntax.consEnv, GeneratedPeTTaResultBinding.variableToken]

private theorem successful_operand_origin : instantiate? successfulCallerEnv (.atom "$origin") =
    some (.atom "origin") := by
  simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, successfulCallerEnv,
    PlainBnfGeneratedScalarListSyntax.consEnv, GeneratedPeTTaResultBinding.variableToken]

/-- Non-vacuity at the real caller: both actual control fragments return one
constant answer, not two outside-fragment outcomes or an empty stream. -/
theorem successful_continuation_control :
    eval 7 program PlainBnfGeneratedScalarListExecution.dataHeads successfulCallerEnv
      (.list [.atom "let", callerSchema false, callerValue false,
        .list [.atom "quote", .atom "42"]]) = .complete [.atom "42"] ∧
    eval 7 program PlainBnfGeneratedScalarListExecution.dataHeads successfulCallerEnv
      (.list [.atom "let", callerSchema true, callerValue true,
        .list [.atom "quote", .atom "42"]]) = .complete [.atom "42"] := by
  have same := authenticated_scalar_list_caller_let actual_source_composition_decoded
    actual_packet_authenticated Fin.val actual_packet_member actual_provider_occurrence
    0 successfulCallerEnv 0 1 (.atom "origin") (.list [.atom "quote", .atom "42"])
    successful_operand_head successful_operand_next successful_operand_origin
  have inner : eval 5 program PlainBnfGeneratedScalarListExecution.dataHeads successfulCallerEnv
      (PlainBnfScalarOperandTransport.generatedCallee true) =
      .complete [PlainBnfGeneratedScalarOrderExecution.result (.atom "BNFDiagnosticsNilV1")] := by
    rw [show 5 = 0 + 5 from rfl, scalar_list_callee_agreement _ _ _ _ _ _
      successful_operand_head successful_operand_next successful_operand_origin,
      PlainBnfGeneratedScalarOrderExecution.run_exact]
    rfl
  have wrapped := GeneratedPeTTaGroundExecution.once_complete 5 program
    PlainBnfGeneratedScalarListExecution.dataHeads successfulCallerEnv _ _ (by simp) inner
  have actualWrapped : eval 6 program PlainBnfGeneratedScalarListExecution.dataHeads
      successfulCallerEnv (callerValue true) =
      .complete [PlainBnfGeneratedScalarOrderExecution.result (.atom "BNFDiagnosticsNilV1")] := by
    simpa [PlainBnfGeneratedScalarOrderSyntax.typed_caller_value,
      PlainBnfScalarOperandTransport.generated_callee_shape] using wrapped
  have finished : eval 7 program PlainBnfGeneratedScalarListExecution.dataHeads successfulCallerEnv
      (.list [.atom "let", callerSchema true, callerValue true,
        .list [.atom "quote", .atom "42"]]) = .complete [.atom "42"] := by
    rw [GeneratedPeTTaGroundExecution.let_complete 6 _ _ _ _ _ _ _
      (scalar_list_schema_inert true) actualWrapped]
    simp [GeneratedPeTTaResultBinding.bindAnswers, GeneratedPeTTaResultBinding.bindResult,
      PlainBnfGeneratedScalarOrderSyntax.caller_schema,
      PlainBnfGeneratedScalarOrderExecution.result, PlainBnfGeneratedScalarOrderSyntax.tag,
      GeneratedPeTTaResultBinding.template, GeneratedPeTTaResultBinding.templates,
      GeneratedPeTTaResultBinding.variableToken, SourceSExprPatternCodec.encode,
      SourceSExprPatternCodec.encodeList, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
      List.foldlM, successfulCallerEnv, PlainBnfGeneratedScalarListSyntax.consEnv,
      eval,
      GeneratedPeTTaTemplateInstantiation.instantiate_atom]
  exact ⟨same.trans finished, finished⟩

/-- A mutated comparison polarity is not authenticated by the selected row,
although it still denotes an abstract zero-or-one relation on Integers. -/
theorem wrong_polarity_not_authentic :
    ¬ ({ selectedInfo 0 0 with notLess := true } : BinaryTypeInfo).Authentic
      [providerSource] ("?left", "?right") := by
  have selected := actual_provider_occurrence 0
  rw [PlainBnfScalarOrderSource.provider_sides] at selected
  change equationAt? [providerSource] 0 =
    some (binaryShape "ground-integer-less" ("?left", "?right") false false) at selected
  simp [BinaryTypeInfo.Authentic, selected, selectedInfo, binaryShape,
    SourceIntegerProvider.sourceVariableToken]

/-- Duplicating a successful source rule duplicates occurrences. The
authenticated provider license alone cannot license an enlarged scalar family. -/
theorem duplicate_scalar_rule_not_licensed (origin : SExpr) :
    (do let answers ← [PlainBnfScalarOrderSource.scalarRow 0,
          PlainBnfScalarOrderSource.scalarRow 0].mapM
          (fun row => PlainBnfScalarOrderSource.ruleAnswers? row (-2) (-1) origin)
        pure answers.flatten : Option (List SExpr)) =
      some [.atom "BNFDiagnosticsNilV1", .atom "BNFDiagnosticsNilV1"] :=
  PlainBnfScalarOrderSource.repeated_rule_not_semidet (-2) (-1) origin (by decide)

#print axioms authenticated_provider_occurrences
#print axioms authenticated_scalar_occurrences
#print axioms authenticated_generated_occurrences
#print axioms authenticated_actual_caller_let
#print axioms actual_provider_inferred
#print axioms actual_source_composition_decoded
#print axioms actual_packet_caller_let
#print axioms checked_pair_caller_let
#print axioms signed_pair_caller_let
#print axioms scalar_list_schema_inert
#print axioms authenticated_scalar_list_caller_let
#print axioms successful_continuation_control
#print axioms wrong_polarity_not_authentic
#print axioms duplicate_scalar_rule_not_licensed

end Mettapedia.GSLT.Parsing.PlainBnfSelectedNativeTypeRefinement
