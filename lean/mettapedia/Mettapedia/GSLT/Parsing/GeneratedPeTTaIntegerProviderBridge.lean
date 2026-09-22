import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundCondition

/-!
# Actual integer-provider condition and quotation bridge

The existing source reader supplies the authored provider presentation. The
whole independently generated PeTTa artifact supplies target equations. Their
actual conditions and echo payloads agree for mathematical Integer inputs.
Target lazy-if/quote/empty execution remains a separate consumer of these
facts; this module adds no body evaluator.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderBridge

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open SourceSExprPatternCodec (encode)
open GeneratedPeTTaTemplateInstantiation (instantiate?)
open GeneratedPeTTaGroundCondition (integer? condition?)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def sourceSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/experiments/gslt2parse_foundation/presentations/shared/cetta_petta_ground_integer_relations_v1.metta"

private theorem source_admitted : (decode sourceSyntax).isSome = true := by
  have one : "1".toNat? = some 1 := Nat.toNat?_repr 1
  have two : "2".toNat? = some 2 := Nat.toNat?_repr 2
  have three : "3".toNat? = some 3 := Nat.toNat?_repr 3
  simp [sourceSyntax, decode, decodeList, decodeOperator, decodeRewrite, atomToken?, one, two, three]

/-- Returned by the actual successful canonical decoder, with no fallback. -/
def providerSource : Source := (decode sourceSyntax).get source_admitted

theorem providerSource_decoded : decode sourceSyntax = some providerSource :=
  (Option.some_get source_admitted).symm

def sourceSides? (occurrence : Nat) : Option (SExpr × SExpr) :=
  (rawRewriteAt? sourceSyntax occurrence).bind SourceIntegerProviderNativeType.equationSides?

theorem sourceSides_from_admitted (occurrence : Nat) :
    sourceSides? occurrence =
      SourceIntegerProviderNativeType.equationAt? [providerSource] occurrence := by
  simp only [SourceIntegerProviderNativeType.equationAt?, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [rawRewriteAt?_of_decode providerSource_decoded occurrence]
  rfl

def emittedSource? (occurrence : Nat) : Option SExpr := do
  let (left, right) ← sourceSides? occurrence
  let head ← PlainBnfGeneratedPeTTaSyntax.sourceTerm? left
  let body ← PlainBnfGeneratedPeTTaSyntax.sourceTerm? right
  return .list [.atom "=", head, body]

def isIntegerProvider : SExpr → Bool
  | .list [.atom "=", .list (.atom head :: _), _] =>
      head.toList.take 20 == "gslt:ground-integer-".toList
  | _ => false

def generatedProviders : List SExpr :=
  (PlainBnfGeneratedPeTTaSyntax.generatedProgram.filter
    (fun row => isIntegerProvider row.2)).map Prod.snd

theorem generatedProviders_count : generatedProviders.length = 4 := by rfl

/-- Every actual generated integer-provider occurrence is compared against
the full template rendering of its independently read source equation. -/
theorem generatedProviders_from_source :
    (List.range 4).map emittedSource? = generatedProviders.map some := by rfl

def targetSides? (occurrence : Nat) : Option (SExpr × SExpr) := do
  let .list [.atom "=", left, right] ← generatedProviders[occurrence]? | none
  return (left, right)

def conditionOf? : SExpr → Option SExpr
  | .list [.atom "if", guard, _, _] => some guard
  | _ => none

def payloadOf? : SExpr → Option SExpr
  | .list [.atom "if", _, .list [.atom "quote", payload], _] => some payload
  | _ => none

def sourceCondition? (occurrence : Nat) : Option SExpr :=
  (sourceSides? occurrence).bind (fun sides => conditionOf? sides.2)

def targetCondition? (occurrence : Nat) : Option SExpr :=
  (targetSides? occurrence).bind (fun sides => conditionOf? sides.2)

def sourcePayload? (occurrence : Nat) : Option SExpr :=
  (sourceSides? occurrence).bind (fun sides => payloadOf? sides.2)

def targetPayload? (occurrence : Nat) : Option SExpr :=
  (targetSides? occurrence).bind (fun sides => payloadOf? sides.2)

def sourceEnv (left right : Int) : SourceIntegerProvider.Env :=
  [("?left", left), ("?right", right)]

def targetEnv (left right : Int) : Bindings :=
  [("$left", encode (.atom (toString left))), ("$right", encode (.atom (toString right)))]

theorem target_left (left right : Int) :
    instantiate? (targetEnv left right) (.atom "$left") = some (.atom (toString left)) := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable
  · simp [GeneratedPeTTaResultBinding.variableToken]
  · simp [targetEnv]

theorem target_right (left right : Int) :
    instantiate? (targetEnv left right) (.atom "$right") = some (.atom (toString right)) := by
  apply GeneratedPeTTaTemplateInstantiation.instantiate_variable
  · simp [GeneratedPeTTaResultBinding.variableToken]
  · simp [targetEnv]

theorem integer_left (left right : Int) : integer? (targetEnv left right) (.atom "$left") = some left :=
  GeneratedPeTTaGroundCondition.integer?_complete (.atom (target_left left right))

theorem integer_right (left right : Int) : integer? (targetEnv left right) (.atom "$right") = some right :=
  GeneratedPeTTaGroundCondition.integer?_complete (.atom (target_right left right))

theorem integer_one (env : Bindings) : integer? env (.atom "1") = some 1 := by
  have closed : instantiate? env (.atom "1") = some (.atom "1") := by
    simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, GeneratedPeTTaResultBinding.variableToken]
  simp [integer?, closed, SourceIntegerProvider.integerValue?_one]

private theorem integer_add (env : Bindings) (left right : SExpr) :
    integer? env (.list [.atom "+", left, right]) =
      (do return (← integer? env left) + (← integer? env right)) := by
  rw [integer?]

theorem actual_conditions_agree (occurrence : Fin 4) (left right : Int) :
    (targetCondition? occurrence).bind (condition? (targetEnv left right)) =
      (sourceCondition? occurrence).bind
        (SourceIntegerProvider.evalBoolean? (sourceEnv left right)) := by
  fin_cases occurrence
  · change condition? (targetEnv left right) (.list [.atom "<", .atom "$left", .atom "$right"]) =
      SourceIntegerProvider.evalBoolean? (sourceEnv left right)
        (.list [.atom "<", .atom "?left", .atom "?right"])
    simp [condition?, integer_left, integer_right,
      SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv]
  · change condition? (targetEnv left right) (.list [.atom ">=", .atom "$left", .atom "$right"]) =
      SourceIntegerProvider.evalBoolean? (sourceEnv left right)
        (.list [.atom ">=", .atom "?left", .atom "?right"])
    simp [condition?, integer_left, integer_right,
      SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv]
  · change condition? (targetEnv left right)
        (.list [.atom "<", .list [.atom "+", .atom "$left", .atom "1"], .atom "$right"]) =
      SourceIntegerProvider.evalBoolean? (sourceEnv left right)
        (.list [.atom "<", .list [.atom "+", .atom "?left", .atom "1"], .atom "?right"])
    simp [condition?, integer_add, integer_left, integer_right, integer_one,
      SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv,
      SourceIntegerProvider.integerValue?_one]
  · change condition? (targetEnv left right)
        (.list [.atom ">=", .list [.atom "+", .atom "$left", .atom "1"], .atom "$right"]) =
      SourceIntegerProvider.evalBoolean? (sourceEnv left right)
        (.list [.atom ">=", .list [.atom "+", .atom "?left", .atom "1"], .atom "?right"])
    simp [condition?, integer_add, integer_left, integer_right, integer_one,
      SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv,
      SourceIntegerProvider.integerValue?_one]

private theorem echo_agrees (relation : String) (left right : Int)
    (sourceOrdinary : SourceIntegerProvider.sourceVariableToken relation = false)
    (targetOrdinary : GeneratedPeTTaResultBinding.variableToken relation = false) :
    instantiate? (targetEnv left right)
        (.list [.atom relation, .atom "$left", .atom "$right"]) =
      SourceIntegerProvider.closeTerm? (sourceEnv left right)
        (.list [.atom relation, .atom "?left", .atom "?right"]) := by
  have targetHead : instantiate? (targetEnv left right) (.atom relation) = some (.atom relation) := by
    simp [GeneratedPeTTaTemplateInstantiation.instantiate_atom, targetOrdinary]
  have sourceLeft : SourceIntegerProvider.closeTerm? (sourceEnv left right) (.atom "?left") =
      some (.atom (toString left)) := by
    simp [SourceIntegerProvider.closeTerm?, SourceIntegerProvider.sourceVariableToken,
      SourceIntegerProvider.lookup?, sourceEnv]
  have sourceRight : SourceIntegerProvider.closeTerm? (sourceEnv left right) (.atom "?right") =
      some (.atom (toString right)) := by
    simp [SourceIntegerProvider.closeTerm?, SourceIntegerProvider.sourceVariableToken,
      SourceIntegerProvider.lookup?, sourceEnv]
  have sourceHead := SourceIntegerProvider.closeTerm?_atom (sourceEnv left right) relation sourceOrdinary
  have sourceClosed : SourceIntegerProvider.closeTerm? (sourceEnv left right)
      (.list [.atom relation, .atom "?left", .atom "?right"]) =
        some (.list [.atom relation, .atom (toString left), .atom (toString right)]) := by
    rw [SourceIntegerProvider.closeTerm?]
    simp only [SourceIntegerProvider.closeTerms?, sourceHead, sourceLeft, sourceRight]
    rfl
  rw [sourceClosed]
  simp only [GeneratedPeTTaTemplateInstantiation.instantiate_list,
    GeneratedPeTTaTemplateInstantiation.instantiateList_cons,
    GeneratedPeTTaTemplateInstantiation.instantiateList_nil,
    targetHead, target_left, target_right]
  rfl

/-- Quotation instantiates the actual echo templates without evaluating the
closed result as code. Both sides retain the exact relation and integer data. -/
theorem actual_echoes_agree (occurrence : Fin 4) (left right : Int) :
    (targetPayload? occurrence).bind (instantiate? (targetEnv left right)) =
      (sourcePayload? occurrence).bind
        (SourceIntegerProvider.closeTerm? (sourceEnv left right)) := by
  fin_cases occurrence
  all_goals
    change instantiate? (targetEnv left right) (.list [.atom _, .atom "$left", .atom "$right"]) =
      SourceIntegerProvider.closeTerm? (sourceEnv left right)
        (.list [.atom _, .atom "?left", .atom "?right"])
    apply echo_agrees <;>
      simp [SourceIntegerProvider.sourceVariableToken, GeneratedPeTTaResultBinding.variableToken]

def falseBranchOf? : SExpr → Option SExpr
  | .list [.atom "if", _, _, otherwise] => some otherwise
  | _ => none

/-- The nullary encoding changes at source rendering, not by identifying an
atom named `empty` with an application of that name. -/
theorem actual_false_branches (occurrence : Fin 4) :
    (targetSides? occurrence).bind (fun sides => falseBranchOf? sides.2) =
        some (.list [.atom "empty"]) ∧
      (sourceSides? occurrence).bind (fun sides => falseBranchOf? sides.2) =
        some (.list [.atom "metta-nullary", .atom "empty"]) := by
  fin_cases occurrence <;> constructor <;> rfl

theorem actual_source_conditions_total (occurrence : Fin 4) (left right : Int) :
    ((sourceCondition? occurrence).bind
      (SourceIntegerProvider.evalBoolean? (sourceEnv left right))).isSome = true := by
  fin_cases occurrence
  · change (SourceIntegerProvider.evalBoolean? (sourceEnv left right)
      (.list [.atom "<", .atom "?left", .atom "?right"])).isSome = true
    simp [SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv]
  · change (SourceIntegerProvider.evalBoolean? (sourceEnv left right)
      (.list [.atom ">=", .atom "?left", .atom "?right"])).isSome = true
    simp [SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv]
  · change (SourceIntegerProvider.evalBoolean? (sourceEnv left right)
      (.list [.atom "<", .list [.atom "+", .atom "?left", .atom "1"], .atom "?right"])).isSome = true
    simp [SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv]
  · change (SourceIntegerProvider.evalBoolean? (sourceEnv left right)
      (.list [.atom ">=", .list [.atom "+", .atom "?left", .atom "1"], .atom "?right"])).isSome = true
    simp [SourceIntegerProvider.evalBoolean?, SourceIntegerProvider.evalInteger?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv]

theorem actual_target_conditions_total (occurrence : Fin 4) (left right : Int) :
    ((targetCondition? occurrence).bind (condition? (targetEnv left right))).isSome = true := by
  rw [actual_conditions_agree]
  exact actual_source_conditions_total occurrence left right

theorem actual_source_echoes_total (occurrence : Fin 4) (left right : Int) :
    ((sourcePayload? occurrence).bind
      (SourceIntegerProvider.closeTerm? (sourceEnv left right))).isSome = true := by
  fin_cases occurrence
  all_goals
    change (SourceIntegerProvider.closeTerm? (sourceEnv left right)
      (.list [.atom _, .atom "?left", .atom "?right"])).isSome = true
    simp [SourceIntegerProvider.closeTerm?, SourceIntegerProvider.closeTerms?,
      SourceIntegerProvider.lookup?, SourceIntegerProvider.sourceVariableToken, sourceEnv]

theorem actual_target_echoes_total (occurrence : Fin 4) (left right : Int) :
    ((targetPayload? occurrence).bind (instantiate? (targetEnv left right))).isSome = true := by
  rw [actual_echoes_agree]
  exact actual_source_echoes_total occurrence left right

/-- Syntactic witnesses for the existing lazy-if/quote/empty consumer. No
arbitrary branch is admitted by the condition and payload projections alone. -/
theorem actual_body_shapes (occurrence : Fin 4) :
    ∃ sourceHead targetHead sourceGuard targetGuard sourceEcho targetEcho,
      sourceSides? occurrence = some (sourceHead,
        .list [.atom "if", sourceGuard, .list [.atom "quote", sourceEcho],
          .list [.atom "metta-nullary", .atom "empty"]]) ∧
      targetSides? occurrence = some (targetHead,
        .list [.atom "if", targetGuard, .list [.atom "quote", targetEcho],
          .list [.atom "empty"]]) := by
  fin_cases occurrence <;> exact ⟨_, _, _, _, _, _, rfl, rfl⟩

/-! ## Executable domain and quotation controls -/

/-- An expression-shaped value supplied through a variable is data, not an
arithmetic program to revisit. This holds for every list-shaped payload. -/
theorem variable_list_is_not_arithmetic (env : Bindings) (token : String) (terms : List SExpr)
    (named : GeneratedPeTTaResultBinding.variableToken token = true) :
    integer? ((token, encode (.list terms)) :: env) (.atom token) = none := by
  rw [integer?, GeneratedPeTTaTemplateInstantiation.bound_value_is_inert env token (.list terms) named]
  rfl

theorem mathematical_successor (left right : Int) :
    integer? (targetEnv left right) (.list [.atom "+", .atom "$left", .atom "1"]) =
      some (left + 1) := by
  simp [integer_add, integer_left, integer_one]

theorem float_is_not_integer : integer? [] (.atom "1.0") = none := by
  have notNat : "1.0".isNat = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have character := (String.isNat_iff.mp accepted).2.1 '.' (by decide)
    simp [Char.isDigit] at character
  have notInt : "1.0".toInt? = none := by
    rw [String.toInt?_eq_toNat?_of_startsWith_eq_false (by decide), String.toNat?_eq_none notNat]
    rfl
  simp [integer?, GeneratedPeTTaTemplateInstantiation.instantiate_atom,
    GeneratedPeTTaResultBinding.variableToken, SourceIntegerProvider.integerValue?, notInt]

theorem missing_operand_is_not_failure :
    condition? [] (.list [.atom "<", .atom "$missing", .atom "1"]) = none := by
  simp [condition?, integer?, GeneratedPeTTaTemplateInstantiation.instantiate_atom,
    GeneratedPeTTaResultBinding.variableToken]

theorem bare_boolean_is_outside_fragment (env : Bindings) :
    condition? env (.atom "True") = none := rfl

theorem unquoted_equality_is_outside_fragment (env : Bindings) (left right : String) :
    condition? env (.list [.atom "==", .atom left, .atom right]) = none := rfl

theorem quoted_equality_is_reflexive (env : Bindings) (schema value : SExpr)
    (closed : instantiate? env schema = some value) :
    condition? env (.list [.atom "==", .list [.atom "quote", schema],
      .list [.atom "quote", schema]]) = some true := by
  simp [condition?, closed]

theorem quoted_atom_differs_from_nullary_call (env : Bindings) :
    condition? env (.list [.atom "==", .list [.atom "quote", .atom "empty"],
      .list [.atom "quote", .list [.atom "empty"]]]) = some false := by
  simp [condition?, GeneratedPeTTaTemplateInstantiation.instantiateList_cons,
    GeneratedPeTTaTemplateInstantiation.instantiate_atom, GeneratedPeTTaResultBinding.variableToken]

example : condition? (targetEnv (-3) (-2))
    (.list [.atom "<", .atom "$left", .atom "$right"]) = some true := by
  simp [condition?, integer_left, integer_right]

example (left : Int) : condition? (targetEnv left (left + 1))
    (.list [.atom "<", .list [.atom "+", .atom "$left", .atom "1"], .atom "$right"]) =
      some false := by
  simp [condition?, mathematical_successor, integer_right]

#print axioms GeneratedPeTTaGroundCondition.integer?_iff
#print axioms GeneratedPeTTaGroundCondition.condition?_iff
#print axioms generatedProviders_from_source
#print axioms actual_conditions_agree
#print axioms actual_echoes_agree
#print axioms actual_body_shapes
#print axioms actual_target_conditions_total
#print axioms actual_target_echoes_total
#print axioms variable_list_is_not_arithmetic

end Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderBridge
