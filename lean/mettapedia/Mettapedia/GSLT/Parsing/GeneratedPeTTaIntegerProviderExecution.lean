import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution
import Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderBridge
import Mettapedia.GSLT.Parsing.GeneratedPeTTaNativeTypeBinding

/-!
# Executing the four actual generated Integer provider bodies

The existing source and target projections retrieve the actual equations.
Their condition and quotation bridges feed the target lazy-if execution;
the resulting complete answer lists agree with independent source evaluation.
This is body execution at the declared Integer environment, not whole-program
dispatch, fixed-width C arithmetic or an installed-runtime adequacy theorem.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open GeneratedPeTTaGroundExecution
open GeneratedPeTTaIntegerProviderBridge
open PlainBnfGeneratedPeTTaSyntax (generatedProgram)

/-- All mathematical Integer operands and all four actual generated bodies;
the exact empty/singleton stream is compared, not just successful values. -/
theorem actual_body_execution (depth : Nat) (occurrence : Fin 4) (left right : Int) :
    (targetSides? occurrence).map (fun sides =>
      eval (depth + 2) generatedProgram [] (targetEnv left right) sides.2) =
      ((sourceSides? occurrence).bind (fun sides =>
        SourceIntegerProvider.evalAnswers? (sourceEnv left right) sides.2)).map Outcome.complete := by
  obtain ⟨sourceHead, targetHead, sourceGuard, targetGuard, sourceEcho, targetEcho,
      sourceShape, targetShape⟩ := actual_body_shapes occurrence
  have conditions := actual_conditions_agree occurrence left right
  have echoes := actual_echoes_agree occurrence left right
  have conditionsTotal := actual_source_conditions_total occurrence left right
  have echoesTotal := actual_source_echoes_total occurrence left right
  simp only [sourceCondition?, targetCondition?, sourceShape, targetShape,
    Option.bind_some, conditionOf?] at conditions conditionsTotal
  simp only [sourcePayload?, targetPayload?, sourceShape, targetShape,
    Option.bind_some, payloadOf?] at echoes echoesTotal
  obtain ⟨truth, sourceCondition⟩ := Option.isSome_iff_exists.mp conditionsTotal
  obtain ⟨value, sourceClosed⟩ := Option.isSome_iff_exists.mp echoesTotal
  have targetCondition := conditions.trans sourceCondition
  have targetClosed := echoes.trans sourceClosed
  rw [targetShape, sourceShape]
  simp only [Option.map_some, Option.bind_some]
  rw [conditional_quote_empty depth generatedProgram [] (targetEnv left right)
    targetGuard targetEcho value truth targetCondition targetClosed]
  cases truth <;>
    simp [SourceIntegerProvider.evalAnswers?, sourceCondition, sourceClosed]

/-- A completed target body reflects to the independent source expression
judgment for the retrieved source body. -/
theorem completed_body_iff (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (answers : List SExpr) :
    (targetSides? occurrence).map (fun sides =>
      eval (depth + 2) generatedProgram [] (targetEnv left right) sides.2) =
        some (.complete answers) ↔
      ∃ head body, sourceSides? occurrence = some (head, body) ∧
        SourceIntegerProvider.AnswersEval (sourceEnv left right) body answers := by
  rw [actual_body_execution]
  simp only [Option.map_eq_some_iff, Outcome.complete.injEq]
  constructor
  · rintro ⟨values, evaluated, rfl⟩
    obtain ⟨⟨head, body⟩, selected, ran⟩ := Option.bind_eq_some_iff.mp evaluated
    exact ⟨head, body, selected, SourceIntegerProvider.evalAnswers?_sound _ _ _ ran⟩
  · rintro ⟨head, body, selected, evaluated⟩
    exact ⟨answers, by simp [selected, SourceIntegerProvider.evalAnswers?_complete evaluated], rfl⟩

/-- Occurrence cardinality, rather than cardinality of the set of values. -/
theorem completed_body_at_most_one (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (answers : List SExpr)
    (completed : (targetSides? occurrence).map (fun sides =>
      eval (depth + 2) generatedProgram [] (targetEnv left right) sides.2) =
        some (.complete answers)) : answers.length ≤ 1 := by
  obtain ⟨_, _, _, evaluated⟩ := (completed_body_iff depth occurrence left right answers).mp completed
  exact evaluated.at_most_one

/-- A source NativeType now licenses binding of an actually executed target
body. The premise is the source completion type, not a target cardinality
assumption. Whole-program provider dispatch remains a separate boundary. -/
theorem native_type_consumed_at_body (depth : Nat) (occurrence : Fin 4) (left right : Int)
    (call expected : SExpr)
    (queried : (sourceSides? occurrence).bind (fun sides =>
      SourceIntegerProvider.closeTerm? (sourceEnv left right) sides.1) = some call)
    (typed : SourceIntegerProviderNativeType.satisfiesNative
      (SourceIntegerProviderNativeType.echoNativeType expected)
      (.request ([providerSource], sourceEnv left right) ⟨occurrence, call⟩))
    (answers : List SExpr)
    (completed : (targetSides? occurrence).map (fun sides =>
      eval (depth + 2) generatedProgram [] (targetEnv left right) sides.2) =
        some (.complete answers)) :
    answers.length ≤ 1 ∧
      ∀ (env : Mettapedia.OSLF.MeTTaIL.Match.Bindings) (schema : SExpr)
        (continuation : Mettapedia.OSLF.MeTTaIL.Match.Bindings → List SExpr),
        (GeneratedPeTTaResultBinding.bindAnswers env schema (answers.take 1)).flatMap continuation =
          ((GeneratedPeTTaResultBinding.bindAnswers env schema answers).take 1).flatMap continuation := by
  obtain ⟨head, body, selected, evaluated⟩ :=
    (completed_body_iff depth occurrence left right answers).mp completed
  have sourceExecution : SourceIntegerProviderNativeType.source.Evaluates
      ([providerSource], sourceEnv left right) ⟨occurrence, call⟩
      ([providerSource], sourceEnv left right) answers := by
    refine ⟨rfl, head, body, ?_, ?_, evaluated⟩
    · rw [← sourceSides_from_admitted]
      exact selected
    · simpa [selected] using queried
  have licensed := (GeneratedPeTTaNativeTypeBinding.native_completion_binding
    _ _ expected typed).2 _ _ sourceExecution
  exact licensed.2

#print axioms actual_body_execution
#print axioms completed_body_iff
#print axioms completed_body_at_most_one
#print axioms native_type_consumed_at_body

end Mettapedia.GSLT.Parsing.GeneratedPeTTaIntegerProviderExecution
