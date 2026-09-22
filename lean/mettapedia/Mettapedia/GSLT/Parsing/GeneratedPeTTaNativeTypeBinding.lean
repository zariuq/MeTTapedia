import Mettapedia.GSLT.Parsing.GeneratedPeTTaResultBinding
import Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeCodec

/-!
# Consuming source completion types at the generated result-binding boundary

The actual inferred provider completion type supplies a finite zero-or-one
occurrence stream and retains its source environment. Those facts license
moving the selected `once` across ground result binding and preserve every
existing caller binding. The complete generated equation/body execution and
machine-Integer correspondence remain separate obligations.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaNativeTypeBinding

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Source)
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis
open SourceIntegerProviderNativeType
open GeneratedPeTTaResultBinding

/-- A native completion predicate supplies both existence and the strong
occurrence bound. Neither is inferred from a successful example. -/
theorem native_completion_binding (initial : State) (request : Request)
    (expected : SExpr)
    (typed : satisfiesNative (echoNativeType expected) (.request initial request)) :
    (∃ answers, source.Evaluates initial request initial answers) ∧
      ∀ final answers, source.Evaluates initial request final answers →
        final = initial ∧ answers.length ≤ 1 ∧
          ∀ (env : Bindings) (schema : SExpr) (body : Bindings → List SExpr),
            (bindAnswers env schema (answers.take 1)).flatMap body =
              ((bindAnswers env schema answers).take 1).flatMap body := by
  change completesOnly source (echoObservation expected) (.request initial request) at typed
  obtain ⟨⟨final, answers, executed⟩, observes⟩ :=
    (completesOnly_request_iff source (echoObservation expected) initial request).mp typed
  have first := observes final answers executed
  refine ⟨⟨answers, first.1 ▸ executed⟩, ?_⟩
  intro final answers executed
  have observation := observes final answers executed
  have small : answers.length ≤ 1 := by
    rcases observation.2 with rfl | rfl <;> simp
  exact ⟨observation.1, small, fun env schema body =>
    semidet_let_continuation env schema answers small body⟩

/-- Authentication is about the actual decoded sources and occurrence. Its
completion judgment is consumed in the result-binding theorem, not attached
as a passive label. This remains a selected-occurrence source license. -/
theorem authenticated_provider_binding
    {rawSources : List SExpr} {packet : IntegerProviderNativeTypeCodec.Packet}
    {sources : List Source} {info : BinaryTypeInfo}
    (decoded : IntegerProviderNativeTypeCodec.decodeSource? rawSources = some sources)
    (accepted : IntegerProviderNativeTypeCodec.authenticate rawSources packet = true)
    (member : info ∈ packet.types) :
    ∃ names, inputNamesAt? sources info.occurrence = some names ∧
      ∀ (providerEnv : SourceIntegerProvider.Env) (left right : Int),
        SourceIntegerProvider.lookup? providerEnv names.1 = some left →
        SourceIntegerProvider.lookup? providerEnv names.2 = some right →
        ∃ answers,
          source.Evaluates (sources, providerEnv)
            ⟨info.occurrence, binaryCall info.relation left right⟩
            (sources, providerEnv) answers ∧
          answers.length ≤ 1 ∧
          (∀ (env : Bindings) (schema : SExpr) (body : Bindings → List SExpr),
            (bindAnswers env schema (answers.take 1)).flatMap body =
              ((bindAnswers env schema answers).take 1).flatMap body) ∧
          (∀ (env next : Bindings) (schema : SExpr) (name : String) (before : Pattern),
            next ∈ bindAnswers env schema answers →
            env.find? (·.1 == name) = some (name, before) →
            next.find? (·.1 == name) = some (name, before)) := by
  obtain ⟨names, namesAt, echo⟩ :=
    IntegerProviderNativeTypeCodec.authenticated_info_echo decoded accepted member
  refine ⟨names, namesAt, ?_⟩
  intro providerEnv left right firstBound secondBound
  obtain ⟨⟨answers, executed⟩, allAnswers⟩ := native_completion_binding _ _ _
    (echo providerEnv left right firstBound secondBound)
  have observed := allAnswers _ answers executed
  exact ⟨answers, executed, observed.2.1, observed.2.2,
    fun env next schema name before returned bound =>
      bindAnswers_preserves_frame env schema answers next returned name before bound⟩

end Mettapedia.GSLT.Parsing.GeneratedPeTTaNativeTypeBinding
