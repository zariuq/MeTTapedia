import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution

/-!
# Completed ground execution under additional data constructors

The program and its callable names are unchanged. Enlarging the explicit
data-constructor inventory preserves completed execution; it may admit a
previously unsupported template. No claim equates unsupported or exhausted
observations, changes native translation, or permits callable result tags.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataHeadExtension

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaGroundExecution

def Extends (before after : List String) : Prop :=
  ∀ head, before.contains head = true → after.contains head = true

theorem extends_append (before additional : List String) : Extends before (before ++ additional) := by
  intro head present
  have member : head ∈ before := by simpa using present
  simpa using List.mem_append_left additional member

mutual
  theorem dataTemplate_mono {before after : List String} (extension : Extends before after)
      (expression : SExpr) (accepted : dataTemplate before expression = true) :
      dataTemplate after expression = true := by
    cases expression with
    | atom => rfl
    | list terms =>
        cases terms with
        | nil => simp [dataTemplate] at accepted
        | cons first rest =>
            cases first with
            | list => simp [dataTemplate] at accepted
            | atom head =>
                simp only [dataTemplate, Bool.and_eq_true] at accepted ⊢
                exact ⟨extension head accepted.1, dataTemplates_mono extension rest accepted.2⟩

  theorem dataTemplates_mono {before after : List String} (extension : Extends before after)
      (expressions : List SExpr) (accepted : dataTemplates before expressions = true) :
      dataTemplates after expressions = true := by
    cases expressions with
    | nil => rfl
    | cons first rest =>
        simp only [dataTemplates, Bool.and_eq_true] at accepted ⊢
        exact ⟨dataTemplate_mono extension first accepted.1,
          dataTemplates_mono extension rest accepted.2⟩
end

mutual
  theorem inertBinder_mono {before after : List String} (extension : Extends before after)
      (program : List (Nat × SExpr)) (expression : SExpr)
      (accepted : inertBinder program before expression = true) :
      inertBinder program after expression = true := by
    cases expression with
    | atom => rfl
    | list terms =>
        cases terms with
        | nil => simp [inertBinder] at accepted
        | cons first rest =>
            cases first with
            | list => simp [inertBinder] at accepted
            | atom head =>
                simp only [inertBinder, Bool.and_eq_true] at accepted ⊢
                exact ⟨⟨⟨accepted.1.1.1, accepted.1.1.2⟩,
                  extension head accepted.1.2⟩,
                  inertBinders_mono extension program rest accepted.2⟩

  theorem inertBinders_mono {before after : List String} (extension : Extends before after)
      (program : List (Nat × SExpr)) (expressions : List SExpr)
      (accepted : inertBinders program before expressions = true) :
      inertBinders program after expressions = true := by
    cases expressions with
    | nil => rfl
    | cons first rest =>
        simp only [inertBinders, Bool.and_eq_true] at accepted ⊢
        exact ⟨⟨accepted.1.1, inertBinder_mono extension program first accepted.1.2⟩,
          inertBinders_mono extension program rest accepted.2⟩
end

theorem collect_completed {α : Type} (before after : α → Outcome)
    (preserves : ∀ input answers, before input = .complete answers → after input = .complete answers)
    (inputs : List α) (answers : List SExpr) (completed : collect before inputs = .complete answers) :
    collect after inputs = .complete answers := by
  induction inputs generalizing answers with
  | nil => exact completed
  | cons first rest ih =>
      cases head : before first with
      | exhausted => simp [collect, head] at completed
      | outsideFragment => simp [collect, head] at completed
      | complete values =>
          cases tail : collect before rest with
          | exhausted => simp [collect, head, tail] at completed
          | outsideFragment => simp [collect, head, tail] at completed
          | complete following =>
              have same : values ++ following = answers := by
                simpa [collect, head, tail] using completed
              simp [collect, preserves first values head, ih following tail, same]

theorem runWith_completed (before after : Bindings → SExpr → Outcome)
    (preserves : ∀ env expression answers,
      before env expression = .complete answers → after env expression = .complete answers)
    (program : List (Nat × SExpr)) (call : SExpr) (answers : List SExpr)
    (completed : runWith before program call = .complete answers) :
    runWith after program call = .complete answers := by
  unfold runWith at completed ⊢
  split at completed
  · split at completed
    · cases completed
    · split
      · contradiction
      · apply collect_completed _ _ _ _ _ completed
        intro matched values found
        cases parsed : GeneratedPeTTaEquationDispatch.equation? matched.1.2 with
        | none => simp [parsed] at found
        | some pair =>
            simp only [parsed] at found ⊢
            exact preserves _ _ _ found
  · cases completed

theorem eval_completed {before after : List String} (extension : Extends before after)
    (depth : Nat) (program : List (Nat × SExpr)) (env : Bindings)
    (expression : SExpr) (answers : List SExpr)
    (completed : eval depth program before env expression = .complete answers) :
    eval depth program after env expression = .complete answers := by
  induction depth generalizing env expression answers with
  | zero => cases completed
  | succ depth ih =>
      unfold eval at completed ⊢
      split at completed
      all_goals try exact completed
      case h_3 => exact collect_completed _ _ (ih env) _ _ completed
      case h_4 =>
        rename_i original inner
        cases evaluated : eval depth program before env inner with
        | exhausted => simp [evaluated] at completed
        | outsideFragment => simp [evaluated] at completed
        | complete values =>
            simpa only [evaluated, ih env inner values evaluated] using completed
      case h_5 =>
        split at completed
        · exact ih _ _ _ completed
        · exact ih _ _ _ completed
        · cases completed
      case h_6 =>
        rename_i original schema value continuation
        cases permitted : inertBinder program before schema with
        | false => simp [permitted] at completed
        | true =>
            have newPermitted := inertBinder_mono extension program schema permitted
            simp only [permitted, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at completed
            simp only [newPermitted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases evaluated : eval depth program before env value with
            | exhausted => simp [evaluated] at completed
            | outsideFragment => simp [evaluated] at completed
            | complete values =>
                simp only [evaluated] at completed
                rw [ih env value values evaluated]
                exact collect_completed _ _ (fun next => ih next continuation) _ _ completed
      case h_7 =>
        rename_i original head templates _ _ _ _ _ _
        have guards : reserved head = false ∧ dataTemplates before templates = true := by
          cases reservedValue : reserved head <;>
            cases dataValue : dataTemplates before templates <;> simp_all
        have newData := dataTemplates_mono extension templates guards.2
        simp only [guards.1, guards.2, Bool.not_true, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte] at completed
        simp only [guards.1, newData, Bool.not_true, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte]
        cases instantiated : GeneratedPeTTaTemplateInstantiation.instantiateList? env templates with
        | none => simp [instantiated] at completed
        | some arguments =>
            simp only [instantiated] at completed
            exact runWith_completed _ _ ih _ _ _ completed

theorem run_completed {before after : List String} (extension : Extends before after)
    (depth : Nat) (program : List (Nat × SExpr)) (call : SExpr) (answers : List SExpr)
    (completed : run depth program before call = .complete answers) :
    run depth program after call = .complete answers :=
  runWith_completed _ _ (eval_completed extension depth program) _ _ _ completed

def packetBinder : SExpr := .list [.atom "packet", .atom "$value"]

def packetExample : SExpr :=
  .list [.atom "let", packetBinder,
    .list [.atom "quote", .list [.atom "packet", .atom "payload"]],
    .list [.atom "quote", .atom "$value"]]

theorem completed_binding_control :
    eval 3 [] ["packet"] [] packetExample = .complete [.atom "payload"] := by
  simp [packetExample, packetBinder, eval, inertBinder, inertBinders,
    reserved, knownFunction, GeneratedPeTTaEquationDispatch.equationsFor,
    GeneratedPeTTaResultBinding.bindAnswers, GeneratedPeTTaResultBinding.bindResult,
    GeneratedPeTTaResultBinding.template, GeneratedPeTTaResultBinding.templates,
    GeneratedPeTTaResultBinding.variableToken,
    GeneratedPeTTaTemplateInstantiation.instantiate_atom,
    SourceSExprPatternCodec.encode, SourceSExprPatternCodec.encodeList, SourceSExprPatternCodec.decode,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem completed_extension_control :
    eval 3 [] ["packet", "additional"] [] packetExample = .complete [.atom "payload"] :=
  eval_completed (extends_append ["packet"] ["additional"]) _ _ _ _ _ completed_binding_control

/-- The reverse assertion would be false: a larger inventory can admit a
previously unsupported binder. This is not observational equivalence of the
entire partial models. -/
theorem unsupported_not_preserved :
    eval 3 [] [] [] packetExample = .outsideFragment ∧
    eval 3 [] ["packet"] [] packetExample ≠ .outsideFragment := by
  constructor
  · simp [packetExample, packetBinder, eval, inertBinder]
  · rw [completed_binding_control]
    decide

theorem callable_tag_still_refused (program : List (Nat × SExpr))
    (heads : List String) (callable : knownFunction program "packet" = true) :
    inertBinder program heads packetBinder = false := by
  simp [packetBinder, inertBinder, callable]

#print axioms eval_completed
#print axioms run_completed
#print axioms completed_extension_control
#print axioms unsupported_not_preserved

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataHeadExtension
