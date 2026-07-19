import Mettapedia.Languages.MeTTa.HE.HumanEvalSpec
import MettaHyperonFull.Core.Bindings

/-!
# Evaluator outcome boundary

The fuel-free human evaluator describes semantic results only.  An executable
may additionally stop because its resource budget is exhausted.  This module
keeps those two outcomes disjoint without importing fuel into the human
semantics.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanEvalOutcome

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanEvalSpec

/-- An execution either returns a semantic result or reports resource
exhaustion.  `StackOverflow` is a resource outcome mirroring upstream's
documented stack-depth limit, not a semantic result. -/
inductive ExecutionOutcome (AtomT BindingsT : Type) where
  | semantic (result : AtomT × BindingsT)
  | resourceExhausted (source : AtomT) (bindings : BindingsT)

/-- Classify the exact HE stack-depth exhaustion shape outside the semantic
result lane.  Other error atoms remain semantic results. -/
def classifyHEResult : ResultPair → ExecutionOutcome Atom Bindings
  | (.expression [.symbol "Error", source, .symbol "StackOverflow"], bindings) =>
      .resourceExhausted source bindings
  | result => .semantic result

/-- Classify the exact LeaTTa stack-depth exhaustion shape outside the
semantic result lane.  Other error atoms remain semantic results. -/
def classifyLeaTTaResult :
    Metta.Atom × Metta.Bindings → ExecutionOutcome Metta.Atom Metta.Bindings
  | (.expr [.sym "Error", source, .sym "StackOverflow"], bindings) =>
      .resourceExhausted source bindings
  | result => .semantic result

/-- Constructor-independent statement that an outcome records resource
exhaustion. -/
def IsResourceExhaustion {AtomT BindingsT : Type}
    (outcome : ExecutionOutcome AtomT BindingsT) : Prop :=
  ∃ source bindings, outcome = .resourceExhausted source bindings

/-- A semantic outcome is justified by the fuel-free human evaluator. -/
def HumanSemanticOutcome
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : Bindings)
    (outcome : ExecutionOutcome Atom Bindings) : Prop :=
  ∃ result,
    outcome = .semantic result ∧
      HumanEval space dispatch live atom expectedType bindings result

/-! ## Classification canaries -/

/-- Positive: the documented HE exhaustion shape is classified as a resource
outcome. -/
example :
    classifyHEResult
        (.expression [.symbol "Error", .symbol "a", .symbol "StackOverflow"],
          Bindings.empty) =
      .resourceExhausted (.symbol "a") Bindings.empty := rfl

/-- Negative boundary canary: ordinary HE errors remain semantic results. -/
example :
    classifyHEResult
        (.expression [.symbol "Error", .symbol "a", .symbol "DivisionByZero"],
          Bindings.empty) =
      .semantic
        (.expression [.symbol "Error", .symbol "a", .symbol "DivisionByZero"],
          Bindings.empty) := rfl

/-- Positive: the documented LeaTTa exhaustion shape is classified as a
resource outcome. -/
example :
    classifyLeaTTaResult
        (.expr [.sym "Error", .sym "a", .sym "StackOverflow"], []) =
      .resourceExhausted (.sym "a") [] := rfl

/-- Negative boundary canary: an ordinary LeaTTa result remains semantic. -/
example : classifyLeaTTaResult (.sym "a", []) = .semantic (.sym "a", []) := rfl

end Mettapedia.Languages.MeTTa.HE.HumanEvalOutcome
