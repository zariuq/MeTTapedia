import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Minimal-instruction semantics

The published evaluator uses two host objects that ordinary MeTTa syntax
cannot inspect: the current context space and the binding snapshot stored by
`collapse-bind`.  This module keeps their representation abstract.  Concrete
interpreters choose carriers at the conformance boundary; the semantic rules
depend only on their observable role.

In particular, a collapsed binding set is not encoded as a MeTTa expression.
It is an opaque grounded value, and `superpose-bind` restores it before merging
it with the bindings at the continuation point.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge
open Spec.Eval
open Spec.Eval.Steps

/-- Host representations used only by the minimal-instruction layer.  The
carrier contains data; injectivity and other properties are separate laws. -/
structure Services where
  /-- Opaque grounded representation of a complete binding set. -/
  bindingPayload : Bindings → GroundedValue
  /-- Opaque grounded handle for the current context space. -/
  contextPayload : Space → GroundedValue
  /-- Behavior of the internal `call-native` instruction. -/
  nativeCall : Atom → Atom → Atom → Bindings → ResultPair → Prop

/-- Laws needed when an implementation realizes the opaque service.  They are
not fields of the data carrier, so partial or symbolic models can still state
the instruction relation without manufacturing proofs they do not possess. -/
structure ServiceLaws (services : Services) : Prop where
  /-- Distinct binding sets have distinct opaque identities. -/
  bindingPayload_injective : Function.Injective services.bindingPayload
  /-- A context-space handle is never confused with a collapsed binding set. -/
  contextPayload_ne_bindingPayload :
    ∀ space bindings, services.contextPayload space ≠ services.bindingPayload bindings

/-- An ordered enumeration profile for the fuel-free evaluator.  `EvalRel`
describes which individual results are semantically possible; this relation
separately records the order and multiplicity exposed by `collapse-bind`.

The carrier is relational because the published semantics need not choose one
global scheduler.  A concrete operational profile may nevertheless be
functional. -/
structure EvalEnumeration
    (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) where
  results : Space → Atom → Atom → Bindings → ResultSet → Prop

/-- The semantic law for an evaluation enumeration.  It must enumerate
exactly the support of `EvalRel`; its order and multiplicity remain explicit
data in the chosen profile rather than being reconstructed from membership.

This separation is necessary because individual `Prop`-valued derivations do
not determine how many operational alternatives produced the same result. -/
structure EvalEnumerationLaws
    {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService}
    (enumeration : EvalEnumeration dispatch live typing) : Prop where
  support_exact :
    ∀ space atom expectedType bindings results,
      enumeration.results space atom expectedType bindings results →
        ∀ result,
          result ∈ results ↔
            EvalRel space dispatch live atom expectedType bindings result
              (typing := typing)

/-- Encode one semantic result in the exact pair shape consumed by
`superpose-bind`. -/
def encodeResult (services : Services) (result : ResultPair) : Atom :=
  .expression [result.1, .grounded (services.bindingPayload result.2)]

/-- Encode an ordered list of results without changing order or multiplicity. -/
def encodeResults (services : Services) (results : ResultSet) : Atom :=
  .expression (results.map (encodeResult services))

/-- One state-free minimal-instruction step.  The context space is read-only;
the state-writing extension is specified separately by `StateAlgebra`.

`live` is the published equation-query environment threaded by `EvalRel`.
Every recursive evaluation premise uses the executable-independent evaluator,
never a runtime function. -/
inductive MinimalStepRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → Bindings → ResultPair → Prop where
  | eval (space : Space) (atom : Atom) (bindings : Bindings)
      (result : ResultPair) :
      EvalRel space dispatch live atom Atom.undefinedType bindings result
        (typing := typing) →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "eval", atom]) bindings result
  | evalc (space context : Space) (atom : Atom) (bindings : Bindings)
      (result : ResultPair) :
      EvalRel context dispatch live atom Atom.undefinedType bindings result
        (typing := typing) →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "evalc", atom,
          .grounded (services.contextPayload context)]) bindings result
  | chain (space : Space) (atom : Atom) (name : String) (template : Atom)
      (bindings : Bindings) (result : ResultPair) :
      EvalRel space dispatch live atom Atom.undefinedType bindings result
        (typing := typing) →
      result.1 ≠ Atom.empty →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "chain", atom, .var name, template]) bindings
        ((result.2.assign name result.1).applyDefault template,
          result.2.assign name result.1)
  | chainEmpty (space : Space) (atom : Atom) (name : String)
      (template : Atom) (bindings output : Bindings) :
      EvalRel space dispatch live atom Atom.undefinedType bindings
        (Atom.empty, output) (typing := typing) →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "chain", atom, .var name, template]) bindings
        (Atom.empty, output)
  | unify (space : Space) (target pattern thenBranch elseBranch result : Atom)
      (bindings output : Bindings) :
      UnifyStep target pattern thenBranch elseBranch bindings result output →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        bindings (result, output)
  | consAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : Bindings) :
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "cons-atom", head, .expression tail]) bindings
        (.expression (head :: tail), bindings)
  | deconsAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : Bindings) :
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "decons-atom", .expression (head :: tail)])
        bindings (.expression [head, .expression tail], bindings)
  | collapseBind (space : Space) (atom : Atom) (bindings : Bindings)
      (results : ResultSet) :
      enumeration.results space atom Atom.undefinedType bindings results →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "collapse-bind", atom]) bindings
        (encodeResults services results, bindings)
  | superposeBind (space : Space) (results : ResultSet)
      (stored : ResultPair) (bindings merged : Bindings) :
      stored ∈ results →
      MergeRel equalityGroundedSemantic stored.2 bindings merged →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "superpose-bind", encodeResults services results])
        bindings (stored.1, merged)
  | functionReturn (space : Space) (body returned : Atom)
      (bindings output : Bindings) :
      EvalRel space dispatch live body Atom.undefinedType bindings
        (.expression [.symbol "return", returned], output) (typing := typing) →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "function", body]) bindings (returned, output)
  | functionNoReturn (space : Space) (body result : Atom)
      (bindings output : Bindings) :
      EvalRel space dispatch live body Atom.undefinedType bindings
        (result, output) (typing := typing) →
      (∀ returned, result ≠ .expression [.symbol "return", returned]) →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "function", body]) bindings
        (Atom.error (.expression [.symbol "function", body])
          (.symbol "NoReturn"), output)
  | metta (space context : Space) (atom expectedType : Atom)
      (bindings : Bindings) (result : ResultPair) :
      EvalRel context dispatch live atom expectedType bindings result
        (typing := typing) →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "metta", atom, expectedType,
          .grounded (services.contextPayload context)]) bindings result
  | contextSpace (space : Space) (bindings : Bindings) :
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "context-space"]) bindings
        (.grounded (services.contextPayload space), bindings)
  | callNative (space : Space) (name function arguments : Atom)
      (bindings : Bindings) (result : ResultPair) :
      services.nativeCall name function arguments bindings result →
      MinimalStepRel services dispatch live typing enumeration space
        (.expression [.symbol "call-native", name, function, arguments])
        bindings result

/-! ## Boundary laws and canaries -/

/-- Under lawful services, equal opaque payloads identify the complete binding
sets they carry. -/
theorem bindings_eq_of_payload_eq {services : Services}
    (laws : ServiceLaws services) {left right : Bindings}
    (equal : services.bindingPayload left = services.bindingPayload right) :
    left = right :=
  laws.bindingPayload_injective equal

/-- A lawful enumeration lists precisely the individual semantic results.
The theorem intentionally says nothing about order or multiplicity: those are
the additional operational data carried by `EvalEnumeration.results`. -/
theorem result_mem_iff_evalRel
    {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService}
    {enumeration : EvalEnumeration dispatch live typing}
    (laws : EvalEnumerationLaws enumeration)
    {space : Space} {atom expectedType : Atom} {bindings : Bindings}
    {results : ResultSet}
    (enumerates : enumeration.results space atom expectedType bindings results)
    (result : ResultPair) :
    result ∈ results ↔
      EvalRel space dispatch live atom expectedType bindings result
        (typing := typing) :=
  laws.support_exact space atom expectedType bindings results enumerates result

/-- Positive canary: `context-space` returns the service's opaque handle and
does not change bindings. -/
example (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing)
    (space : Space) (bindings : Bindings) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "context-space"]) bindings
      (.grounded (services.contextPayload space), bindings) :=
  .contextSpace space bindings

/-- Negative canary: lawful opaque binding payloads cannot identify two
different binding sets. -/
theorem distinct_bindings_have_distinct_payloads {services : Services}
    (laws : ServiceLaws services) {left right : Bindings}
    (different : left ≠ right) :
    services.bindingPayload left ≠ services.bindingPayload right := by
  intro equal
  exact different (bindings_eq_of_payload_eq laws equal)

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
