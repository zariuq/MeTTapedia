import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.StateAlgebra

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

/-- Laws needed when an implementation realizes the opaque service.  They are
not fields of the data carrier, so partial or symbolic models can still state
the instruction relation without manufacturing proofs they do not possess. -/
structure ServiceLaws (services : Services) : Prop where
  /-- Distinct binding sets have distinct opaque identities. -/
  bindingPayload_injective : Function.Injective services.bindingPayload
  /-- A context-space handle is never confused with a collapsed binding set. -/
  contextPayload_ne_bindingPayload :
    ∀ space bindings, services.contextPayload space ≠ services.bindingPayload bindings

/-- The representation-only enumeration carrier is shared with full calls. -/
abbrev EvalEnumeration (_dispatch : GroundedDispatch) (_live : List Atom)
    (_typing : EvalTypeService) := Enumeration

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

/-- The shared core with this representation/collection package installed. -/
abbrev MinimalStepRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → Bindings → ResultPair → Prop :=
  fun space atom bindings result =>
    CoreStepRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing)

/-- The shared core with this representation/collection package installed. -/
abbrev RawInvocationRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → Bindings → ResultPair → Prop :=
  fun space atom bindings result =>
    CoreInvocationRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing)

/-- The shared core with this representation/collection package installed. -/
abbrev InvocationResultRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → Bindings → ResultPair → Prop :=
  fun space atom bindings result =>
    CoreInvocationResultRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing)

/-- The shared core with this representation/collection package installed. -/
abbrev MinimalRunRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → Bindings → ResultPair → Prop :=
  fun space atom bindings result =>
    CoreRunRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing)

/-- The shared core with this representation/collection package installed. -/
abbrev FunctionBodyRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) :
    Space → Atom → Bindings → ResultPair → Prop :=
  fun space atom bindings result =>
    CoreFunctionBodyRel space (withHost dispatch services enumeration) live atom bindings result
      (typing := typing)


/-- Final Empty results are omitted at the observation/collection boundary.
This does not suppress continuation activation inside the minimal machine. -/
def MinimalResultRel
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing)
    (space : Space) (atom : Atom) (bindings : Bindings) (result : ResultPair) : Prop :=
  MinimalRunRel services dispatch live typing enumeration space atom bindings result ∧
    result.1 ≠ Atom.empty

/-- A collapse profile enumerates the surviving minimal results, not the
full ordinary interpretation of the same syntax. Order and multiplicity are
additional profile data; the may relation fixes only support. -/
structure MinimalEnumerationLaws
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService)
    (enumeration : EvalEnumeration dispatch live typing) : Prop where
  support_exact :
    ∀ space atom bindings results,
      enumeration.minimalResults space atom bindings results →
        ∀ result, result ∈ results ↔
          MinimalResultRel services dispatch live typing enumeration
            space atom bindings result

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
  .contextSpace space bindings services enumeration rfl

/-- Negative canary: lawful opaque binding payloads cannot identify two
different binding sets. -/
theorem distinct_bindings_have_distinct_payloads {services : Services}
    (laws : ServiceLaws services) {left right : Bindings}
    (different : left ≠ right) :
    services.bindingPayload left ≠ services.bindingPayload right := by
  intro equal
  exact different (bindings_eq_of_payload_eq laws equal)

/-! ## Invocation and continuation boundary laws -/

theorem chain_is_embedded {atom : Atom} (chain : IsChain atom) :
    embeddedInstruction atom = true := by
  obtain ⟨tail, rfl⟩ := chain
  simp [embeddedInstruction]

theorem eval_is_not_chain (atom : Atom) :
    ¬IsChain (.expression [.symbol "eval", atom]) := by
  rintro ⟨tail, equal⟩
  simp at equal

theorem function_is_not_chain (body : Atom) :
    ¬IsChain (.expression [.symbol "function", body]) := by
  rintro ⟨tail, equal⟩
  simp at equal

/-- Noninstruction data is never interpreted merely because it looks like
an ordinary call. -/
theorem minimal_data_exact
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {bindings : Bindings} {result : ResultPair}
    (data : embeddedInstruction atom = false) :
    MinimalRunRel services dispatch live typing enumeration space atom bindings result ↔
      result = (atom, bindings) := by
  constructor
  · intro run
    cases run with
    | data => rfl
    | instruction _ _ _ _ embedded _ _ => simp [data] at embedded
    | chain _ _ _ _ _ chain _ _ =>
        have embedded := chain_is_embedded chain
        simp [data] at embedded
  · rintro rfl
    exact .data space atom bindings data

/-- Minimal eval completes precisely the raw operand invocation, with no
ordinary result re-interpretation inserted afterward. -/
theorem minimal_eval_exact
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {bindings : Bindings} {result : ResultPair} :
    MinimalRunRel services dispatch live typing enumeration space
      (.expression [.symbol "eval", atom]) bindings result ↔
    RawInvocationRel services dispatch live typing enumeration space atom bindings result := by
  constructor
  · intro run
    cases run with
    | data _ _ _ data => simp [embeddedInstruction] at data
    | instruction _ _ _ _ _ _ step =>
        generalize sourceEq : (Atom.expression [.symbol "eval", atom]) = source at step
        cases step with
        | eval _ _ _ _ invoke =>
            simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true] at sourceEq
            subst_vars
            exact invoke
        | _ => simp at sourceEq
    | chain _ _ _ _ _ chain _ _ => exact (eval_is_not_chain atom chain).elim
  · intro invoke
    exact .instruction space _ bindings result
      (by simp [embeddedInstruction]) (eval_is_not_chain atom)
      (.eval space atom bindings result invoke)

/-- Executing an embedded eval operand is another minimal dispatch, not
ordinary evaluation of a finished result. -/
theorem nested_eval_of_invocation
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {bindings : Bindings} {result : ResultPair}
    (notHost : ¬HostCall dispatch (.expression [.symbol "eval", atom]))
    (invoke : RawInvocationRel services dispatch live typing enumeration space
      atom bindings result) :
    MinimalRunRel services dispatch live typing enumeration space
      (.expression [.symbol "eval", .expression [.symbol "eval", atom]])
      bindings result := by
  apply minimal_eval_exact.mpr
  exact .embedded space _ bindings result notHost
    (by simp [embeddedInstruction]) (minimal_eval_exact.mpr invoke)

/-- Sequential evaluation really invokes the acquired member a second time;
the second invocation sees the first result's refined frame. The chain binder
is substituted locally and does not leak into that ambient frame. -/
theorem sequential_eval
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source member : Atom} {name : String}
    {bindings refined : Bindings} {result : ResultPair}
    (first : RawInvocationRel services dispatch live typing enumeration space
      source bindings (member, refined))
    (second : RawInvocationRel services dispatch live typing enumeration space
      member refined result) :
    MinimalRunRel services dispatch live typing enumeration space
      (.expression [.symbol "chain", .expression [.symbol "eval", source],
        .var name, .expression [.symbol "eval", .var name]]) bindings result := by
  apply CoreRunRel.chain space _ bindings
    (.expression [.symbol "eval", member], refined) result
  · exact ⟨_, rfl⟩
  · simpa [substituteName] using
      CoreStepRel.chain (dispatch := withHost dispatch services enumeration)
        (live := live) (typing := typing) space
        (.expression [.symbol "eval", source]) name
        (.expression [.symbol "eval", .var name]) bindings (member, refined)
        (minimal_eval_exact.mpr first)
  · exact minimal_eval_exact.mpr second

theorem empty_is_not_observable
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {atom : Atom} {bindings output : Bindings} :
    ¬MinimalResultRel services dispatch live typing enumeration space
      atom bindings (Atom.empty, output) := by
  rintro ⟨_, notEmpty⟩
  exact notEmpty rfl

/-- The typed ordinary interpreter's Atom guard has an exact singleton
support, independently of how the raw call produced its result. -/
theorem full_atom_expected_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom : Atom} {bindings : Bindings}
    {result : ResultPair} :
    EvalRel space dispatch live atom Atom.atomType bindings result
      (typing := typing) ↔ result = (atom, bindings) := by
  have rawExact : ∀ candidate,
      EvalAtomRawRel space dispatch live (typing := typing)
        atom Atom.atomType bindings candidate → candidate = (atom, bindings) := by
    intro candidate raw
    cases raw with
    | emptyOrError => rfl
    | typePass => rfl
    | cast _ _ _ _ _ _ _ doesNotPass _ _ => exact (doesNotPass (Or.inl rfl)).elim
    | interpretSuccess _ _ _ _ _ _ _ doesNotPass _ _ _ =>
        exact (doesNotPass (Or.inl rfl)).elim
    | interpretError _ _ _ _ _ _ _ doesNotPass _ _ _ =>
        exact (doesNotPass (Or.inl rfl)).elim
  constructor
  · exact fun evaluated => rawExact result evaluated.1
  · rintro rfl
    constructor
    · by_cases special : IsEmptyOrErrorRel atom
      · exact .emptyOrError atom Atom.atomType bindings special
      · have observedMeta : ∃ metaType, MetaTypeRel atom metaType := by
          cases atom with
          | symbol name => exact ⟨_, .symbol name⟩
          | var name => exact ⟨_, .variable name⟩
          | grounded value => exact ⟨_, .grounded value⟩
          | expression atoms => exact ⟨_, .expression atoms⟩
        obtain ⟨metaType, metaRelation⟩ := observedMeta
        exact .typePass atom Atom.atomType metaType bindings special metaRelation (Or.inl rfl)
    · intro error candidate raw
      simpa [rawExact candidate raw] using error

/-! ## Independent native boundary controls

The native service below emits a callable expression, computes its value,
or emits an empty alternative list. Its outcomes are specified independently
of both evaluator relations. Full interpretation uses the published type
service and one real arrow declaration, not a tailor-made type oracle. -/

private def probeMember : Atom := .expression [.symbol "leaf"]
private def probeValue : Atom := .grounded (.int 3)
private def probeFunction : Atom :=
  .expression [.symbol "function", .expression [.symbol "return", probeMember]]
private def probeArrow : Atom := .expression [.symbol "->", Atom.undefinedType]
private def probeSpace : Space :=
  ⟨[.expression [.symbol ":", .symbol "leaf", probeArrow]]⟩

private def probeDispatch : GroundedDispatch where
  executable := fun operator => operator = .symbol "emit" ∨
    operator = .symbol "leaf" ∨ operator = .symbol "none" ∨
    operator = .symbol "emit-function"
  outcome := fun operator arguments outcome =>
    (operator = .symbol "emit" ∧ arguments = [] ∧
      outcome = .ok [(probeMember, Bindings.empty)]) ∨
    (operator = .symbol "leaf" ∧ arguments = [] ∧
      outcome = .ok [(probeValue, Bindings.empty)]) ∨
    (operator = .symbol "none" ∧ arguments = [] ∧ outcome = .ok []) ∨
    (operator = .symbol "emit-function" ∧ arguments = [] ∧
      outcome = .ok [(probeFunction, Bindings.empty)])

private theorem merge_empty_empty :
    MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints, Bindings.empty]) .nil

private theorem empty_frame_satisfiable :
    ∃ valuation : String → Metta.Atom,
      LeaTTaBridge.HEBindingSatisfied valuation Bindings.empty :=
  ⟨fun name => .var name, by simp [LeaTTaBridge.HEBindingSatisfied, Bindings.empty]⟩

private theorem probe_invocation
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService)
    {operator emitted : Atom}
    (executable : probeDispatch.executable operator)
    (outcome : probeDispatch.outcome operator []
      (.ok [(emitted, Bindings.empty)]))
    (notFunction : ¬IsFunction emitted) :
    RawInvocationRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [operator]) Bindings.empty
      (emitted, Bindings.empty) := by
  exact .grounded probeSpace operator [] Bindings.empty Bindings.empty
    [(emitted, Bindings.empty)] (emitted, Bindings.empty)
    (emitted, Bindings.empty) emitted executable rfl outcome (by simp)
    merge_empty_empty empty_frame_satisfiable (by intros; rfl)
    (.raw probeSpace emitted Bindings.empty notFunction)

private theorem probe_emit_invocation
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    RawInvocationRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "emit"]) Bindings.empty
      (probeMember, Bindings.empty) := by
  apply probe_invocation services enumeration
  · exact Or.inl rfl
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · rintro ⟨body, equal⟩
    simp [probeMember] at equal

private theorem probe_leaf_invocation
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    RawInvocationRel services probeDispatch [] publishedTypeService enumeration
      probeSpace probeMember Bindings.empty (probeValue, Bindings.empty) := by
  apply probe_invocation services enumeration
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · rintro ⟨body, equal⟩
    simp [probeValue] at equal

/-- A native callable-looking result stays raw after minimal eval. -/
theorem native_member_is_raw
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "eval", .expression [.symbol "emit"]])
      Bindings.empty (probeMember, Bindings.empty) :=
  minimal_eval_exact.mpr (probe_emit_invocation services enumeration)

/-- Nesting eval does not reinterpret the already-finished native result. -/
theorem native_member_nested_eval_is_raw
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "eval", .expression
        [.symbol "eval", .expression [.symbol "emit"]]])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply nested_eval_of_invocation
  · rintro ⟨operator, arguments, equal, executable⟩
    simp only [Atom.expression.injEq, List.cons.injEq] at equal
    rcases equal with ⟨rfl, _⟩
    simp [probeDispatch] at executable
  · exact probe_emit_invocation services enumeration

/-- A chain explicitly evaluating the selected member does compute it. -/
theorem native_member_sequential_eval_computes
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "emit"]],
        .var "member", .expression [.symbol "eval", .var "member"]])
      Bindings.empty (probeValue, Bindings.empty) :=
  sequential_eval (probe_emit_invocation services enumeration)
    (probe_leaf_invocation services enumeration)

open Spec.Type in
private theorem probe_arrow_matches :
    TypeMatchRel probeArrow probeArrow Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural <;> try simp [probeArrow, Atom.undefinedType, Atom.atomType]
  · apply MatchRel.expression _ semanticLoopFree_empty
    exact .cons (.symSym "->" semanticLoopFree_empty) merge_empty_empty
      (.cons (.symSym "%Undefined%" semanticLoopFree_empty) merge_empty_empty .nil)
  · exact merge_empty_empty

open Spec.Type in
private theorem probe_leaf_types :
    TypesOfRel probeSpace (.symbol "leaf") [probeArrow] :=
  .symbolKnown (.hit .nil) (by simp)

open Spec.Type in
private theorem probe_value_full
    (protectedScope : List String := []) :
    EvalAtomRawRel probeSpace probeDispatch []
      (protectedScope := protectedScope) probeValue Atom.undefinedType
      Bindings.empty (probeValue, Bindings.empty) := by
  apply EvalAtomRawRel.cast probeValue Atom.undefinedType Atom.groundedType
    Bindings.empty (probeValue, Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, probeValue, Atom.empty]
  · exact .grounded (.int 3)
  · simp [Atom.undefinedType, Atom.atomType, Atom.groundedType, Atom.variableType]
  · exact Or.inr (Or.inl ⟨.int 3, rfl⟩)
  · apply TypeCastRel.success (earlierTypes := []) (laterTypes := [])
      (actualType := .symbol "Number")
    · exact .groundedKnown (.int 3) (by simp [Atom.undefinedType])
    · rfl
    · simp
    · exact .undefinedLeft _ _

open Spec.Type in
private theorem probe_leaf_full :
    EvalAtomRawRel probeSpace probeDispatch [] probeMember Atom.undefinedType
      Bindings.empty (probeValue, Bindings.empty) := by
  have headEval : EvalAtomRawRel probeSpace probeDispatch []
      (protectedScope := expectedApplicationScope probeMember Atom.undefinedType)
      (.symbol "leaf") probeArrow Bindings.empty (.symbol "leaf", Bindings.empty) := by
    apply EvalAtomRawRel.cast (.symbol "leaf") probeArrow Atom.symbolType
      Bindings.empty (.symbol "leaf", Bindings.empty)
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact .symbol "leaf"
    · simp [probeArrow, Atom.atomType, Atom.symbolType, Atom.variableType]
    · exact Or.inl ⟨"leaf", rfl⟩
    · apply TypeCastRel.success (earlierTypes := []) (laterTypes := [])
        (actualType := probeArrow) probe_leaf_types rfl
      · simp
      · exact probe_arrow_matches
  apply EvalAtomRawRel.interpretSuccess probeMember Atom.undefinedType Atom.expressionType
    Bindings.empty (probeValue, Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, probeMember, Atom.empty]
  · exact .expression [.symbol "leaf"]
  · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
  · exact ⟨.symbol "leaf", [], rfl⟩
  · apply InterpretExpressionRel.functionPath probeMember Atom.undefinedType
      (.symbol "leaf") [] [probeArrow] ⟨probeArrow, [], Atom.undefinedType, rfl⟩
      Atom.undefinedType Bindings.empty Bindings.empty
      (probeMember, Bindings.empty) (probeValue, Bindings.empty) rfl probe_leaf_types
    · apply FunctionCandidateScanRel.functionSuccess (argumentTypes := [])
        (returnType := Atom.undefinedType) rfl
      exact .success rfl (.success (.mk rfl rfl (.nil _) (.undefinedLeft _ _)))
    · simp [Atom.undefinedType, Atom.expressionType]
    · exact .success probeMember probeArrow Atom.undefinedType (.symbol "leaf")
        Atom.undefinedType [] [] Bindings.empty (.symbol "leaf", Bindings.empty)
        (Atom.unit, Bindings.empty) rfl rfl headEval
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.nil _)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, Atom.unit])
    · exact .groundedSuccess probeMember Atom.undefinedType (.symbol "leaf") []
        Bindings.empty [(probeValue, Bindings.empty)] (probeValue, Bindings.empty)
        (probeValue, Bindings.empty) Bindings.empty (probeValue, Bindings.empty)
        rfl (Or.inr (Or.inl rfl)) rfl
        (by simp) (by simp) (by simp [IsErrorRel, probeMember])
        (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (by simp) merge_empty_empty
        (.raw _ _ _ (by rintro ⟨_, equal⟩; simp [probeValue] at equal)) probe_value_full
  · simp [IsErrorRel, probeValue]

/-- The identical native emission is raw under Atom return demand and
computed under Undefined return demand. This exercises the existing full
call relation, independently of the new minimal invocation relation. -/
theorem native_return_demand_discriminates :
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit"])
      Atom.atomType Bindings.empty (probeMember, Bindings.empty) ∧
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit"])
      Atom.undefinedType Bindings.empty (probeValue, Bindings.empty) ∧
    probeMember ≠ probeValue := by
  have nativeCall : ∀ expected result,
      EvalAtomRawRel probeSpace probeDispatch [] probeMember expected Bindings.empty result →
      CallRel probeSpace probeDispatch [] (.expression [.symbol "emit"])
        expected Bindings.empty result := by
    intro expected result evaluated
    exact .groundedSuccess _ expected (.symbol "emit") [] Bindings.empty
      [(probeMember, Bindings.empty)] (probeMember, Bindings.empty) result Bindings.empty
      (probeMember, Bindings.empty)
      rfl (Or.inl rfl) rfl (by simp) (by simp) (by simp [IsErrorRel])
      (Or.inl ⟨rfl, rfl, rfl⟩) (by simp) merge_empty_empty
      (.raw _ _ _ (by rintro ⟨_, equal⟩; simp [probeMember] at equal)) evaluated
  exact ⟨nativeCall _ _ ((full_atom_expected_exact.mpr rfl).1),
    nativeCall _ _ probe_leaf_full, by simp [probeMember, probeValue]⟩

/-- Negative typed-boundary control: Atom demand cannot compute the member
into its native value. This excludes the erroneous recursive continuation,
not merely constructs one allowed raw derivation. -/
theorem atom_demand_cannot_compute_member :
    ¬EvalRel probeSpace probeDispatch [] probeMember Atom.atomType
      Bindings.empty (probeValue, Bindings.empty) := by
  intro evaluated
  have unchanged := full_atom_expected_exact.mp evaluated
  simp [probeMember, probeValue] at unchanged

/-- A function emitted by a native call executes its delimiter before the
caller's return demand. This is the very same completion judgment consumed
by full calls and by raw minimal invocation. -/
private theorem probe_function_completes
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (bindings : Bindings) :
    CoreInvocationResultRel space dispatch live probeFunction bindings
      (probeMember, bindings) (typing := typing) := by
  apply CoreInvocationResultRel.function
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  · exact .terminal space _ bindings (by simp [embeddedInstruction])

/-- An immediately returning emitted function has exactly its declared
return value as completion support. It cannot be mistaken for held function
syntax, nor may its return value be re-invoked during completion. -/
theorem immediate_function_completion_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {returned : Atom} {bindings : Bindings}
    {result : ResultPair} :
    CoreInvocationResultRel space dispatch live
      (.expression [.symbol "function", .expression [.symbol "return", returned]])
      bindings result (typing := typing) ↔ result = (returned, bindings) := by
  constructor
  · intro completed
    cases completed with
    | raw _ _ _ notFunction => exact (notFunction ⟨_, rfl⟩).elim
    | function _ _ _ _ step =>
        generalize sourceEq :
          (Atom.expression [.symbol "function", .expression [.symbol "return", returned]]) =
            source at step
        cases step with
        | functionReturn _ _ _ _ _ _ body =>
            simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true] at sourceEq
            subst_vars
            cases body with
            | terminal => rfl
            | resume _ _ _ _ _ embedded _ _ => simp [embeddedInstruction] at embedded
        | functionNoReturn _ _ _ _ _ _ body noReturn =>
            simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true] at sourceEq
            subst_vars
            cases body with
            | terminal => exact (noReturn returned rfl).elim
            | resume _ _ _ _ _ embedded _ _ => simp [embeddedInstruction] at embedded
        | _ => simp at sourceEq
  · rintro rfl
    exact .function space _ bindings (returned, bindings)
      (.functionReturn space _ returned bindings bindings ⟨_, rfl⟩
        (.terminal space _ bindings (by simp [embeddedInstruction])))

/-- Full native calls execute an emitted function before Atom freezes its
returned member; Undefined instead resumes full interpretation of that
member. The function block itself is not the Atom-demand result. -/
theorem native_function_completion_precedes_return_demand :
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit-function"])
      Atom.atomType Bindings.empty (probeMember, Bindings.empty) ∧
    CallRel probeSpace probeDispatch [] (.expression [.symbol "emit-function"])
      Atom.undefinedType Bindings.empty (probeValue, Bindings.empty) ∧
    probeFunction ≠ probeMember := by
  have completedCall : ∀ expected result,
      EvalAtomRawRel probeSpace probeDispatch [] probeMember expected Bindings.empty result →
      CallRel probeSpace probeDispatch [] (.expression [.symbol "emit-function"])
        expected Bindings.empty result := by
    intro expected result evaluated
    exact .groundedSuccess _ expected (.symbol "emit-function") [] Bindings.empty
      [(probeFunction, Bindings.empty)] (probeFunction, Bindings.empty) result Bindings.empty
      (probeMember, Bindings.empty) rfl (Or.inr (Or.inr (Or.inr rfl))) rfl
      (by simp) (by simp) (by simp [IsErrorRel])
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) (by simp) merge_empty_empty
      (probe_function_completes _ _ _ _ _) evaluated
  exact ⟨completedCall _ _ ((full_atom_expected_exact.mpr rfl).1),
    completedCall _ _ probe_leaf_full, by simp [probeFunction, probeMember]⟩

/-- Explicit Atom interpretation of the source function is different from
completing a function emitted by an invoked operation. The source is held
verbatim, with its original bindings. -/
theorem source_function_under_atom_demand_is_held :
    EvalRel probeSpace probeDispatch [] probeFunction Atom.atomType Bindings.empty
      (probeFunction, Bindings.empty) ∧
    ¬EvalRel probeSpace probeDispatch [] probeFunction Atom.atomType Bindings.empty
      (probeMember, Bindings.empty) := by
  constructor
  · exact full_atom_expected_exact.mpr rfl
  · intro evaluated
    have unchanged := full_atom_expected_exact.mp evaluated
    simp [probeFunction, probeMember] at unchanged

/-! ## Producer-completed native values

The phase tag belongs to the producer protocol, not to the returned syntax.
These probes test that protocol independently of any particular native
library: they are not a realization proof for an opaque host service.
-/

/-- A completed value at a keep boundary has exactly its original syntax
and frame as support. The cast constructor is excluded, not merely unused. -/
theorem completed_native_keep_exact
    {space : Space} {typing : EvalTypeService} {value expectedType : Atom}
    {bindings : Bindings} {result : ResultPair}
    (keep : CompletedNativeKeepRel value expectedType) :
    CompletedNativeReturnRel space typing value expectedType bindings result ↔
      result = (value, bindings) := by
  constructor
  · intro returned
    cases returned with
    | keep => rfl
    | cast notKeep _ => exact (notKeep keep).elim
  · rintro rfl
    exact .keep keep

/-- Undefined demand does not re-enter interpretation of a completed value. -/
theorem completed_native_undefined_exact
    {space : Space} {typing : EvalTypeService} {value : Atom}
    {bindings : Bindings} {result : ResultPair} :
    CompletedNativeReturnRel space typing value Atom.undefinedType bindings result ↔
      result = (value, bindings) :=
  completed_native_keep_exact (Or.inr (Or.inl rfl))

/-- Concrete demands outside the keep boundary use precisely the existing
cast judgment, including its refined frame or structured failure result. -/
theorem completed_native_cast_exact
    {space : Space} {typing : EvalTypeService} {value expectedType : Atom}
    {bindings : Bindings} {result : ResultPair}
    (notKeep : ¬CompletedNativeKeepRel value expectedType) :
    CompletedNativeReturnRel space typing value expectedType bindings result ↔
      typing.typeCast [] space value expectedType bindings result := by
  constructor
  · intro returned
    cases returned with
    | keep keep => exact (notKeep keep).elim
    | cast _ cast => exact cast
  · exact .cast notKeep

/-- A completed Error remains held even under an incompatible demand. -/
theorem completed_native_error_exact
    {space : Space} {typing : EvalTypeService} {value expectedType : Atom}
    {bindings : Bindings} {result : ResultPair} (error : IsErrorRel value) :
    CompletedNativeReturnRel space typing value expectedType bindings result ↔
      result = (value, bindings) :=
  completed_native_keep_exact (Or.inl (Or.inr error))

private def completedProbeDispatch : GroundedDispatch :=
  { probeDispatch with valueProvenance := fun _ _ => .completed }

/-- The identical function-shaped native payload is held under both Atom
and Undefined when the producer certifies completion. Ordinary emissions
still execute their function delimiter, as the preceding control proves. -/
theorem completed_native_function_stays_data :
    CallRel probeSpace completedProbeDispatch []
      (.expression [.symbol "emit-function"]) Atom.atomType Bindings.empty
      (probeFunction, Bindings.empty) ∧
    CallRel probeSpace completedProbeDispatch []
      (.expression [.symbol "emit-function"]) Atom.undefinedType Bindings.empty
      (probeFunction, Bindings.empty) ∧
    probeFunction ≠ probeMember := by
  have held (expected : Atom) (keep : CompletedNativeKeepRel probeFunction expected) :
      CallRel probeSpace completedProbeDispatch []
        (.expression [.symbol "emit-function"]) expected Bindings.empty
        (probeFunction, Bindings.empty) := by
    exact .groundedCompletedSuccess _ expected (.symbol "emit-function") []
      Bindings.empty [(probeFunction, Bindings.empty)] (probeFunction, Bindings.empty)
      (probeFunction, Bindings.empty) Bindings.empty rfl
      (Or.inr (Or.inr (Or.inr rfl))) rfl (by simp) (by simp)
      (by simp [IsErrorRel]) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
      (by simp) merge_empty_empty (.keep keep)
  exact ⟨held _ (Or.inr (Or.inr (Or.inl rfl))),
    held _ (Or.inr (Or.inl rfl)), by simp [probeFunction, probeMember]⟩

/-- Raw invocation consumes completed provenance too; an instruction-shaped
payload is not treated as a newly emitted function block. -/
theorem completed_native_raw_function_is_held
    (services : Services)
    (enumeration : EvalEnumeration completedProbeDispatch [] publishedTypeService) :
    MinimalRunRel services completedProbeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "eval", .expression [.symbol "emit-function"]])
      Bindings.empty (probeFunction, Bindings.empty) := by
  apply minimal_eval_exact.mpr
  exact .completedGrounded probeSpace (.symbol "emit-function") []
    Bindings.empty Bindings.empty [(probeFunction, Bindings.empty)]
    (probeFunction, Bindings.empty) probeFunction
    (Or.inr (Or.inr (Or.inr rfl))) rfl
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) (by simp)
    merge_empty_empty empty_frame_satisfiable (by intros; rfl)

private theorem completed_number_not_keep (expected : Atom)
    (notUndefined : expected ≠ Atom.undefinedType)
    (notAtom : expected ≠ Atom.atomType)
    (notGrounded : expected ≠ Atom.groundedType) :
    ¬CompletedNativeKeepRel probeValue expected := by
  rintro (special | undefined | atom | ⟨metaType, metaRelation, matched | variableMeta⟩)
  · simp [IsEmptyOrErrorRel, IsErrorRel, probeValue, Atom.empty] at special
  · exact notUndefined undefined
  · exact notAtom atom
  · cases metaRelation
    exact notGrounded matched
  · cases metaRelation
    simp [Atom.groundedType, Atom.variableType] at variableMeta

open Spec.Type in
/-- A completed number is still checked against Bool and returns the real
published BadType failure; completion does not authorize a failed cast. -/
theorem completed_native_number_rejects_bool :
    CallRel probeSpace completedProbeDispatch [] probeMember (.symbol "Bool")
      Bindings.empty
      (mkError probeValue (.badType (.symbol "Bool") (.symbol "Number")),
        Bindings.empty) := by
  apply CallRel.groundedCompletedSuccess probeMember (.symbol "Bool") (.symbol "leaf")
    [] Bindings.empty [(probeValue, Bindings.empty)] (probeValue, Bindings.empty)
    _ Bindings.empty rfl (Or.inr (Or.inl rfl)) rfl (by simp) (by simp)
    (by simp [IsErrorRel, probeMember]) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    (by simp) merge_empty_empty
  apply CompletedNativeReturnRel.cast
    (completed_number_not_keep _ (by decide) (by decide) (by decide))
  apply TypeCastRel.failure (types := [.symbol "Number"]) (actualType := .symbol "Number")
  · exact .groundedKnown (.int 3) (by simp [Atom.undefinedType])
  · simp
  · intro candidateType member candidate matched
    simp only [List.mem_singleton] at member
    subst candidateType
    obtain ⟨frame, structural, _⟩ := matched.structural_of_nonWildcard
      (by decide) (by decide) (by decide) (by decide)
    exact symbol_mismatch_not_match (by decide) frame structural

open Spec.Type in
/-- The same completed number can refine an expected type variable through
the existing structural match and binding merge, without evaluator re-entry. -/
theorem completed_native_number_binds_type_variable :
    CallRel probeSpace completedProbeDispatch [] probeMember (.var "T")
      Bindings.empty
      (probeValue, Bindings.empty.assign "T" (.symbol "Number")) := by
  apply CallRel.groundedCompletedSuccess probeMember (.var "T") (.symbol "leaf")
    [] Bindings.empty [(probeValue, Bindings.empty)] (probeValue, Bindings.empty)
    _ Bindings.empty rfl (Or.inr (Or.inl rfl)) rfl (by simp) (by simp)
    (by simp [IsErrorRel, probeMember]) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    (by simp) merge_empty_empty
  apply CompletedNativeReturnRel.cast
    (completed_number_not_keep _ (by decide) (by decide) (by decide))
  apply TypeCastRel.success (types := [.symbol "Number"])
    (earlierTypes := []) (laterTypes := []) (actualType := .symbol "Number")
  · exact .groundedKnown (.int 3) (by simp [Atom.undefinedType])
  · rfl
  · simp
  · apply TypeMatchRel.structural <;> try decide
    · exact .varNonVar rfl (semanticLoopFree_single_assignment (by intro occurrence; cases occurrence))
    · apply MergeRel.mk (order := [.value "T" (.symbol "Number")])
      · decide
      · exact .value (.fresh (by simp [Bindings.classValues, Bindings.lookup, Bindings.empty])) .nil

/-! ## Embedded typed interpretation connection

The shared core admits ordinary non-error interpretation results and exact
Atom/error passthrough. General error-priority completeness requires an
all-alternatives collecting interpreter and is not asserted by this fragment.
-/

/-- A non-error embedded typed result is a public full result, not merely a
raw error candidate. This follows from the independent public success rule. -/
theorem embedded_metta_nonerror_is_full_result
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom expectedType : Atom} {bindings : Bindings}
    {result : ResultPair}
    (evaluated : EvalAtomRawRel space dispatch live atom expectedType bindings result
      (typing := typing)) (notError : ¬IsErrorRel result.1) :
    EvalRel space dispatch live atom expectedType bindings result (typing := typing) := by
  exact ⟨evaluated, fun error => (notError error).elim⟩

/-- Empty and syntactic error inputs have exact passthrough support under
every expected type. In particular the embedded error-input rule satisfies
the full public error-priority boundary rather than inventing an error lane. -/
theorem full_special_input_exact
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {atom expectedType : Atom} {bindings : Bindings}
    {result : ResultPair} (special : IsEmptyOrErrorRel atom) :
    EvalRel space dispatch live atom expectedType bindings result (typing := typing) ↔
      result = (atom, bindings) := by
  have rawExact : ∀ candidate,
      EvalAtomRawRel space dispatch live atom expectedType bindings candidate
        (typing := typing) → candidate = (atom, bindings) := by
    intro candidate raw
    cases raw <;> first | rfl | contradiction
  constructor
  · exact fun evaluated => rawExact result evaluated.1
  · rintro rfl
    refine ⟨.emptyOrError _ _ _ special, ?_⟩
    intro error candidate raw
    simpa [rawExact candidate raw] using error

/-- Explicit embedded metta with expected Atom holds even an executable
function source. It is not raw invocation completion. -/
theorem embedded_metta_atom_holds_function
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (enumeration : EvalEnumeration dispatch live typing)
    (space context : Space) (body : Atom) (bindings : Bindings) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "metta", .expression [.symbol "function", body], Atom.atomType,
        .grounded (services.contextPayload context)]) bindings
      (.expression [.symbol "function", body], bindings) :=
  .mettaAtom space context _ bindings services enumeration rfl

/-! ## Independent equation and context controls -/

private def noHostDispatch : GroundedDispatch :=
  ⟨fun _ => False, fun _ _ _ => False, none, fun _ _ => .emitted⟩
private def equationProbeSpace : Space :=
  ⟨[.expression [.symbol "=", .symbol "source", probeMember]]⟩

private theorem equation_probe_candidate :
    EquationQueryCandidateRel equationProbeSpace [] (.symbol "source")
      Bindings.empty probeMember Bindings.empty := by
  refine ⟨.symbol "source", probeMember, Bindings.empty, ?_,
    merge_empty_empty, semanticLoopFree_empty, empty_frame_satisfiable, ?_⟩
  · refine ⟨.symbol "source", probeMember, ?_, ?_,
      .symSym "source" semanticLoopFree_empty⟩
    · simp [equationProbeSpace]
    · refine ⟨id, Function.injective_id, .symbol "source",
        .expression (.cons (.symbol "leaf") .nil), ?_⟩
      intro name occurrence
      rcases occurrence with occurrence | occurrence
      · cases occurrence
      · cases occurrence with
        | expression member occurs =>
            simp only [List.mem_singleton] at member
            subst_vars
            cases occurs
  · intros
    rfl

/-- Equation selection also leaves a callable-looking RHS raw. The proof
uses actual hygienic matching and binding merge, not ordinary EvalRel. -/
theorem equation_result_is_raw
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalRunRel services noHostDispatch [] publishedTypeService enumeration
      equationProbeSpace (.expression [.symbol "eval", .symbol "source"])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply minimal_eval_exact.mpr
  apply CoreInvocationRel.equation
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · exact equation_probe_candidate
  · exact .raw _ _ _ (by rintro ⟨body, equal⟩; simp [probeMember] at equal)

private def functionEquationSpace : Space :=
  ⟨[.expression [.symbol "=", .symbol "source-function", probeFunction]]⟩

private theorem function_equation_candidate :
    EquationQueryCandidateRel functionEquationSpace [] (.symbol "source-function")
      Bindings.empty probeFunction Bindings.empty := by
  refine ⟨.symbol "source-function", probeFunction, Bindings.empty, ?_,
    merge_empty_empty, semanticLoopFree_empty, empty_frame_satisfiable, ?_⟩
  · refine ⟨.symbol "source-function", probeFunction, ?_, ?_,
      .symSym "source-function" semanticLoopFree_empty⟩
    · simp [functionEquationSpace]
    · refine ⟨id, Function.injective_id, .symbol "source-function",
        .expression (.cons (.symbol "function") (.cons
          (.expression (.cons (.symbol "return") (.cons
            (.expression (.cons (.symbol "leaf") .nil)) .nil))) .nil)), ?_⟩
      intro name occurrence
      rcases occurrence with occurrence | occurrence
      · cases occurrence
      · cases occurrence with
        | expression member occurs =>
            simp at member
            rcases member with rfl | rfl
            · cases occurs
            · cases occurs with
              | expression member occurs =>
                  simp at member
                  rcases member with rfl | rfl
                  · cases occurs
                  · cases occurs with
                    | expression member occurs =>
                        simp only [List.mem_singleton] at member
                        subst_vars
                        cases occurs
  · intros
    rfl

/-- A hygienically selected equation RHS function executes before the full
call's Atom demand. Atom demand freezes its returned member, not the emitted
function syntax. The equation, matching and merge witnesses are concrete. -/
theorem equation_function_completion_precedes_atom_demand :
    CallRel functionEquationSpace noHostDispatch [] (.symbol "source-function")
      Atom.atomType Bindings.empty (probeMember, Bindings.empty) := by
  exact .equation _ Atom.atomType probeFunction Bindings.empty Bindings.empty
    (probeMember, Bindings.empty) (probeMember, Bindings.empty)
    (by simp [IsErrorRel]) (by simp [NonGroundedCallRel]) function_equation_candidate
    (probe_function_completes _ _ _ _ _) ((full_atom_expected_exact.mpr rfl).1)

/-- Raw equation invocation and full call completion share the same emitted
function delimiter. Neither requires evaluating its returned member. -/
theorem raw_equation_function_returns_member
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalRunRel services noHostDispatch [] publishedTypeService enumeration
      functionEquationSpace
      (.expression [.symbol "eval", .symbol "source-function"])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply minimal_eval_exact.mpr
  exact .equation _ _ probeFunction Bindings.empty Bindings.empty
    (probeMember, Bindings.empty)
    (by rintro ⟨_, _, _, impossible⟩; exact impossible) rfl function_equation_candidate
    (probe_function_completes _ _ _ _ _)

/-- evalc invokes the supplied context, not the caller space; a real rule in
that context supplies the raw result even though the caller has no rules. -/
theorem evalc_uses_supplied_context
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalStepRel services noHostDispatch [] publishedTypeService enumeration
      Space.empty (.expression [.symbol "evalc", .symbol "source",
        .grounded (services.contextPayload equationProbeSpace)])
      Bindings.empty (probeMember, Bindings.empty) := by
  apply CoreStepRel.evalc (services := services) (enumeration := enumeration)
  · rfl
  apply CoreInvocationRel.equation
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · exact equation_probe_candidate
  · exact .raw _ _ _ (by rintro ⟨body, equal⟩; simp [probeMember] at equal)

/-- In the empty current space, the same ordinary raw query is NotReducible,
which distinguishes context selection from global/default lookup. -/
theorem empty_context_is_not_reducible
    (services : Services)
    (enumeration : EvalEnumeration noHostDispatch [] publishedTypeService) :
    MinimalRunRel services noHostDispatch [] publishedTypeService enumeration
      Space.empty (.expression [.symbol "eval", .symbol "source"])
      Bindings.empty (Atom.notReducible, Bindings.empty) := by
  apply minimal_eval_exact.mpr
  apply CoreInvocationRel.noEquation
  · rintro ⟨_, _, _, executable⟩
    exact executable
  · rfl
  · intro freshPattern freshRhs matched rule
    obtain ⟨lhs, rhs, member, _⟩ := rule
    simp [Space.empty] at member

/-! ## Local binders, ordered alternatives, and the Empty boundary -/

/-- Instantiate each selected occurrence in order, without deduplication or
exporting the local chain binder into the ambient frame. In particular the
minimal machine does not discard an internal Empty source here. -/
def chainActivations (name : String) (template : Atom) (results : ResultSet) : ResultSet :=
  results.map fun result => (substituteName name result.1 template, result.2)

/-- Every independently enumerated source occurrence justifies its concrete
activation by the minimal chain rule. This connects ordered data to the
instruction relation rather than defining one to be the other. -/
theorem chain_activation_is_step
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source : Atom} {bindings : Bindings} {selected : ResultPair}
    (run : MinimalRunRel services dispatch live typing enumeration space
      source bindings selected) (name : String) (template : Atom) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "chain", source, .var name, template]) bindings
      (substituteName name selected.1 template, selected.2) :=
  .chain space source name template bindings selected run

theorem chain_activations_append (name : String) (template : Atom)
    (left right : ResultSet) :
    chainActivations name template (left ++ right) =
      chainActivations name template left ++ chainActivations name template right := by
  simp [chainActivations]

theorem chain_activations_preserve_ambient_frames (name : String) (template : Atom)
    (results : ResultSet) :
    (chainActivations name template results).map Prod.snd = results.map Prod.snd := by
  simp [chainActivations, List.map_map]

theorem chain_activations_keep_duplicate_occurrences (name : String) (template : Atom)
    (result : ResultPair) :
    chainActivations name template [result, result] =
      [(substituteName name result.1 template, result.2),
        (substituteName name result.1 template, result.2)] := rfl

/-- The substituted template is data unless it is explicitly an embedded
instruction. Its caller frame contains source refinements, not a new binder. -/
theorem chain_data_template
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source : Atom} {bindings : Bindings} {selected : ResultPair}
    (run : MinimalRunRel services dispatch live typing enumeration space
      source bindings selected) (name : String) (template : Atom)
    (data : embeddedInstruction (substituteName name selected.1 template) = false) :
    MinimalRunRel services dispatch live typing enumeration space
      (.expression [.symbol "chain", source, .var name, template]) bindings
      (substituteName name selected.1 template, selected.2) :=
  .chain space _ bindings _ _ ⟨_, rfl⟩
    (chain_activation_is_step run name template) (.data space _ selected.2 data)

/-- A return-shaped source is locally bound as data; it does not prematurely
return from the surrounding function. -/
theorem return_shaped_chain_source_is_data
    (services : Services) (dispatch : GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (enumeration : EvalEnumeration dispatch live typing)
    (space : Space) (bindings : Bindings) (value : Atom) :
    MinimalRunRel services dispatch live typing enumeration space
      (.expression [.symbol "chain", .expression [.symbol "return", value],
        .var "selected", .expression [.symbol "kept", .var "selected"]]) bindings
      (.expression [.symbol "kept", .expression [.symbol "return", value]], bindings) := by
  simpa [substituteName] using chain_data_template
    (.data space (.expression [.symbol "return", value]) bindings
      (by simp [embeddedInstruction])) "selected"
      (.expression [.symbol "kept", .var "selected"])
      (by simp [substituteName, embeddedInstruction])

/-- A function returns the locally selected value without interpreting that
value as a fresh call. Source binding refinements survive, but the explicit
local binder does not escape. -/
theorem function_chain_returns_selected_raw
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    {space : Space} {source value : Atom} {bindings refined : Bindings}
    (run : MinimalRunRel services dispatch live typing enumeration space
      source bindings (value, refined)) (name : String) :
    MinimalStepRel services dispatch live typing enumeration space
      (.expression [.symbol "function", .expression [.symbol "chain", source,
        .var name, .expression [.symbol "return", .var name]]]) bindings
      (value, refined) := by
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  apply CoreFunctionBodyRel.resume
  · simp [embeddedInstruction]
  · simpa [substituteName] using chain_data_template run name
      (.expression [.symbol "return", .var name])
      (by simp [substituteName, embeddedInstruction])
  · exact .terminal space _ refined (by simp [embeddedInstruction])

private theorem probe_empty_invocation
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    RawInvocationRel services probeDispatch [] publishedTypeService enumeration
      probeSpace (.expression [.symbol "none"]) Bindings.empty (Atom.empty, Bindings.empty) :=
  .groundedEmpty probeSpace (.symbol "none") [] Bindings.empty
    (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))

/-- The published minimal continuation can run after an Empty native source.
An independent constant return reaches the function boundary normally. This
positive control prevents confusing minimal chain with a pruning map. -/
theorem minimal_empty_source_can_activate_constant_return
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalStepRel services probeDispatch [] publishedTypeService enumeration probeSpace
      (.expression [.symbol "function", .expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "none"]], .var "selected",
        .expression [.symbol "return", .symbol "reached"]]])
      Bindings.empty (.symbol "reached", Bindings.empty) := by
  apply CoreStepRel.functionReturn
  · exact ⟨_, rfl⟩
  apply CoreFunctionBodyRel.resume
  · simp [embeddedInstruction]
  · simpa [substituteName] using chain_data_template
      (minimal_eval_exact.mpr (probe_empty_invocation services enumeration))
      "selected" (.expression [.symbol "return", .symbol "reached"])
      (by simp [substituteName, embeddedInstruction])
  · exact .terminal probeSpace _ Bindings.empty (by simp [embeddedInstruction])

/-- Returning the selected Empty sentinel completes the internal function,
but contributes no public result. This differs from the preceding constant
continuation, which does not return the selected sentinel. -/
theorem minimal_empty_selected_return_is_filtered
    (services : Services)
    (enumeration : EvalEnumeration probeDispatch [] publishedTypeService) :
    MinimalRunRel services probeDispatch [] publishedTypeService enumeration probeSpace
      (.expression [.symbol "function", .expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "none"]], .var "selected",
        .expression [.symbol "return", .var "selected"]]])
      Bindings.empty (Atom.empty, Bindings.empty) ∧
    ¬MinimalResultRel services probeDispatch [] publishedTypeService enumeration probeSpace
      (.expression [.symbol "function", .expression [.symbol "chain",
        .expression [.symbol "eval", .expression [.symbol "none"]], .var "selected",
        .expression [.symbol "return", .var "selected"]]])
      Bindings.empty (Atom.empty, Bindings.empty) := by
  constructor
  · apply CoreRunRel.instruction
    · simp [embeddedInstruction]
    · exact function_is_not_chain _
    · exact function_chain_returns_selected_raw
        (minimal_eval_exact.mpr (probe_empty_invocation services enumeration)) "selected"
  · exact empty_is_not_observable

/-- Empty final outputs cannot occur in a lawful collapse enumeration even
though internal minimal continuations can receive the sentinel. -/
theorem collapse_enumeration_omits_final_empty
    {services : Services} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {enumeration : EvalEnumeration dispatch live typing}
    (laws : MinimalEnumerationLaws services dispatch live typing enumeration)
    {space : Space} {atom : Atom} {bindings : Bindings} {results : ResultSet}
    (enumerates : enumeration.minimalResults space atom bindings results)
    (output : Bindings) : (Atom.empty, output) ∉ results := by
  intro member
  exact empty_is_not_observable
    ((laws.support_exact space atom bindings results enumerates _).mp member)

open Spec.Eval.StateAlgebra

/-- A deliberately effectful body consumer records one activation and emits
its selected atom. This is an independent state service, not an evaluator
definition; the ordered traversal specifies its chronology. -/
private def countActivation (selected : ResultPair) (initial : Nat)
    (results : List Atom) (final : Nat) : Prop :=
  results = [selected.1] ∧ final = initial + 1

private theorem count_activations_final
    {selected : ResultSet} {initial final : Nat} {results : List Atom}
    (run : OrderedStateFlatMapRel countActivation selected initial results final) :
    final = initial + selected.length := by
  induction run with
  | nil => simp
  | @cons head tail initial middle final headResults tailResults step _ inductionHypothesis =>
      rcases step with ⟨_, rfl⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using inductionHypothesis

/-- No selected occurrences imply no body effects, independently of the
contents of the held template. This is an enumeration-level statement, not
an assertion that the internal Empty sentinel is no occurrence. -/
theorem no_occurrences_no_body_effect (name : String) (template : Atom)
    (initial final : Nat) (results : List Atom) :
    OrderedStateFlatMapRel countActivation (chainActivations name template [])
      initial results final ↔ results = [] ∧ final = initial :=
  OrderedStateFlatMapRel.nil_iff

/-- Duplicate source occurrences activate an effectful body twice, in
source order, while retaining the independently selected binding frames. -/
theorem duplicate_occurrences_activate_body_twice (selected : ResultPair) :
    OrderedStateFlatMapRel countActivation
      (chainActivations "selected" (.var "selected") [selected, selected])
      0 [selected.1, selected.1] 2 := by
  simp only [chainActivations, List.map_cons, List.map_nil, substituteName]
  apply OrderedStateFlatMapRel.cons (middle := 1)
    (headResults := [selected.1]) (tailResults := [selected.1])
  · exact ⟨rfl, rfl⟩
  · apply OrderedStateFlatMapRel.cons (middle := 2)
      (headResults := [selected.1]) (tailResults := [])
    · exact ⟨rfl, rfl⟩
    · exact .nil 2

/-- Collapsing equal alternatives into one is observationally wrong for an
effectful body even when their returned atoms coincide. -/
theorem duplicate_occurrences_cannot_be_deduplicated (selected : ResultPair)
    (results : List Atom) :
    ¬OrderedStateFlatMapRel countActivation
      (chainActivations "selected" (.var "selected") [selected, selected])
      0 results 1 := by
  intro run
  have final := count_activations_final run
  simp [chainActivations] at final

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
