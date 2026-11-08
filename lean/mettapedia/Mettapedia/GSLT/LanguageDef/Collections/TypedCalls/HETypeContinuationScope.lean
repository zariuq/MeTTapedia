import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding

/-!
# Type-variable retention in the emitted HE call protocol

Rust's chain frame retains variables appearing in both its nested operation
and continuation, in addition to the outer frame's variables. Completed
frames selectively materialize removed names in emitted code. This is not
the freshness-avoidance scope and is not a read of every bound variable.

The control constructors below preserve the actual function/call-native and
chain/return shapes. Callback payloads remain arbitrary grounded atoms since
only their variable support is relevant here. The private exposure operation
models the closed-resolved part of apply_and_retain's marked payload action;
unresolved private aliases and retained-record mutation need their separate
projection law. The source binding witnesses are independently earned.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypeContinuationScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

def nativeCall (name : String) (callback : GroundedValue) (args : List Atom) : Atom :=
  .expression [.symbol "function", .expression [.symbol "call-native", .symbol name, .grounded callback, .expression args]]

def functionRegion (callback : GroundedValue) (expression functionType expected space : Atom) : Atom :=
  nativeCall "interpret_function" callback [expression, functionType, expected, space]

def returnDemand (range : Atom) : Atom :=
  if range = Atom.expressionType then Atom.undefinedType else range

def continuation (callback : GroundedValue) (reduced result : String) (range space : Atom) : Atom :=
  .expression [.symbol "chain", nativeCall "metta_call" callback [.var reduced, returnDemand range, space],
    .var result, .expression [.symbol "return", .var result]]

def kept (outer : List String) (nested template : Atom) : List String :=
  outer ++ (TypeSubst.typeVars nested).filter (fun name => name ∈ TypeSubst.typeVars template)

theorem kept_mem (outer : List String) (nested template : Atom) (name : String) :
    name ∈ kept outer nested template ↔
      name ∈ outer ∨ name ∈ TypeSubst.typeVars nested ∧ name ∈ TypeSubst.typeVars template := by
  simp [kept]

theorem returnDemand_vars (range : Atom) : TypeSubst.typeVars (returnDemand range) = TypeSubst.typeVars range := by
  unfold returnDemand
  split
  next same => subst range; rfl
  next => rfl

/-- For a freshly scoped function-type name, the emitted chain itself
derives retention from its range occurrence; no range-retention oracle is
assumed. Space support and the generated continuation names are explicit. -/
theorem type_name_kept_iff_range (outer : List String) (functionCallback returnCallback : GroundedValue)
    (expression functionType expected range space : Atom) (reduced result name : String)
    (old : name ∉ outer) (inType : name ∈ TypeSubst.typeVars functionType)
    (notReduced : name ≠ reduced) (notResult : name ≠ result)
    (notSpace : name ∉ TypeSubst.typeVars space) :
    name ∈ kept outer (functionRegion functionCallback expression functionType expected space)
      (continuation returnCallback reduced result range space) ↔ name ∈ TypeSubst.typeVars range := by
  have nested : name ∈ TypeSubst.typeVars (functionRegion functionCallback expression functionType expected space) := by
    simp [functionRegion, nativeCall, TypeSubst.typeVars, TypeSubst.typeVarsList, inType]
  rw [kept_mem]
  simp [old, nested, continuation, nativeCall, TypeSubst.typeVars, TypeSubst.typeVarsList,
    returnDemand_vars, notReduced, notResult, notSpace]

/-- Variable replacement preserves the emitted payload's existing marks,
as the direct iterator substitution of apply_and_retain does. Its use below
is restricted to an actually resolved closed type instance. -/
def expose (retained : List String) (frame : Frame) (payload : Entry.Value) : Entry.Value :=
  Entry.Value.substitute .preserve
    (fun name => if name ∈ retained then .var name else frame.read Policy.ready (.var name)) payload

theorem expose_kept (retained : List String) (frame : Frame) (name : String) (present : name ∈ retained) :
    expose retained frame (.var name) = .var name := by simp [expose, Entry.Value.substitute, present]

theorem expose_removed (retained : List String) (frame : Frame) (name : String) (absent : name ∉ retained) :
    expose retained frame (.var name) = frame.read Policy.ready (.var name) := by
  simp [expose, Entry.Value.substitute, absent]

theorem exposed_payload_keeps_parent_mark (retained : List String) (frame : Frame)
    (status : Entry.Status) (fields : List Entry.Value) :
    (expose retained frame (.expression status fields)).status = status := by
  simp [expose, Entry.Value.substitute, Entry.Value.rebuildStatus, Entry.Value.status]

/-- The bound metatype instance is created by the actual source matching
and certified-frame construction, rather than asserted as a frame equality. -/
theorem expression_instance (policy : Policy) (name : String) :
    ∃ frame : Frame,
      frame.bindings = Bindings.empty.assign name Atom.expressionType ∧
      Frame.TypeRenewRel policy (.var name) Atom.expressionType Frame.empty frame ∧
      ∀ readingPolicy : Policy, frame.read readingPolicy (.var name) = .symbol "Expression" := by
  have source := TypeMatchRel.expected_variable_symbol name "Expression" Bindings.empty
    (by decide) (by decide) (by simp [Bindings.classValues, Bindings.empty, Bindings.lookup])
  have model : ∃ valuation, TypeBindingSatisfied valuation (Bindings.empty.assign name Atom.expressionType) := by
    simpa only [Frame.empty, HEFreshRangeFrame.assign_eq_extend Bindings.empty name Atom.expressionType
      (by simp [specBindingVars, Bindings.empty])] using
      HEFreshRangeFrame.extended_model Frame.empty name Atom.expressionType rfl
        (by simp [Frame.empty, specBindingVars, Bindings.empty])
  have matched : policy.matching.Rel (.var name) Atom.expressionType Frame.empty.bindings
      (Bindings.empty.assign name Atom.expressionType) := by
    cases policy.matching with
    | raw => exact source
    | finite => exact ⟨source, model⟩
  obtain ⟨frame, bindings, renewed⟩ := Frame.TypeRenewRel.of_modelled_match Frame.empty matched model
  refine ⟨frame, bindings, renewed, ?_⟩
  intro readingPolicy
  apply HEFreshRangeFrame.symbol_of_erase
  apply HEFreshRangeFrame.forced_range_read frame Bindings.empty name Atom.expressionType rfl
  rw [bindings]
  exact HEFreshRangeFrame.assign_eq_extend Bindings.empty name Atom.expressionType
    (by simp [specBindingVars, Bindings.empty])

def pending : Atom := .expression [.symbol "pending"]

theorem raw_variable_interprets (name : String) : Entry.Rel .reuse .active pending (.var name) .interpret := by
  exact .expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (by simp [Atom.atomType, Atom.expressionType, Atom.variableType]) (Or.inr rfl)

theorem exposed_expression_holds : Entry.Rel .reuse .active pending Atom.expressionType .deliver := by
  exact .pass (by simp [pending, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (.expression [.symbol "pending"]) (Or.inr (Or.inl rfl))

/-- Equal resolved instances do not determine the next demand action: the
runtime-derived retained names determine what syntax was actually emitted. -/
theorem retained_and_private_demands_differ (policy : Policy) (name : String) :
    ∃ frame : Frame,
      Frame.TypeRenewRel policy (.var name) Atom.expressionType Frame.empty frame ∧
      frame.read Policy.ready (.var name) = .symbol "Expression" ∧
      expose [name] frame (.var name) = .var name ∧
      expose [] frame (.var name) = .symbol "Expression" ∧
      Entry.Rel .reuse .active pending (expose [name] frame (.var name)).erase .interpret ∧
      Entry.Rel .reuse .active pending (expose [] frame (.var name)).erase .deliver := by
  obtain ⟨frame, _, renewed, read⟩ := expression_instance policy name
  have kept := expose_kept [name] frame name (by simp)
  have dropped : expose [] frame (.var name) = .symbol "Expression" := by
    rw [expose_removed [] frame name (by simp), read]
  refine ⟨frame, renewed, read Policy.ready, kept, dropped, ?_, ?_⟩
  · simpa only [kept, Entry.Value.erase] using raw_variable_interprets name
  · simpa only [dropped, Entry.Value.erase, Atom.expressionType] using exposed_expression_holds

namespace Controls

def sharedType : Atom := .expression [.symbol "->", .var "t", .var "t"]
def privateType : Atom := .expression [.symbol "->", .var "t", .var "t", .symbol "R"]

theorem shared_kept_private_materialized (functionCallback returnCallback : GroundedValue) :
    "t" ∈ kept [] (functionRegion functionCallback (.symbol "closed-call") sharedType Atom.undefinedType (.symbol "space"))
      (continuation returnCallback "reduced" "result" (.var "t") (.symbol "space")) ∧
    "t" ∉ kept [] (functionRegion functionCallback (.symbol "closed-call") privateType Atom.undefinedType (.symbol "space"))
      (continuation returnCallback "reduced" "result" (.symbol "R") (.symbol "space")) := by
  constructor <;> simp [kept, functionRegion, continuation, nativeCall, returnDemand,
    sharedType, privateType, TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.expressionType]

theorem return_rewrite_does_not_remove_a_type_variable : returnDemand (.var "t") = .var "t" := rfl

/-- The same independently obtained type instance yields the two observed
demands under the retained sets computed from the actual control shapes. -/
theorem actual_control_scopes_choose_the_demands (policy : Policy)
    (functionCallback returnCallback : GroundedValue) :
    ∃ frame : Frame,
      Frame.TypeRenewRel policy (.var "t") Atom.expressionType Frame.empty frame ∧
      expose (kept []
        (functionRegion functionCallback (.symbol "closed-call") sharedType Atom.undefinedType (.symbol "space"))
        (continuation returnCallback "reduced" "result" (.var "t") (.symbol "space"))) frame (.var "t") = .var "t" ∧
      expose (kept []
        (functionRegion functionCallback (.symbol "closed-call") privateType Atom.undefinedType (.symbol "space"))
        (continuation returnCallback "reduced" "result" (.symbol "R") (.symbol "space"))) frame (.var "t") = .symbol "Expression" := by
  obtain ⟨frame, _, renewed, read⟩ := expression_instance policy "t"
  have scopes := shared_kept_private_materialized functionCallback returnCallback
  refine ⟨frame, renewed, expose_kept _ frame "t" scopes.1, ?_⟩
  rw [expose_removed _ frame "t" scopes.2, read]

/-- Fresh typing queries must avoid the bound name even when the emitted
continuation does not retain it. These two scopes cannot be substituted for
one another. -/
theorem freshness_avoidance_is_not_retention (policy : Policy)
    (functionCallback returnCallback : GroundedValue) :
    ∃ frame : Frame,
      "t" ∈ invocationTypeScope [] [] (.symbol "closed-call") Atom.undefinedType frame.bindings ∧
      "t" ∉ kept []
        (functionRegion functionCallback (.symbol "closed-call") privateType Atom.undefinedType (.symbol "space"))
        (continuation returnCallback "reduced" "result" (.symbol "R") (.symbol "space")) := by
  obtain ⟨frame, bindings, _, _⟩ := expression_instance policy "t"
  refine ⟨frame, ?_, (shared_kept_private_materialized functionCallback returnCallback).2⟩
  simp [invocationTypeScope, bindings, specBindingVars, Bindings.empty, Bindings.assign,
    TypeSubst.typeVars, TypeSubst.typeVarsList, Bindings.isBound, Bindings.lookup]

/-- Name retention is not closure under the alias class. A removed alias
with a resolved value is materialized even when another class name stays. -/
theorem retained_name_does_not_keep_every_alias (policy : Policy) :
    ∃ frame : Frame,
      ("kept", "private") ∈ frame.bindings.equalities ∧
      frame.read Policy.ready (.var "kept") = .symbol "Expression" ∧
      frame.read Policy.ready (.var "private") = .symbol "Expression" ∧
      expose ["kept"] frame (.var "kept") = .var "kept" ∧
      expose ["kept"] frame (.var "private") = .symbol "Expression" := by
  obtain ⟨before, bindings, _, _⟩ := expression_instance policy "kept"
  have isolated : "kept" ∉ before.bindings.eqVarsInOrder := by
    rw [bindings]
    simp [Bindings.empty, Bindings.assign, Bindings.eqVarsInOrder]
  have assigned : before.bindings.lookup "kept" = some Atom.expressionType := by
    rw [bindings]
    simp [Bindings.empty, Bindings.assign, Bindings.lookup, Bindings.isBound]
  have fresh : "private" ∉ specBindingVars before.bindings := by
    rw [bindings]
    simp [specBindingVars, Bindings.empty, Bindings.assign, TypeSubst.typeVars, Atom.expressionType]
  obtain ⟨frame, aliases, _, read⟩ := HEFreshRangeAlias.arrow_alias_frame policy before []
    "kept" "private" Atom.expressionType rfl isolated assigned fresh
  have first := HEFreshRangeFrame.symbol_of_erase _ "Expression" (read Policy.ready).1
  have second := HEFreshRangeFrame.symbol_of_erase _ "Expression" (read Policy.ready).2
  refine ⟨frame, ?_, first, second, expose_kept _ frame "kept" (by simp), ?_⟩
  · rw [aliases]
    simp [Bindings.addEquality]
  · rw [expose_removed _ frame "private" (by simp), second]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypeContinuationScope
