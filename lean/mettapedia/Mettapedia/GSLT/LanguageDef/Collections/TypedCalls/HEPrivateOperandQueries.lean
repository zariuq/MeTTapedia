import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormMetatype

/-!
# Completed inferred reads for active private-formal operands

The second ExprBox contains an unevaluated nullary program, not a numeric
literal. Its query follows the actual recursive type reader to that child's
declared result without evaluating its body. Every closed declaration read
still advances the actual occurrence supply.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandQueries

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open HEDemandedConstructorInferred (world)
open HEDemandedCurrentReads (ops)

def signature (name : String) : Atom :=
  .expression [.symbol "->", .var name, .var name, .symbol "CompletionResult"]

def space : Space := Space.ofList
  [.expression [.symbol ":", .symbol "CompletionExprBox", .expression [.symbol "->", .symbol "Number", Atom.expressionType]],
   .expression [.symbol ":", .symbol "completion-number", .expression [.symbol "->", .symbol "Number"]],
   .expression [.symbol "=", .expression [.symbol "completion-number"], .grounded (.int 7)],
   .expression [.symbol ":", .symbol "CompletionCoupled", signature "t"],
   .expression [.symbol ":", .symbol "CompletionIdentity", .expression [.symbol "->", .var "t", .var "t"]],
   .expression [.symbol "=", .expression [.symbol "CompletionIdentity", .var "x"], .var "x"]]

abbrev source := HEDemandedConstructorEdge.packet space

def firstOperand : Atom := .expression [.symbol "CompletionExprBox", .grounded (.int 1)]
def numericChild : Atom := .expression [.symbol "completion-number"]
def activeOperand : Atom := .expression [.symbol "CompletionExprBox", numericChild]

def advanced (supply : Supply) (reads : Nat) : Supply := ⟨supply.used, supply.next + reads⟩

theorem advanced_add (supply : Supply) (first second : Nat) :
    advanced (advanced supply first) second = advanced supply (first + second) := by
  simp [advanced, Nat.add_assoc]

theorem declarations_eq (subject : Atom) : rawDeclarations source world subject = getAnnotatedTypes space subject := by
  have observed : RetainedTypePayloads.observeList world space.atoms = space.atoms :=
    TypeDependencyAdmission.observeList_resourceFree world _ (by decide +kernel)
  simp only [rawDeclarations, HEDemandedConstructorEdge.packet, TypeDependencyAdmission.observedSpace,
    observed, show RetainedTypePayloads.observeList world [] = [] from rfl]
  cases subject <;> rfl

theorem operator_closed (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) (closed : atomVariables type = []) :
    NativeTypeScopedReads.evaluate ops source world (depth + 1) (.operatorRows (.symbol name)) supply =
      (some (.types [type]), advanced supply 1) := by
  simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
    Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList,
    HERangeTypeReadApplications.fresh_closed _ _ closed, NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed,
    TypeReadSupply.remember, atomListVariables, atomVariables, closed, advanced]

theorem annotation_empty (supply : Supply) (subject : Atom) (closed : atomVariables subject = [])
    (absent : rawDeclarations source world subject = []) :
    NativeTypeScopedReads.primitive source world supply (.annotations subject) = (some (.types []), supply) := by
  simp [NativeTypeScopedReads.primitive, absent, TypeReadSupply.freshList, TypeReadSupply.remember,
    atomListVariables, closed]

theorem nullary_number (depth : Nat) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops source world (depth + 2) (.infer true numericChild) supply =
      (some (.types [.symbol "Number"]), advanced supply 1) := by
  have classified (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.classify (.symbol "completion-number") []) = (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, nativeClassify, NativeTypeScopedReads.retain]
  have noOwn (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.annotations (.expression [.symbol "completion-number"])) = (some (.types []), current) :=
    annotation_empty current numericChild rfl (by rw [declarations_eq]; decide +kernel)
  have headReply (current : Supply) := operator_closed depth current "completion-number"
    (.expression [.symbol "->", .symbol "Number"]) (by rw [declarations_eq]; decide +kernel) rfl
  have arrow : ops.arrow (.expression [.symbol "->", .symbol "Number"]) = some ([], .symbol "Number") := rfl
  have initial : ops.initial = Atom.var := rfl
  have normalized : ops.normalize (ops.apply Atom.var (.symbol "Number")) = .symbol "Number" := rfl
  rw [NativeTypeScopedReads.evaluate]
  simp only [numericChild, NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.ordinary,
    NativeTypeCallGraph.typesRead, NativeTypeCallGraph.finishTypes, NativeTypeCallGraph.mapTypes,
    NativeTypeCallGraph.liftViews, NativeTypeDemand.rowsPlan, NativeTypeDemand.argsPlan,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    Mettapedia.Machines.ReadOnlyQuery.bind, Mettapedia.Machines.ReadOnlyQuery.map,
    classified, noOwn, headReply, arrow, initial, normalized, List.isEmpty_nil,
    List.any_cons, List.any_nil, Option.isSome_some, Bool.true_or, ite_true,
    NativeTypeRecursiveDriver.completed, Except.map]
  simp [NativeTypeScopedReads.retain, TypeReadSupply.remember, atomListVariables, atomVariables]

/-- One constructor reader can reuse a completed child read with its real
advanced supply. This is a recursive type-service join, not a body-run
assumption and not a rewrite from the child's future value. -/
theorem box_of_number_query (depth cost : Nat) (supply : Supply) (child : Atom)
    (closedChild : atomVariables child = [])
    (noOwn : rawDeclarations source world (.expression [.symbol "CompletionExprBox", child]) = [])
    (childReply : ∀ current, NativeTypeScopedReads.evaluate ops source world (depth + 1)
      (.infer true child) current = (some (.types [.symbol "Number"]), advanced current cost)) :
    NativeTypeScopedReads.evaluate ops source world (depth + 2)
      (.infer true (.expression [.symbol "CompletionExprBox", child])) supply =
      (some (.types [Atom.expressionType]), advanced supply (1 + cost)) := by
  have classified (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.classify (.symbol "CompletionExprBox") [child]) = (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, nativeClassify, NativeTypeScopedReads.retain]
  have annotationReply (current : Supply) := annotation_empty current (.expression [.symbol "CompletionExprBox", child])
    (by simp [atomVariables, atomListVariables, closedChild]) noOwn
  have headReply (current : Supply) := operator_closed depth current "CompletionExprBox"
    (.expression [.symbol "->", .symbol "Number", Atom.expressionType])
    (by rw [declarations_eq]; decide +kernel) rfl
  have kindReply (current : Supply) : NativeTypeScopedReads.primitive source world current (.kind child) =
      (some (.kind (getMetaType child)), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain]
  have arrow : ops.arrow (.expression [.symbol "->", .symbol "Number", Atom.expressionType]) =
      some ([.symbol "Number"], Atom.expressionType) := rfl
  have initial : ops.initial = Atom.var := rfl
  have metaCheck : ops.metaCheck (ops.apply Atom.var (.symbol "Number")) (getMetaType child) = none := rfl
  have matched : ops.unify Atom.var (.symbol "Number") (ops.apply Atom.var (.symbol "Number")) = some Atom.var :=
    HERangeTypeReadApplications.number_match world
  have normalized : ops.normalize (ops.apply Atom.var Atom.expressionType) = Atom.expressionType := rfl
  rw [NativeTypeScopedReads.evaluate]
  simp only [NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.ordinary,
    NativeTypeCallGraph.typesRead, NativeTypeCallGraph.finishTypes, NativeTypeCallGraph.mapTypes,
    NativeTypeCallGraph.liftViews, NativeTypeCallGraph.viewQuestion,
    NativeTypeDemand.rowsPlan, NativeTypeDemand.argsPlan, NativeTypeDemand.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    Mettapedia.Machines.ReadOnlyQuery.bind, Mettapedia.Machines.ReadOnlyQuery.map,
    classified, annotationReply, headReply, childReply, kindReply, arrow, initial, metaCheck, matched, normalized,
    List.isEmpty_nil, List.any_cons, List.any_nil, Option.isSome_some, Bool.true_or, ite_true,
    StampInference.firstResult, NativeTypeRecursiveDriver.completed, Except.map]
  simp [NativeTypeScopedReads.retain, TypeReadSupply.remember, atomListVariables, atomVariables,
    Atom.expressionType, advanced_add]

theorem first_query (depth : Nat) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops source world (depth + 2) (.infer true firstOperand) supply =
      (some (.types [Atom.expressionType]), advanced supply 1) := by
  simpa only [firstOperand, Nat.add_zero] using
    box_of_number_query depth 0 supply (.grounded (.int 1)) rfl
      (by rw [declarations_eq]; decide +kernel)
      (fun current => by simpa [advanced] using HERangeTypeReadPrimitives.number_read ops source world depth 1 current)

theorem active_query (depth : Nat) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops source world (depth + 3) (.infer true activeOperand) supply =
      (some (.types [Atom.expressionType]), advanced supply 2) := by
  simpa only [activeOperand, Nat.add_assoc] using
    box_of_number_query (depth + 1) 1 supply numericChild rfl
      (by rw [declarations_eq]; decide +kernel) (nullary_number depth)

theorem first_lookup (scope : List String) (before : Frame) (expected : Atom) :
    HEDemandedCurrentReads.lookup scope space before.bindings firstOperand expected [Atom.expressionType] := by
  exact congrArg (fun result => NativeTypeRecursiveDriver.publishTypes result.1)
    (first_query 6 ⟨invocationTypeScope scope [] firstOperand expected before.bindings, 0⟩)

theorem active_lookup (scope : List String) (before : Frame) (expected : Atom) :
    HEDemandedCurrentReads.lookup scope space before.bindings activeOperand expected [Atom.expressionType] := by
  exact congrArg (fun result => NativeTypeRecursiveDriver.publishTypes result.1)
    (active_query 5 ⟨invocationTypeScope scope [] activeOperand expected before.bindings, 0⟩)

theorem no_subtypes : ∀ row ∈ source.rows, ScopedSubtypeReads.possibleRow row = false := by
  simp [source, HEDemandedConstructorEdge.packet, space, Space.ofList, ScopedSubtypeReads.possibleRow,
    signature]

theorem closure_finished (seeds : List Atom) (supply : Supply) :
    (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha source.subtypeBudget seeds supply).1 =
      some seeds :=
  HERangeTypeReadPrimitives.no_edge_closure world source.rows no_subtypes
    source.subtypeFresh source.alpha 3 seeds supply

theorem symbol_read (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) :
    (NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol name)) supply).1 =
      some (.types [(TypeReadSupply.fresh (TypeReadSupply.remember supply [.symbol name]) type).1]) := by
  simp only [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.closeTypes, NativeTypeCallGraph.finishTypes,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList, List.isEmpty_cons,
    Bool.false_eq_true, ite_false, ite_true, closure_finished, Option.map_some, NativeTypeRecursiveDriver.completed]

theorem head_lookup (scope : List String) (before : Frame) (expected : Atom) :
    ∃ name,
      HEDemandedCurrentReads.lookup scope space before.bindings (.symbol "CompletionCoupled") expected [signature name] ∧
      name ∉ invocationTypeScope scope [] (.symbol "CompletionCoupled") expected before.bindings := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.symbol "CompletionCoupled") expected before.bindings, 0⟩
  let prepared := TypeReadSupply.remember supply [Atom.symbol "CompletionCoupled"]
  let name := instanceName prepared.used (atomVariables (signature "t")).eraseDups prepared.next "t"
  have shape : (TypeReadSupply.fresh prepared (signature "t")).1 = signature name := by
    simp [TypeReadSupply.fresh, instantiateTypeSignature, signature, renameAtom, renameAtomList, name]
  have read := symbol_read 7 supply "CompletionCoupled" (signature "t")
    (by rw [declarations_eq]; decide +kernel)
  refine ⟨name, ?_, ?_⟩
  · change NativeTypeRecursiveDriver.publishTypes
      (NativeTypeScopedReads.evaluate ops source world 8 (.infer true (.symbol "CompletionCoupled")) supply).1 = _
    rw [read]
    exact congrArg (fun type => some [type]) shape
  · exact instanceName_not_mem prepared.used (atomVariables (signature "t")).eraseDups prepared.next "t"

namespace Controls

/-- A shallow suspended child query is not a completed empty type list. -/
theorem active_query_requires_recursive_depth (supply : Supply) :
    (NativeTypeScopedReads.evaluate ops source world 0 (.infer true activeOperand) supply).1 = none := rfl

theorem nested_program_is_not_a_number_literal :
    activeOperand ≠ firstOperand := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandQueries
