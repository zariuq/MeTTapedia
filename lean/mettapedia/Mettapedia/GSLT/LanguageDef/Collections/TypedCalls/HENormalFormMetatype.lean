import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormWildcard
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadApplications

/-!
# Inference's substituted metatype cut does not establish source applicability

A shared formal becomes Expression after its first operand. The structural
reader then accepts a later expression by its kind. The source applicability
protocol still examines the authored variable formal and asks for that
operand's inferred type, which is CompletionDataType, not Expression.
Both variants have no expression-subject rows and no Undefined type.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormMetatype

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open HEDemandedConstructorInferred (world)
open HEDemandedCurrentReads (ops)

def dataValue : Atom := .expression [.symbol "CompletionData", .grounded (.int 7)]
def firstValue (constructor : Bool) : Atom :=
  if constructor then .expression [.symbol "CompletionExprBox", .grounded (.int 1)]
  else .symbol "CompletionExpressionWitness"
def call (constructor : Bool) : Atom := .expression [.symbol "CompletionCoupled", firstValue constructor, dataValue]

def signature : Atom := .expression [.symbol "->", .var "t", .var "t", .symbol "CompletionResult"]

def space (constructor : Bool) : Space := Space.ofList
  [(if constructor then
      .expression [.symbol ":", .symbol "CompletionExprBox", .expression [.symbol "->", .symbol "Number", Atom.expressionType]]
    else .expression [.symbol ":", .symbol "CompletionExpressionWitness", Atom.expressionType]),
   .expression [.symbol ":", .symbol "CompletionData", .expression [.symbol "->", .symbol "Number", .symbol "CompletionDataType"]],
   .expression [.symbol ":", .symbol "CompletionCoupled", signature]]

def observed (constructor : Bool) (bindings : Bindings) (subject expected : Atom) : Option (List Atom) :=
  NativeTypeRecursiveDriver.publishTypes
    (NativeTypeScopedReads.evaluate HEDemandedCurrentReads.ops
      (HEDemandedConstructorEdge.packet (space constructor)) HEDemandedConstructorInferred.world 8
      (.infer true subject)
      ⟨Spec.Eval.invocationTypeScope [] [] subject expected bindings, 0⟩).1

/-- This total adapter is used only at the two reached questions proved
completed below. Missing observations are not used as evidence of rejection. -/
def observedLookup (constructor : Bool) : TypeLookup :=
  fun bindings subject expected => (observed constructor bindings subject expected).getD []

def expressionBinding : Bindings := Bindings.empty.assign "t" Atom.expressionType

theorem declarations_eq (constructor : Bool) (subject : Atom) :
    rawDeclarations (HEDemandedConstructorEdge.packet (space constructor)) world subject =
      getAnnotatedTypes (space constructor) subject := by
  have observed : RetainedTypePayloads.observeList world (space constructor).atoms = (space constructor).atoms :=
    TypeDependencyAdmission.observeList_resourceFree world _ (by cases constructor <;> decide +kernel)
  simp only [rawDeclarations, HEDemandedConstructorEdge.packet, TypeDependencyAdmission.observedSpace,
    observed, show RetainedTypePayloads.observeList world [] = [] from rfl]
  cases subject <;> rfl

theorem no_subtypes (constructor : Bool) :
    ∀ row ∈ (HEDemandedConstructorEdge.packet (space constructor)).rows,
      ScopedSubtypeReads.possibleRow row = false := by
  cases constructor <;>
    simp [HEDemandedConstructorEdge.packet, space, Space.ofList, ScopedSubtypeReads.possibleRow]

theorem closure_finished (constructor : Bool) (seeds : List Atom) (supply : Supply) :
    (ScopedSubtypeReads.completeTypes world (space constructor).atoms "subtype"
      (fun left right => left == right) 4 seeds supply).1 = some seeds :=
  HERangeTypeReadPrimitives.no_edge_closure world (space constructor).atoms (no_subtypes constructor)
    "subtype" (fun left right => left == right) 3 seeds supply

def readSupply (constructor : Bool) (depth : Nat) (call : Call) (supply : Supply) : Supply :=
  (NativeTypeScopedReads.evaluate ops (HEDemandedConstructorEdge.packet (space constructor)) world depth call supply).2

theorem operator_closed (constructor : Bool) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations (HEDemandedConstructorEdge.packet (space constructor)) world (.symbol name) = [type])
    (closed : atomVariables type = []) :
    NativeTypeScopedReads.evaluate ops (HEDemandedConstructorEdge.packet (space constructor)) world (depth + 1)
      (.operatorRows (.symbol name)) supply =
      (some (.types [type]), readSupply constructor (depth + 1) (.operatorRows (.symbol name)) supply) := by
  apply Prod.ext
  · simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
      NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
      Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList,
      HERangeTypeReadApplications.fresh_closed _ _ closed, NativeTypeRecursiveDriver.completed]
  · rfl

theorem symbol_closed (constructor : Bool) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations (HEDemandedConstructorEdge.packet (space constructor)) world (.symbol name) = [type])
    (closed : atomVariables type = []) :
    NativeTypeScopedReads.evaluate ops (HEDemandedConstructorEdge.packet (space constructor)) world (depth + 1)
      (.infer true (.symbol name)) supply =
      (some (.types [type]), readSupply constructor (depth + 1) (.infer true (.symbol name)) supply) := by
  apply Prod.ext
  · have closure (seeds : List Atom) (current : Supply) :
        (ScopedSubtypeReads.completeTypes world
          (HEDemandedConstructorEdge.packet (space constructor)).rows
          (HEDemandedConstructorEdge.packet (space constructor)).subtypeFresh
          (HEDemandedConstructorEdge.packet (space constructor)).alpha
          (HEDemandedConstructorEdge.packet (space constructor)).subtypeBudget seeds current).1 = some seeds :=
      closure_finished constructor seeds current
    simp only [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
      NativeTypeCallGraph.finishTypes, NativeTypeCallGraph.closeTypes,
      Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
      NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList,
      HERangeTypeReadApplications.fresh_closed _ _ closed, List.isEmpty_cons,
      Bool.false_eq_true, ite_false, ite_true, closure, Option.map_some,
      NativeTypeRecursiveDriver.completed]
  · rfl

theorem number_constructor (constructor : Bool) (depth : Nat) (supply : Supply)
    (name rangeName : String) (number : Int)
    (declared : rawDeclarations (HEDemandedConstructorEdge.packet (space constructor)) world (.symbol name) =
      [.expression [.symbol "->", .symbol "Number", .symbol rangeName]])
    (noOwn : rawDeclarations (HEDemandedConstructorEdge.packet (space constructor)) world
      (.expression [.symbol name, .grounded (.int number)]) = []) :
    NativeTypeScopedReads.evaluate ops (HEDemandedConstructorEdge.packet (space constructor)) world (depth + 2)
      (.infer true (.expression [.symbol name, .grounded (.int number)])) supply =
      (some (.types [.symbol rangeName]),
        readSupply constructor (depth + 2) (.infer true (.expression [.symbol name, .grounded (.int number)])) supply) := by
  apply Prod.ext
  · have classifyReply (current : Supply) :
        NativeTypeScopedReads.primitive (HEDemandedConstructorEdge.packet (space constructor)) world current
          (.classify (.symbol name) [.grounded (.int number)]) = (some (.class_ .ordinary), current) := by
      simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, nativeClassify, NativeTypeScopedReads.retain]
    have annotationReply (current : Supply) :
        NativeTypeScopedReads.primitive (HEDemandedConstructorEdge.packet (space constructor)) world current
          (.annotations (.expression [.symbol name, .grounded (.int number)])) = (some (.types []), current) := by
      simp [NativeTypeScopedReads.primitive, noOwn, TypeReadSupply.freshList, TypeReadSupply.remember,
        atomListVariables, atomVariables]
    have headReply (current : Supply) := operator_closed constructor depth current name _ declared rfl
    have childReply (current : Supply) := HERangeTypeReadPrimitives.number_read ops
      (HEDemandedConstructorEdge.packet (space constructor)) world depth number current
    have kindReply (current : Supply) :
        NativeTypeScopedReads.primitive (HEDemandedConstructorEdge.packet (space constructor)) world current
          (.kind (.grounded (.int number))) = (some (.kind Atom.groundedType), current) := by
      simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain, getMetaType]
    have arrow : ops.arrow (.expression [.symbol "->", .symbol "Number", .symbol rangeName]) =
        some ([.symbol "Number"], .symbol rangeName) := rfl
    have initial : ops.initial = Atom.var := rfl
    have metaCheck : ops.metaCheck (ops.apply Atom.var (.symbol "Number")) Atom.groundedType = none := rfl
    have matched : ops.unify Atom.var (.symbol "Number") (ops.apply Atom.var (.symbol "Number")) = some Atom.var :=
      HERangeTypeReadApplications.number_match world
    have normalized : ops.normalize (ops.apply Atom.var (.symbol rangeName)) = .symbol rangeName := rfl
    rw [NativeTypeScopedReads.evaluate]
    simp only [NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.ordinary,
      NativeTypeCallGraph.typesRead, NativeTypeCallGraph.finishTypes, NativeTypeCallGraph.mapTypes,
      NativeTypeCallGraph.liftViews, NativeTypeCallGraph.viewQuestion,
      NativeTypeDemand.rowsPlan, NativeTypeDemand.argsPlan, NativeTypeDemand.typesRead,
      Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
      Mettapedia.Machines.ReadOnlyQuery.bind, Mettapedia.Machines.ReadOnlyQuery.map,
      classifyReply, annotationReply, headReply, childReply, kindReply, arrow, initial, metaCheck, matched, normalized,
      List.isEmpty_nil, List.any_cons, List.any_nil, Option.isSome_some, Bool.true_or, ite_true,
      StampInference.firstResult, NativeTypeRecursiveDriver.completed, Except.map]
  · rfl

theorem first_query_completed (constructor : Bool) :
    observed constructor Bindings.empty (firstValue constructor) (.var "t") = some [Atom.expressionType] := by
  let supply : Supply := ⟨Spec.Eval.invocationTypeScope [] [] (firstValue constructor) (.var "t") Bindings.empty, 0⟩
  cases constructor
  · have reply := symbol_closed false 7 supply "CompletionExpressionWitness" Atom.expressionType
      (by rw [declarations_eq]; decide +kernel) rfl
    change NativeTypeRecursiveDriver.publishTypes
      (NativeTypeScopedReads.evaluate ops (HEDemandedConstructorEdge.packet (space false)) world 8
        (.infer true (.symbol "CompletionExpressionWitness")) supply).1 = _
    rw [reply]
    rfl
  · have reply := number_constructor true 6 supply "CompletionExprBox" "Expression" 1
      (by rw [declarations_eq]; decide +kernel) (by rw [declarations_eq]; decide +kernel)
    change NativeTypeRecursiveDriver.publishTypes
      (NativeTypeScopedReads.evaluate ops (HEDemandedConstructorEdge.packet (space true)) world 8
        (.infer true (.expression [.symbol "CompletionExprBox", .grounded (.int 1)])) supply).1 = _
    rw [reply]
    rfl

theorem second_query_completed (constructor : Bool) :
    observed constructor expressionBinding dataValue (.var "t") = some [.symbol "CompletionDataType"] := by
  let supply : Supply := ⟨Spec.Eval.invocationTypeScope [] [] dataValue (.var "t") expressionBinding, 0⟩
  have reply := number_constructor constructor 6 supply "CompletionData" "CompletionDataType" 7
    (by rw [declarations_eq]; cases constructor <;> decide +kernel)
    (by rw [declarations_eq]; cases constructor <;> decide +kernel)
  change NativeTypeRecursiveDriver.publishTypes
    (NativeTypeScopedReads.evaluate ops (HEDemandedConstructorEdge.packet (space constructor)) world 8
      (.infer true (.expression [.symbol "CompletionData", .grounded (.int 7)])) supply).1 = _
  rw [reply]
  rfl

theorem first_source_match :
    matchTypes (.var "t") Atom.expressionType Bindings.empty 23 = [expressionBinding] := by decide +kernel

theorem second_source_match :
    matchTypes (.var "t") (.symbol "CompletionDataType") expressionBinding 23 = [] := by decide +kernel

/-- The actual authored-formal applicability checker rejects after two
completed inferred reads; it is not the annotation-only legacy evaluator. -/
theorem applicability_rejects (constructor : Bool) :
    (checkIfFunctionTypeIsApplicable (call constructor)
      signature Atom.undefinedType
      (space constructor) Bindings.empty 24 (observedLookup constructor)).isLeft = true := by
  simp [checkIfFunctionTypeIsApplicable, call, signature, getFunctionArgTypes,
    checkIfFunctionTypeIsApplicable.checkArgLoop, checkArgumentType, observedLookup,
    first_query_completed, second_query_completed, first_source_match, second_source_match]

def expressionState : TypeScopeMatcher.State :=
  (TypeScopeMatcher.unify world Atom.var Atom.expressionType (.var "t")).getD Atom.var

theorem expression_state_selected :
    TypeScopeMatcher.unify world Atom.var Atom.expressionType (.var "t") = some expressionState := by
  unfold expressionState
  cbv

theorem expression_state_value : expressionState "t" = Atom.expressionType := by cbv

/-- The completed local reader port uses the actual stored head declaration
and the completed first-operand query. Tuple alternatives and the later
operand's inferred query are not reached by this admitted arrow path. -/
def localReads (constructor : Bool) : NativeTypeViews.Reads Atom Atom Atom where
  classify _ _ := .ordinary
  annotations head args := getAnnotatedTypes (space constructor) (.expression (head :: args))
  headRows head := getAnnotatedTypes (space constructor) head
  tupleHead _ := []
  kind := getMetaType
  inferred subject := observedLookup constructor Bindings.empty subject (.var "t")
  tuplePart _ := []

def localInference (constructor : Bool) : List Atom :=
  NativeTypeViews.sourceNode ops (localReads constructor) false (.symbol "CompletionCoupled")
    [firstValue constructor, dataValue]

theorem local_inference_accepts (constructor : Bool) :
    localInference constructor = [.symbol "CompletionResult"] := by
  have headRows : (localReads constructor).headRows (.symbol "CompletionCoupled") = [signature] := by
    cases constructor <;> decide +kernel
  have inferred : (localReads constructor).inferred (firstValue constructor) = [Atom.expressionType] := by
    change (observed constructor Bindings.empty (firstValue constructor) (.var "t")).getD [] = _
    rw [first_query_completed]
    rfl
  have arrow : ops.arrow signature = some ([.var "t", .var "t"], .symbol "CompletionResult") := rfl
  have initial : ops.initial = Atom.var := rfl
  have firstMeta : ops.metaCheck (ops.apply Atom.var (.var "t"))
      ((localReads constructor).kind (firstValue constructor)) = none := rfl
  have selected : ops.unify Atom.var Atom.expressionType (ops.apply Atom.var (.var "t")) =
      some expressionState := expression_state_selected
  have secondMeta : ops.metaCheck (ops.apply expressionState (.var "t"))
      ((localReads constructor).kind dataValue) = some true := by
    change TypeScopeMatcher.metaCheckAtom (expressionState "t") Atom.expressionType = some true
    rw [expression_state_value]
    rfl
  have normalized : ops.normalize (ops.apply expressionState (.symbol "CompletionResult")) =
      .symbol "CompletionResult" := rfl
  simp only [localInference, NativeTypeViews.sourceNode,
    show (localReads constructor).classify (.symbol "CompletionCoupled") [firstValue constructor, dataValue] = .ordinary from rfl,
    Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, headRows,
    List.any_cons, List.any_nil, arrow, Option.isSome_some, Bool.true_or,
    NativeTypeViews.sourceRows, NativeTypeViews.sourceArgs, initial,
    firstMeta, inferred, StampInference.firstResult, selected, secondMeta, normalized]

theorem original_and_instantiated_kind_cuts_differ :
    TypeScopeMatcher.metaCheckAtom (.var "t") Atom.expressionType = none ∧
    TypeScopeMatcher.metaCheckAtom Atom.expressionType Atom.expressionType = some true := by decide +kernel

theorem local_inference_does_not_certify_applicability (constructor : Bool) :
    localInference constructor = [.symbol "CompletionResult"] ∧
    (checkIfFunctionTypeIsApplicable (call constructor) signature Atom.undefinedType
      (space constructor) Bindings.empty 24 (observedLookup constructor)).isLeft = true :=
  ⟨local_inference_accepts constructor, applicability_rejects constructor⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormMetatype
