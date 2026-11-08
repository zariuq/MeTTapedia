import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionTypeReadPrimitives
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicyAgreement

/-! Local application and polymorphic-head reads in the collection source
packet. In particular range remains an undeclared producer: its raw call's
Undefined type is not confused with the Numbers its execution later emits. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionTypeReadApplications

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)
open HECollectionTypeReadPrimitives

theorem current_policy_agrees (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (policy : NativeTypeViews.AnnotationPolicy Atom) (world : ExternalView)
    (depth : Nat) (call : Call) (supply : Supply) :
    NativeTypeScopedReads.evaluate { ops with annotationPolicy := policy } source world depth call supply =
      NativeTypeScopedReads.evaluate ops source world depth call supply :=
  NativeTypePolicyAgreement.evaluate_policy ops policy source world (no_expression_annotations world) depth call supply

theorem binary_numeric_type (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (name returned : String) (depth : Nat) (supply : Supply) (left right : Int)
    (declared : rawDeclarations source world (.symbol name) =
      [CompletedDelivery.arrowType [.symbol "Number", .symbol "Number"] (.symbol returned)])
    (ordinary : nativeClassify (.symbol name) [.grounded (.int left), .grounded (.int right)] = .ordinary) :
    (NativeTypeScopedReads.evaluate (HERangeTypeReadApplications.ops world active primitive unobservedClosure) source world (depth + 2)
      (.infer true (.expression [.symbol name, .grounded (.int left), .grounded (.int right)])) supply).1 =
      some (.types [.symbol returned]) := by
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  let arrowType := CompletedDelivery.arrowType [Atom.symbol "Number", .symbol "Number"] (.symbol returned)
  have arrowClosed : atomVariables arrowType = [] := rfl
  have classifyReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.classify (.symbol name) [.grounded (.int left), .grounded (.int right)]) =
      (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, ordinary, NativeTypeScopedReads.retain]
  have annotationReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.annotations (.expression [.symbol name, .grounded (.int left), .grounded (.int right)])) =
      (some (.types []), current) := annotation_empty world current _ rfl (no_expression_annotations world _)
  have headReply (current : Supply) := operator_singleton currentOps world depth current name arrowType declared arrowClosed
  have childReply (current : Supply) (value : Int) := HERangeTypeReadPrimitives.number_read currentOps source world depth value current
  have kindReply (current : Supply) (value : Int) : NativeTypeScopedReads.primitive source world current
      (.kind (.grounded (.int value))) = (some (.kind Atom.groundedType), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain, getMetaType]
  have arrow : currentOps.arrow arrowType = some ([.symbol "Number", .symbol "Number"], .symbol returned) := rfl
  have initial : currentOps.initial = Atom.var := rfl
  have metaChoice (state : TypeScopeMatcher.State) : currentOps.metaCheck (currentOps.apply state (.symbol "Number")) Atom.groundedType = none := rfl
  have matching : currentOps.unify Atom.var (.symbol "Number") (currentOps.apply Atom.var (.symbol "Number")) = some Atom.var :=
    HERangeTypeReadApplications.number_match world
  have normalized : currentOps.normalize (currentOps.apply Atom.var (.symbol returned)) = .symbol returned := rfl
  change (NativeTypeScopedReads.evaluate currentOps source world (depth + 2)
    (.infer true (.expression [.symbol name, .grounded (.int left), .grounded (.int right)])) supply).1 = _
  rw [NativeTypeScopedReads.evaluate]
  simp only [NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.ordinary,
    NativeTypeCallGraph.typesRead, NativeTypeCallGraph.finishTypes, NativeTypeCallGraph.mapTypes,
    NativeTypeCallGraph.liftViews, NativeTypeCallGraph.viewQuestion,
    NativeTypeDemand.rowsPlan, NativeTypeDemand.argsPlan, NativeTypeDemand.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    Mettapedia.Machines.ReadOnlyQuery.bind, Mettapedia.Machines.ReadOnlyQuery.map,
    classifyReply, annotationReply, headReply, childReply, kindReply, arrow, initial, metaChoice, matching, normalized,
    List.isEmpty_nil, List.any_cons, List.any_nil, Option.isSome_some, Bool.true_or, ite_true,
    StampInference.firstResult, NativeTypeRecursiveDriver.completed, Except.map]

theorem comparison_type (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (depth : Nat) (supply : Supply) (left right : Int) :
    (NativeTypeScopedReads.evaluate (HERangeTypeReadApplications.ops world active primitive unobservedClosure) source world (depth + 2)
      (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 =
      some (.types [.symbol "Bool"]) := by
  apply binary_numeric_type
  · rw [declarations_eq]; rfl
  · rfl

theorem if_head_type (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) :
    ∃ name, (NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol "if")) supply).1 =
      some (.types [(HEIfSourceSelection.signature name).functionType]) ∧ name ∉ supply.used := by
  let prepared := TypeReadSupply.remember supply [Atom.symbol "if"]
  let original := (HEIfSourceSelection.signature "t").functionType
  let name := instanceName prepared.used (atomVariables original).eraseDups prepared.next "t"
  have declared : rawDeclarations source world (.symbol "if") = [original] := by rw [declarations_eq]; rfl
  have shape : (TypeReadSupply.fresh prepared original).1 = (HEIfSourceSelection.signature name).functionType := by
    simp [TypeReadSupply.fresh, instantiateTypeSignature, original, HEIfSourceSelection.signature,
      CompletedDelivery.arrowType, renameAtom, renameAtomList, name, Atom.atomType]
  have returned := symbol_singleton_read ops world depth supply "if" original declared
  refine ⟨name, ?_, ?_⟩
  · simpa only [prepared, shape] using returned
  · have fresh := TypeReadSupply.fresh_avoids prepared original name (by
      rw [shape]
      simp [HEIfSourceSelection.signature, CompletedDelivery.arrowType, atomVariables, atomListVariables, Atom.atomType])
    intro old
    exact fresh (TypeReadSupply.remember_old supply [.symbol "if"] old)

/-- The first empty tuple-head observation ends the type product. No
operand inference or program-body execution is imported into this read. -/
theorem undeclared_application_type (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String) (arguments : List Atom)
    (closed : atomListVariables arguments = [])
    (absent : rawDeclarations source world (.symbol name) = [])
    (ordinary : nativeClassify (.symbol name) arguments = .ordinary) :
    (NativeTypeScopedReads.evaluate ops source world (depth + 2)
      (.infer true (.expression (.symbol name :: arguments))) supply).1 = some (.types [ops.undefined]) := by
  have classifyReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.classify (.symbol name) arguments) = (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, ordinary, NativeTypeScopedReads.retain]
  have annotations (current : Supply) := annotation_empty world current (.symbol name) rfl absent
  have outerAnnotations (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.annotations (.expression (.symbol name :: arguments))) = (some (.types []), current) :=
    annotation_empty world current _ (by simpa [atomVariables, atomListVariables] using closed)
      (no_expression_annotations world _)
  have headRows (current : Supply) :
      NativeTypeScopedReads.evaluate ops source world (depth + 1) (.operatorRows (.symbol name)) current =
        (some (.types []), current) := by
    simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
      NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
      Mettapedia.Machines.QueryState.run, annotations, NativeTypeRecursiveDriver.completed,
      NativeTypeScopedReads.retain, TypeReadSupply.remember, atomListVariables]
  have tupleHead (current : Supply) :
      NativeTypeScopedReads.evaluate ops source world (depth + 1) (.tuplePart true (.symbol name)) current =
        (some (.types []), current) := by
    simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
      NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
      Mettapedia.Machines.QueryState.run, annotations, NativeTypeRecursiveDriver.completed,
      NativeTypeScopedReads.retain, TypeReadSupply.remember, atomListVariables]
  rw [NativeTypeScopedReads.evaluate]
  simp only [NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.ordinary,
    NativeTypeCallGraph.typesRead, NativeTypeCallGraph.finishTypes, NativeTypeCallGraph.liftViews,
    NativeTypeCallGraph.viewQuestion, NativeTypeDemand.productPlan, NativeTypeDemand.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    Mettapedia.Machines.ReadOnlyQuery.bind, classifyReply, outerAnnotations, headRows, tupleHead,
    List.isEmpty_nil, ite_true, List.any_nil, Bool.false_eq_true, ite_false, List.map_nil,
    NativeTypeRecursiveDriver.completed]

theorem range_type (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (lower upper : Int) :
    (NativeTypeScopedReads.evaluate ops source world (depth + 2)
      (.infer true (.expression [.symbol "range", .grounded (.int lower), .grounded (.int upper)])) supply).1 =
      some (.types [ops.undefined]) := by
  apply undeclared_application_type
  · rfl
  · rw [declarations_eq]; rfl
  · rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionTypeReadApplications
