import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadPrimitives

/-!
# Local inferred application queries reached by range

The actual occurrence-scoped reader is used with the existing source-shaped
normalizer. Grounded intrinsic replies, raw operator rows and complete
inference remain distinct roles. Supply changes are retained explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadApplications

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)
open HERangeTypeReadPrimitives (source)

theorem fresh_closed (supply : Supply) (type : Atom) (closed : atomVariables type = []) :
    TypeReadSupply.fresh supply type = (type, ⟨supply.used, supply.next + 1⟩) := by
  simp [TypeReadSupply.fresh, instantiateTypeSignature_closed _ _ closed, closed]

theorem annotation_empty (world : ExternalView) (supply : Supply) (subject : Atom)
    (closed : atomVariables subject = []) (absent : rawDeclarations source world subject = []) :
    NativeTypeScopedReads.primitive source world supply (.annotations subject) = (some (.types []), supply) := by
  simp [NativeTypeScopedReads.primitive, absent, TypeReadSupply.freshList, TypeReadSupply.remember,
    atomListVariables, closed]

theorem operator_singleton (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) (closed : atomVariables type = []) :
    NativeTypeScopedReads.evaluate ops source world (depth + 1) (.operatorRows (.symbol name)) supply =
      (some (.types [type]), ⟨supply.used, supply.next + 1⟩) := by
  simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
    Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList,
    fresh_closed _ _ closed, NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed,
    TypeReadSupply.remember, atomListVariables, atomVariables, closed]

theorem closed_symbol (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) (closed : atomVariables type = []) :
    (NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol name)) supply).1 =
      some (.types [type]) := by
  simpa only [fresh_closed _ _ closed] using
    HERangeTypeReadPrimitives.symbol_singleton_read ops world depth supply name type declared

theorem undeclared_range (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol "range")) supply =
      (some (.types [ops.undefined]), TypeReadSupply.remember supply [ops.undefined]) := by
  apply HERangeTypeReadPrimitives.undeclared_symbol_read
  rw [HERangeTypeReadPrimitives.declarations_eq]
  rfl

theorem undeclared_empty (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol "empty")) supply =
      (some (.types [ops.undefined]), TypeReadSupply.remember supply [ops.undefined]) := by
  apply HERangeTypeReadPrimitives.undeclared_symbol_read
  rw [HERangeTypeReadPrimitives.declarations_eq]
  rfl

theorem number_match (world : ExternalView) :
    TypeScopeMatcher.unify world Atom.var (.symbol "Number") (.symbol "Number") = some Atom.var := by
  simp only [TypeScopeMatcher.unify, substA, RetainedTypePayloads.observe, TypeScopeMatcher.wildcard,
    Atom.undefinedType, Atom.atomType]
  cbv

def ops (world : ExternalView) (active : String → Bool) (primitive : TypeNormalizationScope.Primitive)
    (unobservedClosure : List Atom → List Atom) : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom :=
  TypeDependencyClosure.sourceOps world active primitive unobservedClosure

theorem comparison_type (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (depth : Nat) (supply : Supply) (left right : Int) :
    (NativeTypeScopedReads.evaluate (ops world active primitive unobservedClosure) source world (depth + 2)
      (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 =
      some (.types [.symbol "Bool"]) := by
  have declared : rawDeclarations source world (.symbol ">=") =
      [HEBinaryNumericSource.greaterEqual.signature.functionType] := by
    rw [HERangeTypeReadPrimitives.declarations_eq]
    rfl
  have closed : atomVariables HEBinaryNumericSource.greaterEqual.signature.functionType = [] := rfl
  let currentOps := ops world active primitive unobservedClosure
  have classifyReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.classify (.symbol ">=") [.grounded (.int left), .grounded (.int right)]) =
      (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, nativeClassify, NativeTypeScopedReads.retain]
  have annotationReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.annotations (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) =
      (some (.types []), current) :=
    annotation_empty world current _ rfl (HERangeTypeReadPrimitives.no_expression_annotations world _)
  have headReply (current : Supply) := operator_singleton currentOps world depth current ">=" _ declared closed
  have childReply (current : Supply) (value : Int) := HERangeTypeReadPrimitives.number_read currentOps source world depth value current
  have kindReply (current : Supply) (value : Int) : NativeTypeScopedReads.primitive source world current
      (.kind (.grounded (.int value))) = (some (.kind Atom.groundedType), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain, getMetaType]
  have arrow : currentOps.arrow HEBinaryNumericSource.greaterEqual.signature.functionType =
      some ([.symbol "Number", .symbol "Number"], .symbol "Bool") := rfl
  have initial : currentOps.initial = Atom.var := rfl
  have metaChoice (state : TypeScopeMatcher.State) : currentOps.metaCheck (currentOps.apply state (.symbol "Number")) Atom.groundedType = none := rfl
  have matching : currentOps.unify Atom.var (.symbol "Number") (currentOps.apply Atom.var (.symbol "Number")) = some Atom.var := number_match world
  have normalized : currentOps.normalize (currentOps.apply Atom.var (.symbol "Bool")) = .symbol "Bool" := rfl
  change (NativeTypeScopedReads.evaluate currentOps source world (depth + 2)
    (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 = _
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

theorem comparison_shallow_declines (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (supply : Supply) (left right : Int) :
    (NativeTypeScopedReads.evaluate currentOps source world 1
      (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 = none := by
  have classifyReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.classify (.symbol ">=") [.grounded (.int left), .grounded (.int right)]) =
      (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, nativeClassify, NativeTypeScopedReads.retain]
  have annotationReply (current : Supply) : NativeTypeScopedReads.primitive source world current
      (.annotations (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) =
      (some (.types []), current) :=
    annotation_empty world current _ rfl (HERangeTypeReadPrimitives.no_expression_annotations world _)
  rw [NativeTypeScopedReads.evaluate]
  simp only [NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.ordinary,
    NativeTypeCallGraph.typesRead, Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    classifyReply, annotationReply, List.isEmpty_nil, ite_true, NativeTypeScopedReads.evaluate,
    NativeTypeRecursiveDriver.completed]

/-- Every completed reply of this reached non-meta query is the singleton
Bool family, independently of the caller's protected supply and bound values. -/
theorem comparison_types_unique (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (depth : Nat) (supply : Supply) (left right : Int) (types : List Atom)
    (completed : (NativeTypeScopedReads.evaluate (ops world active primitive unobservedClosure) source world depth
      (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 = some (.types types)) :
    types = [.symbol "Bool"] := by
  cases depth with
  | zero => simp [NativeTypeScopedReads.evaluate] at completed
  | succ depth =>
      cases depth with
      | zero => rw [comparison_shallow_declines] at completed; cases completed
      | succ depth =>
          change (NativeTypeScopedReads.evaluate (ops world active primitive unobservedClosure) source world (depth + 2)
            (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 = some (.types types) at completed
          rw [comparison_type] at completed
          exact (NativeTypeDemand.ViewReply.types.inj (Option.some.inj completed)).symm

theorem plus_head_type (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) :
    (NativeTypeScopedReads.evaluate currentOps source world (depth + 1) (.infer true (.symbol "+")) supply).1 =
      some (.types [HEBinaryNumericSource.addition.signature.functionType]) := by
  apply closed_symbol
  · rw [HERangeTypeReadPrimitives.declarations_eq]; rfl
  · rfl

theorem comparison_head_type (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) :
    (NativeTypeScopedReads.evaluate currentOps source world (depth + 1) (.infer true (.symbol ">=")) supply).1 =
      some (.types [HEBinaryNumericSource.greaterEqual.signature.functionType]) := by
  apply closed_symbol
  · rw [HERangeTypeReadPrimitives.declarations_eq]; rfl
  · rfl

theorem superpose_head_type (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) :
    (NativeTypeScopedReads.evaluate currentOps source world (depth + 1) (.infer true (.symbol "superpose")) supply).1 =
      some (.types [HERangeSourceProgram.superposeType]) := by
  apply closed_symbol
  · rw [HERangeTypeReadPrimitives.declarations_eq]; rfl
  · rfl

/-- The returned if arrow is the reader's real fresh instance, not a
reused schema or a preselected name supplied by a source theorem. -/
theorem if_head_type (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) :
    ∃ name,
      (NativeTypeScopedReads.evaluate currentOps source world (depth + 1) (.infer true (.symbol "if")) supply).1 =
        some (.types [(HEIfSourceSelection.signature name).functionType]) ∧ name ∉ supply.used := by
  let prepared := TypeReadSupply.remember supply [Atom.symbol "if"]
  let original := (HEIfSourceSelection.signature "t").functionType
  let name := instanceName prepared.used (atomVariables original).eraseDups prepared.next "t"
  have declared : rawDeclarations source world (.symbol "if") = [original] := by
    rw [HERangeTypeReadPrimitives.declarations_eq]
    rfl
  have shape : (TypeReadSupply.fresh prepared original).1 = (HEIfSourceSelection.signature name).functionType := by
    simp [TypeReadSupply.fresh, instantiateTypeSignature, original, HEIfSourceSelection.signature,
      CompletedDelivery.arrowType, renameAtom, renameAtomList, name, Atom.atomType]
  have returned := HERangeTypeReadPrimitives.symbol_singleton_read currentOps world depth supply "if" original declared
  refine ⟨name, ?_, ?_⟩
  · simpa only [prepared, shape] using returned
  · have fresh := TypeReadSupply.fresh_avoids prepared original name (by
      rw [shape]
      simp [HEIfSourceSelection.signature, CompletedDelivery.arrowType, atomVariables, atomListVariables, Atom.atomType])
    intro old
    exact fresh (TypeReadSupply.remember_old supply [.symbol "if"] old)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadApplications
