import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSpaceExtension
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadApplications

/-! Occurrence-scoped reads of the actual collection source packet. Its
additional declarations do not disappear: local replies are derived from
the extended rows, and no global equality with the smaller range packet
is asserted. Empty subtype scans still execute their private-name protocol. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionTypeReadPrimitives

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)

def source : Source :=
  { HERangeTypeReadPrimitives.source with
    rows := HECollectionSpaceExtension.space.atoms
    rename := fun subject index => instanceName (atomVariables subject)
      (atomListVariables HECollectionSpaceExtension.space.atoms).eraseDups index }

theorem safe : NativeTypeSourcePorts.Safe source := by
  exact ⟨HECollectionSpaceExtension.plain_source_rows, rfl⟩

theorem declarations_eq (world : ExternalView) (subject : Atom) :
    rawDeclarations source world subject = getAnnotatedTypes HECollectionSpaceExtension.space subject := by
  have rows : RetainedTypePayloads.observeList world HECollectionSpaceExtension.space.atoms =
      HECollectionSpaceExtension.space.atoms := TypeDependencyAdmission.observeList_resourceFree world source.rows safe.1
  cases subject <;>
    simp [rawDeclarations, TypeDependencyAdmission.observedSpace, source, HERangeTypeReadPrimitives.source, getAnnotatedTypes, rows,
      RetainedTypePayloads.observeList]

theorem no_expression_annotations (world : ExternalView) (children : List Atom) :
    rawDeclarations source world (.expression children) = [] := by
  rw [declarations_eq]
  exact HECollectionSpaceExtension.no_expression_declarations children

theorem closure (world : ExternalView) (seeds : List Atom) (supply : Supply) :
    (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha source.subtypeBudget seeds supply).1 =
      some seeds :=
  HERangeTypeReadPrimitives.no_edge_closure world source.rows HECollectionSpaceExtension.no_subtype_rows
    source.subtypeFresh source.alpha 0 seeds supply

theorem symbol_singleton_read (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) :
    (NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol name)) supply).1 =
      some (.types [(TypeReadSupply.fresh (TypeReadSupply.remember supply [.symbol name]) type).1]) := by
  simp only [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.closeTypes, NativeTypeCallGraph.finishTypes,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList, List.isEmpty_cons,
    Bool.false_eq_true, ite_false, ite_true, closure, Option.map_some, NativeTypeRecursiveDriver.completed]

theorem closed_symbol (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) (closed : atomVariables type = []) :
    (NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol name)) supply).1 =
      some (.types [type]) := by
  simpa only [HERangeTypeReadApplications.fresh_closed _ _ closed] using
    symbol_singleton_read ops world depth supply name type declared

theorem undeclared_symbol (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String)
    (absent : rawDeclarations source world (.symbol name) = []) :
    NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol name)) supply =
      (some (.types [ops.undefined]), TypeReadSupply.remember supply [ops.undefined]) := by
  simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
    Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, absent, TypeReadSupply.freshList,
    NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed, TypeReadSupply.remember, atomListVariables, atomVariables]

theorem operator_singleton (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) (closed : atomVariables type = []) :
    NativeTypeScopedReads.evaluate ops source world (depth + 1) (.operatorRows (.symbol name)) supply =
      (some (.types [type]), ⟨supply.used, supply.next + 1⟩) := by
  simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
    Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList,
    HERangeTypeReadApplications.fresh_closed _ _ closed, NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed,
    TypeReadSupply.remember, atomListVariables, atomVariables, closed]

theorem annotation_empty (world : ExternalView) (supply : Supply) (subject : Atom)
    (closed : atomVariables subject = []) (absent : rawDeclarations source world subject = []) :
    NativeTypeScopedReads.primitive source world supply (.annotations subject) = (some (.types []), supply) := by
  simp [NativeTypeScopedReads.primitive, absent, TypeReadSupply.freshList, TypeReadSupply.remember, atomListVariables, closed]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionTypeReadPrimitives
