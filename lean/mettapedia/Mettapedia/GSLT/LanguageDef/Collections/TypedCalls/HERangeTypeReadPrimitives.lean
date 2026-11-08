import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProgram
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEArgumentMetatypeRole
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReadVariants
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedWorld

/-!
# Actual occurrence-scoped type reads for the finite range source slice

The source packet contains the program's actual declarations and equations.
It has no direct expression annotations or subtype rules. Completed subtype
queries still run and allocate their result names; an unfinished query is not
replaced by an empty list. These are laws for the internal inferred reader,
not a global identification with public HE get-type or argument admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadPrimitives

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)

def source : Source where
  rows := HERangeSourceProgram.space.atoms
  intrinsicRows := []
  rename := fun subject index => instanceName (atomVariables subject)
    (atomListVariables HERangeSourceProgram.space.atoms).eraseDups index
  subtypeBudget := 1
  subtypeFresh := "%range-type-result"
  alpha := (· == ·)

theorem source_safe : NativeTypeSourcePorts.Safe source := by
  unfold NativeTypeSourcePorts.Safe
  decide

theorem no_subtype_rows : ∀ row ∈ source.rows, ScopedSubtypeReads.possibleRow row = false := by
  have checked : source.rows.all (fun row => !ScopedSubtypeReads.possibleRow row) = true := by decide
  intro row present
  simpa using (List.all_eq_true.mp checked) row present

theorem declarations_eq (world : ExternalView) (subject : Atom) :
    rawDeclarations source world subject = getAnnotatedTypes HERangeSourceProgram.space subject := by
  have rows : RetainedTypePayloads.observeList world HERangeSourceProgram.space.atoms = HERangeSourceProgram.space.atoms :=
    TypeDependencyAdmission.observeList_resourceFree world source.rows source_safe.1
  cases subject <;>
    simp [rawDeclarations, TypeDependencyAdmission.observedSpace, source, getAnnotatedTypes,
      rows, RetainedTypePayloads.observeList]

theorem no_expression_annotations (world : ExternalView) (children : List Atom) :
    rawDeclarations source world (.expression children) = [] := by
  rw [declarations_eq]
  rfl

theorem no_edge_scan (world : ExternalView) (rows : List Atom)
    (absent : ∀ row ∈ rows, ScopedSubtypeReads.possibleRow row = false)
    (input : Atom) (name : String) (supply : Supply) :
    ScopedSubtypeReads.rows world input name rows supply = ([], supply) := by
  induction rows generalizing supply with
  | nil => rfl
  | cons row rows ih =>
      simp only [ScopedSubtypeReads.rows, absent row (by simp), Bool.false_eq_true, ite_false]
      exact ih (fun item member => absent item (List.mem_cons_of_mem _ member)) supply

theorem no_edge_query (world : ExternalView) (rows : List Atom)
    (absent : ∀ row ∈ rows, ScopedSubtypeReads.possibleRow row = false)
    (base : String) (input : Atom) (supply : Supply) :
    (ScopedSubtypeReads.query world rows base input supply).1 = [] := by
  simp only [ScopedSubtypeReads.query, no_edge_scan world rows absent]

theorem no_edge_discoveries (world : ExternalView) (rows : List Atom)
    (absent : ∀ row ∈ rows, ScopedSubtypeReads.possibleRow row = false)
    (base : String) (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State)
    (frontier : List (SubtypeClosureRounds.Entry × Nat)) (supply : Supply) :
    (ScopedSubtypeReads.discoveries world rows base alpha before frontier supply).1 = [] := by
  induction frontier generalizing supply with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨entry, index⟩
      simp only [ScopedSubtypeReads.discoveries]
      split
      · exact ih supply
      · simp only [no_edge_query world rows absent, List.filter_nil, List.map_nil]
        exact ih _

/-- The closure is genuinely completed after its empty discovery round.
Its advanced supply is left intact rather than asserted unchanged. -/
theorem no_edge_closure (world : ExternalView) (rows : List Atom)
    (absent : ∀ row ∈ rows, ScopedSubtypeReads.possibleRow row = false)
    (base : String) (alpha : Atom → Atom → Bool) (budget : Nat) (seeds : List Atom) (supply : Supply) :
    (ScopedSubtypeReads.completeTypes world rows base alpha (budget + 1) seeds supply).1 = some seeds := by
  have stopped : (ScopedSubtypeReads.round world rows base alpha (SubtypeClosureRounds.start seeds)
      (TypeReadSupply.remember supply seeds)).1 = none := by
    simp only [ScopedSubtypeReads.round, no_edge_discoveries world rows absent, List.isEmpty_nil, ite_true]
  simp only [ScopedSubtypeReads.completeTypes, ScopedSubtypeReads.run, stopped]
  simp [SubtypeClosureRounds.start, Function.comp_def]

theorem source_closure (world : ExternalView) (seeds : List Atom) (supply : Supply) :
    (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha source.subtypeBudget seeds supply).1 = some seeds :=
  no_edge_closure world source.rows no_subtype_rows source.subtypeFresh source.alpha 0 seeds supply

theorem closure_reply (world : ExternalView) (seeds : List Atom) (supply : Supply) :
    (NativeTypeScopedReads.primitive source world supply (.closure seeds)).1 = some (.types seeds) := by
  simp only [NativeTypeScopedReads.primitive, source_closure, Option.map_some]

/-- Every source symbol query keeps its actual occurrence-specific fresh
instance; completion of the subtype port is proved from the source rows. -/
theorem symbol_singleton_read (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations source world (.symbol name) = [type]) :
    (NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol name)) supply).1 =
      some (.types [(TypeReadSupply.fresh (TypeReadSupply.remember supply [.symbol name]) type).1]) := by
  simp only [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.closeTypes, NativeTypeCallGraph.finishTypes,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList, List.isEmpty_cons,
    Bool.false_eq_true, ite_false, ite_true, source_closure, Option.map_some, NativeTypeRecursiveDriver.completed]

theorem undeclared_symbol_read (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (depth : Nat) (supply : Supply) (name : String)
    (absent : rawDeclarations source world (.symbol name) = []) :
    NativeTypeScopedReads.evaluate ops source world (depth + 1) (.infer true (.symbol name)) supply =
      (some (.types [ops.undefined]), TypeReadSupply.remember supply [ops.undefined]) := by
  simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
    Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, absent, TypeReadSupply.freshList,
    NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed, TypeReadSupply.remember, atomListVariables, atomVariables]

theorem number_read (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (packet : Source)
    (world : ExternalView) (depth : Nat) (value : Int) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops packet world (depth + 1) (.infer true (.grounded (.int value))) supply =
      (some (.types [.symbol "Number"]), supply) := by
  simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
    Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive,
    NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed, getGroundedType,
    TypeReadSupply.remember, atomListVariables, atomVariables]

theorem boolean_read (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (packet : Source)
    (world : ExternalView) (depth : Nat) (value : Bool) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops packet world (depth + 1) (.infer true (.grounded (.bool value))) supply =
      (some (.types [.symbol "Bool"]), supply) := by
  simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
    Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive,
    NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed, getGroundedType,
    TypeReadSupply.remember, atomListVariables, atomVariables]

theorem literal_normalization (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (name : String) :
    InertTypeDependencies.normalize active primitive (.symbol name) = .symbol name := rfl

theorem annotation_scope (world : ExternalView) (supply : Supply) (subject : Atom) (types : List Atom)
    (returned : (NativeTypeScopedReads.primitive source world supply (.annotations subject)).1 = some (.types types)) :
    Spec.Type.Presentation.Exact.ArgumentAlphaVariantsRel (TypeReadSupply.remember supply [subject]).used
      (getAnnotatedTypes HERangeSourceProgram.space subject) types := by
  simpa only [declarations_eq] using NativeTypeScopedReads.annotation_variants source world supply subject types returned

namespace Controls

theorem closure_needs_a_completed_round (world : ExternalView) (supply : Supply) :
    (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha 0 [.symbol "Number"] supply).1 = none ∧
    (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha 1 [.symbol "Number"] supply).1 = some [.symbol "Number"] :=
  ⟨rfl, source_closure world [.symbol "Number"] supply⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadPrimitives
