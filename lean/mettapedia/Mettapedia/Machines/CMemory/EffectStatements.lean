import Mettapedia.Machines.CMemory.StatementBlock
import Mettapedia.Machines.CMemory.PostIndexWrites

/-!
# Declared leading effects followed by retained physical blocks

One supplied effect is executed before its actual statement continuation.
The continuation and scoped flow reuse the existing block service. Selected
branches keep both supplied bodies; an unselected effect is not evaluated.

The deallocation service is explicitly bound to one call name and executes
the actual pointer operand. This is not an arbitrary foreign-call or general
C statement interpreter. Unsupported calls, arities and operand types are
undefined rather than repaired or ignored.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.EffectStatements

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

abbrev Handler := StatementBlock.Effect

/-- Void calls use the same retained argument evaluator as value calls. The
effect catalogue supplies the declared name/arity/conversion and physical
state contract; no scalar dummy return stands in for a void operation. -/
def invokeWithNames (names : NameReads) (values : Calls) (effects : CallService Unit)
    (layout : Layout) (operand : CExpr) (objects : ObjectReads := {}) : CProg CVal Unit :=
  match operand with
  | .call name arguments => do
      let actual ← argumentsWithNames names values layout arguments objects
      effects name actual
  | _ => CProg.undefined

/-- The immutable-local profile keeps its existing public interface while
void arguments share the same general identifier reader as value calls. -/
def invoke (values : Calls) (effects : CallService Unit) (layout : Layout)
    (environment : Environment) (operand : CExpr) : CProg CVal Unit :=
  invokeWithNames (fun name => resolved (environment name)) values effects layout operand

/-- The established immutable-local call equation remains available to
consumers; identifier reads and void calls share one argument evaluator. -/
theorem invoke_equation (values : Calls) (effects : CallService Unit) (layout : Layout)
    (environment : Environment) (operand : CExpr) :
    invoke values effects layout environment operand = (match operand with
      | .call name arguments => argumentsWith values layout environment arguments >>= effects name
      | _ => CProg.undefined) := by
  cases operand <;> rfl

theorem named_void_call_keeps_actual_arguments (names : NameReads) (values : Calls)
    (effects : CallService Unit) (layout : Layout) (name : Name) (arguments : List CExpr)
    (objects : ObjectReads := {}) :
    invokeWithNames names values effects layout (.call name arguments) objects =
      (argumentsWithNames names values layout arguments objects >>= effects name) := rfl

/-- A void call receives the supplied object address without reading the object
as a scalar. The call service remains responsible for its physical effect. -/
theorem named_void_call_receives_object_address (names : NameReads) (values : Calls)
    (effects : CallService Unit) (layout : Layout) (name localName : Name) (address : Ptr) :
    invokeWithNames names values effects layout
      (.call name [.unary .address (.identifier localName)])
      { place := some (fun _ => some address) } = effects name [.ptr (some address)] := by
  simp only [invokeWithNames, argumentsWithNames.eq_def,
    supplied_object_address_skips_rvalue, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem void_call_keeps_actual_arguments (values : Calls) (effects : CallService Unit)
    (layout : Layout) (environment : Environment) (name : Name) (arguments : List CExpr) :
    invoke values effects layout environment (.call name arguments) =
      (argumentsWith values layout environment arguments >>= effects name) := rfl

/-- Resolve the field lvalue once and perform the declared sequential wide
increment. An embedded record, pointer, Boolean or signed scalar does not
acquire an unsigned-counter interpretation. -/
def incrementField (profile : StatementBlock.ObjectBindings.Profile) (layout : Layout)
    (context : StatementBlock.ObjectBindings.Context) (owner : CExpr) (name : Name)
    (throughPointer : Bool) : CProg CVal Unit := do
  let descriptor ← resolved
    (((StatementBlock.ObjectBindings.objects profile context).fieldLayout
      layout owner throughPointer) name)
  match descriptor.kind with
  | .word64 => do
      let address ← StatementBlock.ObjectBindings.place profile layout context
        (.field owner name throughPointer)
      CProg.incrementU64 address
  | _ => CProg.undefined

/-- Object effects reuse the common argument reader. Discarded field increments
resolve their lvalue once; local increments are outside this profile because
discarding an updated lexical context would lose a semantic effect. -/
def withObjects (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (layout : Layout) (context : StatementBlock.ObjectBindings.Context) :
    CExpr → CProg CVal Unit
  | operand@(.call _ _) =>
      invokeWithNames
        (localOrLocated (StatementBlock.ObjectBindings.values context)
          (StatementBlock.ObjectBindings.declared context) profile.locations)
        profile.values effects layout operand (StatementBlock.ObjectBindings.objects profile context)
  | .postIncrement (.field owner name throughPointer)
  | .unary .increment (.field owner name throughPointer) =>
      incrementField profile layout context owner name throughPointer
  | _ => CProg.undefined

theorem discarded_wide_increment_resolves_place_once
    (profile : StatementBlock.ObjectBindings.Profile) (layout : Layout)
    (context : StatementBlock.ObjectBindings.Context) (owner : CExpr) (name : Name)
    (throughPointer : Bool) (offset : Nat)
    (descriptor : ((StatementBlock.ObjectBindings.objects profile context).fieldLayout
      layout owner throughPointer) name = some ⟨offset, .word64⟩) :
    incrementField profile layout context owner name throughPointer =
      (StatementBlock.ObjectBindings.place profile layout context (.field owner name throughPointer)
        >>= CProg.incrementU64) := by
  simp only [incrementField, descriptor, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem object_void_call_keeps_all_actual_arguments
    (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (layout : Layout) (context : StatementBlock.ObjectBindings.Context)
    (name : Name) (arguments : List CExpr) :
    withObjects profile effects layout context (.call name arguments) =
      (argumentsWithNames
        (localOrLocated (StatementBlock.ObjectBindings.values context)
          (StatementBlock.ObjectBindings.declared context) profile.locations)
        profile.values layout arguments (StatementBlock.ObjectBindings.objects profile context)
        >>= effects name) := rfl

theorem discarded_local_increment_is_not_ignored
    (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (layout : Layout) (context : StatementBlock.ObjectBindings.Context) (name : Name) :
    withObjects profile effects layout context (.postIncrement (.identifier name)) =
      CProg.undefined := rfl

theorem wrongly_typed_increment_rejected
    (profile : StatementBlock.ObjectBindings.Profile) (layout : Layout)
    (context : StatementBlock.ObjectBindings.Context) (owner : CExpr) (name : Name)
    (throughPointer : Bool) (offset : Nat)
    (descriptor : ((StatementBlock.ObjectBindings.objects profile context).fieldLayout
      layout owner throughPointer) name = some ⟨offset, .pointer⟩) :
    incrementField profile layout context owner name throughPointer = CProg.undefined := by
  simp only [incrementField, descriptor, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]


def deallocate (name : Name) (layout : Layout) (environment : Environment) :
    CExpr → CProg CVal Unit
  | .call supplied [operand] =>
      if supplied = name then do
        let value ← expression layout environment operand
        let actual ← pointer value
        CProg.free actual
      else CProg.undefined
  | _ => CProg.undefined

def beforeBlock (effect : Handler) (assign : StatementBlock.Assignment) (layout : Layout)
    (innerFuel bodyFuel : Nat) (environment : Environment) : List CStatement →
    CProg CVal ReadBlock.Result
  | .effect operand :: continuation => do
      effect layout environment operand
      StatementBlock.execute assign layout innerFuel bodyFuel environment continuation
  | body => StatementBlock.execute assign layout innerFuel bodyFuel environment body

def selected (effect : Handler) (assign : StatementBlock.Assignment) (layout : Layout)
    (innerFuel bodyFuel : Nat) (environment : Environment) : CStatement →
    CProg CVal ReadBlock.Result
  | .branch condition yes no => do
      let value ← expression layout environment condition
      let actual ← truth value
      beforeBlock effect assign layout innerFuel bodyFuel environment (if actual then yes else no)
  | _ => CProg.undefined

theorem deallocation_keeps_actual_operand (name : Name) (layout : Layout)
    (environment : Environment) (operand : CExpr) :
    deallocate name layout environment (.call name [operand]) =
      (expression layout environment operand >>= fun value => pointer value >>= CProg.free) := by
  simp only [deallocate, ↓reduceIte]

theorem bound_pointer_operand_is_not_replaced (name localName : Name) (layout : Layout)
    (environment : Environment) (actual : Option Ptr)
    (bound : environment localName = some (.ptr actual)) :
    deallocate name layout environment (.call name [.identifier localName]) =
      CProg.free actual := by
  rw [deallocation_keeps_actual_operand]
  simp only [expression, expressionWith_equation, bound, resolved, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]

theorem leading_effect_precedes_actual_continuation (effect : Handler)
    (assign : StatementBlock.Assignment) (layout : Layout) (innerFuel bodyFuel : Nat)
    (environment : Environment) (operand : CExpr) (continuation : List CStatement) :
    beforeBlock effect assign layout innerFuel bodyFuel environment (.effect operand :: continuation) =
      (effect layout environment operand >>= fun _ =>
        StatementBlock.execute assign layout innerFuel bodyFuel environment continuation) := rfl

theorem selected_branch_keeps_authored_bodies (effect : Handler)
    (assign : StatementBlock.Assignment) (layout : Layout) (innerFuel bodyFuel : Nat)
    (environment : Environment) (condition : CExpr) (yes no : List CStatement) :
    selected effect assign layout innerFuel bodyFuel environment (.branch condition yes no) =
      (expression layout environment condition >>= fun value => truth value >>= fun actual =>
        beforeBlock effect assign layout innerFuel bodyFuel environment (if actual then yes else no)) := rfl

section PhysicalDeallocation

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem deallocate_dynamic_array (address : Ptr) (capacity : Nat) (values : List CVal) :
    CTriple (L := L) (DynArray (some address) capacity values)
      (CProg.free (some address)) (fun _ => DeadStorage (some address) capacity) := by
  refine triple_pre _ (P := fun σ => address.offset = 0 ∧
    (LiveBlock address.block capacity ∗ CellsAny address capacity) σ) ?_ ?_
  · intro σ held
    obtain ⟨base, size, spare, spareLength, cells⟩ :=
      (dynArray_some_iff address capacity values σ).mp held
    refine ⟨base, ?_⟩
    exact sepConj_mono le_rfl (fun τ initialized => ⟨values.map some ++ spare,
      by simp only [List.length_append, List.length_map, spareLength]; omega,
      initialized⟩) σ cells
  · apply triple_pure
    intro base
    obtain ⟨block, offset⟩ := address
    dsimp only at base
    subst offset
    exact free_spec block capacity

theorem null_deallocation_preserves_frame (P : Heap L → Prop) :
    CTriple P (CProg.free (V := CVal) none) (fun _ => P) := by
  apply triple_prim
  intro σ held
  exact ⟨trivial, fun _ _ same => same ▸ held⟩

end PhysicalDeallocation

namespace Controls

def emptyLayout : Layout := fun _ => none
def emptyEnvironment : Environment := fun _ => none
def forbidden : Handler := fun _ _ _ => CProg.undefined

theorem noncall_effect_is_not_invented (values : Calls) (effects : CallService Unit)
    (name : Name) :
    invoke values effects emptyLayout emptyEnvironment (.identifier name) = CProg.undefined := rfl

theorem unselected_effect_is_not_executed (body : List CStatement) :
    selected forbidden PostIndexWrites.assign emptyLayout 0 0 emptyEnvironment
      (.branch (.bool false) body []) = pure (.finished (.next emptyEnvironment)) := rfl

theorem unknown_effect_name_is_not_called :
    deallocate "free".toList emptyLayout emptyEnvironment
      (.call "other".toList [.null]) = CProg.undefined := rfl

theorem extra_call_operand_is_not_discarded :
    deallocate "free".toList emptyLayout emptyEnvironment
      (.call "free".toList [.null, .null]) = CProg.undefined := rfl

theorem null_operand_remains_actual_deallocation :
    deallocate "free".toList emptyLayout emptyEnvironment
      (.call "free".toList [.null]) = CProg.free none := rfl

theorem undefined_operand_is_not_success :
    deallocate "free".toList emptyLayout emptyEnvironment
      (.call "free".toList [.identifier "absent".toList]) = CProg.undefined := by
  rw [deallocation_keeps_actual_operand]
  change (CProg.undefined >>= _) = _
  exact undefined_bind _

theorem false_return_prevents_later_effect (body : List CStatement) :
    beforeBlock forbidden PostIndexWrites.assign emptyLayout 0 1 emptyEnvironment
      (.return (some (.bool false)) :: body) =
        pure (.finished (.returned emptyEnvironment (some (.bool false)))) := rfl

end Controls

end Mettapedia.Machines.CMemory.EffectStatements


namespace Mettapedia.Machines.CMemory.EffectStatements

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

/-- A source interpretation can declare a discarded statement macro with
its required syntactic arity. Such a macro omits argument evaluation, not
merely the callee's effect. Agreement with the effective native preprocessor
profile is a separate obligation. Missing declarations use ordinary calls. -/
abbrev OmittedMacros := Name → Option Nat

/-- Retain the common typed object/effect reader except for an explicitly
omitted, arity-checked macro. The omission inventory is static; it never
depends on argument values, boundness, caller scopes or observed effects. -/
def withObjectMacros (profile : StatementBlock.ObjectBindings.Profile)
    (effects : CallService Unit) (omitted : OmittedMacros)
    (layout : Layout) (context : StatementBlock.ObjectBindings.Context)
    (operand : CExpr) : CProg CVal Unit :=
  match operand with
  | .call name arguments => match omitted name with
      | some arity => if arguments.length = arity then pure () else CProg.undefined
      | none => withObjects profile effects layout context operand
  | _ => withObjects profile effects layout context operand

theorem omitted_macro_does_not_evaluate_arguments
    (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (omitted : OmittedMacros) (layout : Layout)
    (context : StatementBlock.ObjectBindings.Context) (name : Name)
    (arguments : List CExpr) (arity : Nat)
    (declared : omitted name = some arity) (correctArity : arguments.length = arity) :
    withObjectMacros profile effects omitted layout context (.call name arguments) = pure () := by
  simp only [withObjectMacros, declared, correctArity, ↓reduceIte]

theorem wrong_macro_arity_is_not_a_discarded_call
    (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (omitted : OmittedMacros) (layout : Layout)
    (context : StatementBlock.ObjectBindings.Context) (name : Name)
    (arguments : List CExpr) (arity : Nat)
    (declared : omitted name = some arity) (wrongArity : arguments.length ≠ arity) :
    withObjectMacros profile effects omitted layout context (.call name arguments) = CProg.undefined := by
  simp only [withObjectMacros, declared, wrongArity, ↓reduceIte]

theorem enabled_call_keeps_the_whole_argument_evaluation
    (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (omitted : OmittedMacros) (layout : Layout)
    (context : StatementBlock.ObjectBindings.Context) (name : Name)
    (arguments : List CExpr) (enabled : omitted name = none) :
    withObjectMacros profile effects omitted layout context (.call name arguments) =
      (argumentsWithNames
        (localOrLocated (StatementBlock.ObjectBindings.values context)
          (StatementBlock.ObjectBindings.declared context) profile.locations)
        profile.values layout arguments (StatementBlock.ObjectBindings.objects profile context)
        >>= effects name) := by
  simp only [withObjectMacros, enabled]
  exact object_void_call_keeps_all_actual_arguments profile effects layout context name arguments

theorem empty_macro_inventory_preserves_all_object_effects
    (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (layout : Layout) (context : StatementBlock.ObjectBindings.Context) (operand : CExpr) :
    withObjectMacros profile effects (fun _ => none) layout context operand =
      withObjects profile effects layout context operand := by
  cases operand <;> rfl

theorem noncall_effect_is_not_omitted_by_macro_inventory
    (profile : StatementBlock.ObjectBindings.Profile) (effects : CallService Unit)
    (omitted : OmittedMacros) (layout : Layout)
    (context : StatementBlock.ObjectBindings.Context) (operand : CExpr)
    (noncall : ∀ name arguments, operand ≠ .call name arguments) :
    withObjectMacros profile effects omitted layout context operand =
      withObjects profile effects layout context operand := by
  cases operand <;> first
    | rfl
    | exact False.elim (noncall _ _ rfl)

end Mettapedia.Machines.CMemory.EffectStatements
