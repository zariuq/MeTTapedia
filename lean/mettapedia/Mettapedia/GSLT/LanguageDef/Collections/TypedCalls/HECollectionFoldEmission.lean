import Mettapedia.Languages.MeTTa.HE.CollectionStdlibSource
import Mettapedia.Languages.MeTTa.HE.ScopedGroundedBoundary

/-!
# One hygienic minimal-fold source emission

The helper emits source syntax for one iteration, not a completed fold.
Template parameters are replaced by full annotated values; other variables
share an injective fresh map. The chain binder is fresh after that map.
Hidden support is an explicit input from the owning world, not inferred by
looking through an opaque snapshot token. This specifies a freshness
contract, not a requirement that a native allocator scan these lists.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldEmission

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation

def call (items : List Entry.Value) (init : Entry.Value) (left right : String)
    (operation context : Entry.Value) (itemsMark : Entry.Status := .active) : Entry.Value :=
  .expression .active [.symbol CollectionStdlibSource.foldName, .expression itemsMark items,
    init, .var left, .var right, operation, context]

def protectedNames (hidden : List String) (live : List Atom) (scope : List String) (frame : Frame)
    (items : List Entry.Value) (init : Entry.Value) (left right : String) (operation context : Entry.Value) : List String :=
  invocationTypeScope scope live (call items init left right operation context).erase Atom.undefinedType frame.bindings ++ hidden

def renamed (avoid : List String) (operation : Entry.Value) (name : String) : String :=
  instanceName avoid (TypeSubst.typeVars operation.erase) 0 name

def rewritten (avoid : List String) (init head : Entry.Value) (left right : String) (operation : Entry.Value) : Entry.Value :=
  Entry.Value.substitute .preserve
    (fun name => if name = left then init else if name = right then head else .var (renamed avoid operation name)) operation

def chainName (avoid : List String) (operation : Entry.Value) : String :=
  instanceName (avoid ++ (TypeSubst.typeVars operation.erase).map (renamed avoid operation)) ["x"] 0 "x"

def step (avoid : List String) (head : Entry.Value) (tail : List Entry.Value)
    (init : Entry.Value) (left right : String) (operation context : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "chain",
    .expression .active [.symbol "metta", rewritten avoid init head left right operation, .symbol "%Undefined%", context],
    .var (chainName avoid operation),
    .expression .active [.symbol "eval", call tail (.var (chainName avoid operation)) left right operation context]]

def emission (hidden : List String) (live : List Atom) (scope : List String) (frame : Frame)
    (items : List Entry.Value) (init : Entry.Value) (left right : String) (operation context : Entry.Value) : Entry.Value :=
  match items with
  | [] => .expression .active [.symbol "return", init]
  | head :: tail => step (protectedNames hidden live scope frame items init left right operation context)
      head tail init left right operation context

theorem renamed_injective (avoid : List String) (operation : Entry.Value) : Function.Injective (renamed avoid operation) :=
  instanceName_injective _ _ _

theorem renamed_fresh (avoid : List String) (operation : Entry.Value) (name : String) :
    renamed avoid operation name ∉ avoid := instanceName_not_mem _ _ _ _

theorem chain_fresh (avoid : List String) (operation : Entry.Value) : chainName avoid operation ∉ avoid := by
  intro present
  exact instanceName_not_mem _ _ _ _ (List.mem_append_left _ present)

theorem chain_distinct_from_renamed (avoid : List String) (operation : Entry.Value) (name : String)
    (occurs : name ∈ TypeSubst.typeVars operation.erase) : chainName avoid operation ≠ renamed avoid operation name := by
  intro same
  apply instanceName_not_mem (avoid ++ (TypeSubst.typeVars operation.erase).map (renamed avoid operation)) ["x"] 0 "x"
  change chainName avoid operation ∈ _
  rw [same]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨name, occurs, rfl⟩)

theorem protects_caller_and_hidden (hidden : List String) (live : List Atom) (scope : List String) (frame : Frame)
    (items : List Entry.Value) (init : Entry.Value) (left right : String) (operation context : Entry.Value) :
    let name := chainName (protectedNames hidden live scope frame items init left right operation context) operation
    name ∉ specBindingVars frame.bindings ∧ name ∉ hidden ∧ name ∉ scope := by
  dsimp only
  have fresh := chain_fresh (protectedNames hidden live scope frame items init left right operation context) operation
  have fromCaller (name : String) (present : name ∈ specBindingVars frame.bindings) :
      name ∈ protectedNames hidden live scope frame items init left right operation context := by
    simp [protectedNames, invocationTypeScope, present]
  have fromScope (name : String) (present : name ∈ scope) :
      name ∈ protectedNames hidden live scope frame items init left right operation context := by
    simp [protectedNames, invocationTypeScope, present]
  refine ⟨?_, ?_, ?_⟩
  · intro present
    exact fresh (fromCaller _ present)
  · intro present
    exact fresh (List.mem_append_right _ present)
  · intro present
    exact fresh (fromScope _ present)

theorem protects_call (hidden : List String) (live : List Atom) (scope : List String) (frame : Frame)
    (items : List Entry.Value) (init : Entry.Value) (left right : String) (operation context : Entry.Value) :
    chainName (protectedNames hidden live scope frame items init left right operation context) operation ∉
      TypeSubst.typeVars (call items init left right operation context).erase := by
  have includes (name : String) (present : name ∈ TypeSubst.typeVars (call items init left right operation context).erase) :
      name ∈ protectedNames hidden live scope frame items init left right operation context := by
    simp [protectedNames, invocationTypeScope, TypeSubst.typeVarsList_append,
      TypeSubst.typeVarsList, present]
  intro present
  exact chain_fresh _ _ (includes _ present)

theorem chain_distinct_from_parameters (hidden : List String) (live : List Atom) (scope : List String) (frame : Frame)
    (items : List Entry.Value) (init : Entry.Value) (left right : String) (operation context : Entry.Value) :
    let name := chainName (protectedNames hidden live scope frame items init left right operation context) operation
    left ≠ name ∧ right ≠ name := by
  dsimp only
  have omitted := protects_call hidden live scope frame items init left right operation context
  constructor <;> intro same <;> apply omitted <;> rw [← same] <;>
    simp [call, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]

/-- The actual collapse operation template has no third class of variables.
Its replacement retains both full values and the template's root mark. -/
theorem collapse_template (avoid : List String) (init head : Entry.Value) (left right : String)
    (different : left ≠ right) (readiness : Entry.Status)
    (operatorName : String := CollectionStdlibSource.appendName) :
    rewritten avoid init head left right
      (.expression readiness [.symbol operatorName, .var left, .var right]) =
      .expression readiness [.symbol operatorName, init, head] := by
  simp [rewritten, Entry.Value.substitute, Entry.Value.rebuildStatus, Ne.symm different]

theorem empty_returns_init (hidden : List String) (live : List Atom) (scope : List String) (frame : Frame)
    (init : Entry.Value) (left right : String) (operation context : Entry.Value) :
    emission hidden live scope frame [] init left right operation context = .expression .active [.symbol "return", init] := rfl

theorem step_is_minimal_instruction (avoid : List String) (head : Entry.Value) (tail : List Entry.Value)
    (init : Entry.Value) (left right : String) (operation context : Entry.Value) :
    Minimal.embeddedInstruction (step avoid head tail init left right operation context).erase = true := by
  simp [step, Entry.Value.erase, Minimal.embeddedInstruction]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldEmission
