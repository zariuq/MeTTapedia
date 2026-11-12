import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionInferredQueries
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldEmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionClosedAppend

/-! One read-only program context with a separate snapshot world for the
collection path. The local native contracts cover arithmetic, superpose,
one fold emission and one saved-pair append; language execution remains in
the existing stateful source family. No physical snapshot layout is imposed. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionWorld

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom executeGroundedOp)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)

abbrev World := Unit × List Frame
def snapshots : SnapshotServices Space World := SnapshotServices.appendModel Space Unit
def hidden (world : World) : List String := world.2.flatMap (fun frame => specBindingVars frame.bindings)

inductive Primitive (policy : Policy) (label : Space) (world : World) (live : List Atom) (scope : List String) (before : Frame) :
    Entry.Value → GroundedResult Entry.Value → Prop where
  | numeric {mark name arguments value} : name ∈ ["+", ">=", "*"] →
      executeGroundedOp (.symbol name) (arguments.map Entry.Value.erase) = some value →
      Primitive policy label world live scope before (.expression mark (.symbol name :: arguments))
        (.ok [(Entry.Value.ofAtom value, Bindings.empty)])
  | superpose (mark tupleMark : Entry.Status) (items : List Entry.Value) :
      Primitive policy label world live scope before (.expression mark [.symbol "superpose", .expression tupleMark items])
        (.ok (items.map fun item => (item, Bindings.empty)))
  | fold {itemsMark : Entry.Status} (items init left right operation context) :
      Primitive policy label world live scope before (HECollectionFoldEmission.call items init left right operation context (itemsMark := itemsMark))
        (.ok [(HECollectionFoldEmission.emission (hidden world) live scope before items init left right operation context, Bindings.empty)])
  | append {input outcome} : HECollectionClosedAppend.Step snapshots policy label world input outcome →
      Primitive policy label world live scope before input outcome

def services (minimal : Minimal.Services) (policy : Policy) : WorldServices Space World where
  contextPayload := minimal.contextPayload
  nativeCall _ _ _ _ _ _ _ _ := False
  snapshots := some snapshots
  scopedGroundedCall := some (fun label world live scope before input outcome after =>
    after = world ∧ Primitive policy label world live scope before input outcome)

def dispatch : Spec.Eval.GroundedDispatch where
  executable (operator : Atom) := operator ∈ ([.symbol "+", .symbol ">=", .symbol "*", .symbol "superpose",
    .symbol CollectionStdlibSource.foldName, .symbol CollectionStdlibSource.appendName] : List Atom)
  outcome operator arguments result := ∃ policy label world live scope before input output,
    input.erase = .expression (operator :: arguments) ∧ output.map Entry.Value.erase = result ∧
      Primitive policy label world live scope before input output
  valueProvenance operator _ := if operator = .symbol CollectionStdlibSource.appendName then .completed else .emitted

def environment (minimal : Minimal.Services) (policy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom) :
    WorldEnvironment Space World where
  view _ := id
  services := services minimal policy
  dispatch := dispatch
  lookup := HECollectionInferredQueries.lookup (HECollectionInferredQueries.currentOps external active primitive subtypes) external
  arguments := kindArgumentService

theorem ordinary (minimal : Minimal.Services) (policy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (name : String) (arguments : List Atom) (member : name ∈ ["range", "if", "empty", "sq", "foldl-atom", "collapse", "let"]) :
    NonGroundedCallRel (environment minimal policy external active primitive subtypes).dispatch
      (.expression (.symbol name :: arguments)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [NonGroundedCallRel, Minimal.HostCall, environment, dispatch, Minimal.embeddedInstruction,
      CollectionStdlibSource.foldName, CollectionStdlibSource.appendName]

theorem primitive_keeps_world (minimal : Minimal.Services) (policy : Policy)
    (label : Space) (world after : World) (live : List Atom) (scope : List String) (before : Frame)
    (input : Entry.Value) (output : GroundedResult Entry.Value)
    (executed : (services minimal policy).groundedAt label world live scope before input output after) : after = world := executed.1

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionWorld
