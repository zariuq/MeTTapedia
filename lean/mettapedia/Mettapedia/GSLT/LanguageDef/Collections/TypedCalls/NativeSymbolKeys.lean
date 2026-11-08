import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViews
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampKeys
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Machines.RevisionedQueryWork

/-!
# Symbol-sensitive keys for ordinary native type transitions

A symbol child is keyed by its identity, not just its inferred types. Other
children keep their kind and full inferred types. For those other children,
the tuple-part view must be a fixed projection of that inference. These
primitive read contracts reconstruct the complete question-qualified
descriptor, and therefore its exact ordered source result.

The ordinary-head admission excludes literal-sensitive special-head typing
and direct expression-subject annotations. It corresponds to the shape path,
not the separate whole-node address cache. Native interning still needs the
retained observation law; key acquisition must also respect completed reads.
This module does not infer either property from groundness or hashing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeSymbolKeys

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeViews

variable {TypeAtom Kind Bind : Type}

inductive ChildKey (TypeAtom Kind : Type) where
  | symbol (name : String)
  | typed (kind : Kind) (types : List TypeAtom)
  deriving DecidableEq

def childKey (reads : Reads Atom TypeAtom Kind) : Atom → ChildKey TypeAtom Kind
  | .symbol name => .symbol name
  | value => .typed (reads.kind value) (reads.inferred value)

def decodeChild (reads : Reads Atom TypeAtom Kind) (tupleView : List TypeAtom → List TypeAtom) :
    ChildKey TypeAtom Kind → ChildView TypeAtom Kind
  | .symbol name => childView reads (.symbol name)
  | .typed kind types => ⟨kind, types, tupleView types⟩

/-- Only a non-symbol child must derive its tuple view from full inference.
Symbols may have different raw annotations despite equal inferred types. -/
def ChildAdmitted (reads : Reads Atom TypeAtom Kind)
    (tupleView : List TypeAtom → List TypeAtom) : Atom → Prop
  | .symbol _ => True
  | value => reads.tuplePart value = tupleView (reads.inferred value)

theorem decode_child {reads : Reads Atom TypeAtom Kind} {tupleView : List TypeAtom → List TypeAtom}
    {value : Atom} (admitted : ChildAdmitted reads tupleView value) :
    decodeChild reads tupleView (childKey reads value) = childView reads value := by
  cases value <;> simp_all [ChildAdmitted, childKey, decodeChild, childView]

structure Key (TypeAtom Kind : Type) where
  head : String
  question : Bool
  children : List (ChildKey TypeAtom Kind)
  deriving DecidableEq

def key (reads : Reads Atom TypeAtom Kind) (question : Bool) (head : String) (children : List Atom) :
    Key TypeAtom Kind := ⟨head, question, children.map (childKey reads)⟩

def decode (reads : Reads Atom TypeAtom Kind) (tupleView : List TypeAtom → List TypeAtom)
    (code : Key TypeAtom Kind) : Descriptor Atom TypeAtom Kind :=
  ⟨.symbol code.head, code.question, .ordinary, [], reads.headRows (.symbol code.head),
    reads.tupleHead (.symbol code.head), code.children.map (decodeChild reads tupleView)⟩

/-- These are primitive source-read facts, not a premise about the result of
the whole inference computation. A native source-index gate must derive them. -/
def Admitted (reads : Reads Atom TypeAtom Kind) (tupleView : List TypeAtom → List TypeAtom)
    (question : Bool) (head : String) (children : List Atom) : Prop :=
  reads.classify (.symbol head) children = .ordinary ∧
    (question = true → reads.annotations (.symbol head) children = []) ∧
      ∀ value ∈ children, ChildAdmitted reads tupleView value

theorem decode_key {reads : Reads Atom TypeAtom Kind} {tupleView : List TypeAtom → List TypeAtom}
    {question : Bool} {head : String} {children : List Atom}
    (admitted : Admitted reads tupleView question head children) :
    decode reads tupleView (key reads question head children) =
      descriptor reads question (.symbol head) children := by
  obtain ⟨ordinary, unannotated, child⟩ := admitted
  have views : (children.map (childKey reads)).map (decodeChild reads tupleView) =
      children.map (childView reads) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro value member
    exact decode_child (child value member)
  have rows : (if question then reads.annotations (.symbol head) children else []) = [] := by
    cases q : question <;> simp [unannotated, q]
  simp only [decode, key, descriptor, ordinary, rows, views]

/-- The repaired key computes the independent source traversal. It contains
neither the whole original child syntax nor the root's inferred answer. -/
theorem key_computes_source (ops : Ops TypeAtom Bind Kind)
    {reads : Reads Atom TypeAtom Kind} {tupleView : List TypeAtom → List TypeAtom}
    {question : Bool} {head : String} {children : List Atom}
    (admitted : Admitted reads tupleView question head children) :
    transition ops (decode reads tupleView (key reads question head children)) =
      sourceNode ops reads question (.symbol head) children := by
  rw [decode_key admitted]
  exact (node_factor ops reads question (.symbol head) children).symm

theorem equal_keys_equal_source (ops : Ops TypeAtom Bind Kind)
    {reads : Reads Atom TypeAtom Kind} {tupleView : List TypeAtom → List TypeAtom}
    {q q' : Bool} {head head' : String} {children children' : List Atom}
    (left : Admitted reads tupleView q head children)
    (right : Admitted reads tupleView q' head' children')
    (same : key reads q head children = key reads q' head' children') :
    sourceNode ops reads q (.symbol head) children =
      sourceNode ops reads q' (.symbol head') children' := by
  rw [← key_computes_source ops left, ← key_computes_source ops right, same]

/-- This is a sufficient read contract for the existing `StampKeys` key,
not a second typing relation. Its expression clause supplies the primitive
reason that a type state determines both views; it does not assume whole
root inference equality. -/
structure PrimitiveViews (reads : Reads Atom Atom Atom) (state : Atom → List Atom)
    (tupleView : List Atom → List Atom) : Prop where
  kind : ∀ value, reads.kind value = Mettapedia.Languages.MeTTa.HE.getMetaType value
  varViews : ∀ x y, childView reads (.var x) = childView reads (.var y)
  literal : ∀ value,
    reads.inferred (.grounded value) = [Mettapedia.Languages.MeTTa.HE.getGroundedType value]
  literalTuple : ∀ value,
    reads.tuplePart (.grounded value) =
      tupleView [Mettapedia.Languages.MeTTa.HE.getGroundedType value]
  expression : ∀ values, reads.inferred (.expression values) = state (.expression values)
  expressionTuple : ∀ values,
    reads.tuplePart (.expression values) = tupleView (state (.expression values))

theorem primitive_views_same_key {reads : Reads Atom Atom Atom} {state : Atom → List Atom}
    {tupleView : List Atom → List Atom} (views : PrimitiveViews reads state tupleView)
    (left right : Atom) (same : StampKeys.cKey state left = StampKeys.cKey state right) :
    childView reads left = childView reads right := by
  cases left <;> cases right <;> simp only [StampKeys.cKey, reduceCtorEq] at same
  · cases same
    rfl
  · exact views.varViews _ _
  · simp only [StampKeys.CChild.literal.injEq] at same
    simp only [childView, views.kind, views.literal, views.literalTuple, same]
    rfl
  · simp only [StampKeys.CChild.typed.injEq] at same
    simp only [childView, views.kind, views.expression, views.expressionTuple, same]
    rfl

/-- Derives the existing table's adequacy from primitive views, head
ownership and absence of expression-subject annotations. In particular the
previous expression-state congruence premise is discharged here. -/
theorem existing_key_adequate {reads : Reads Atom Atom Atom} {state : Atom → List Atom}
    {tupleView : List Atom → List Atom} (views : PrimitiveViews reads state tupleView)
    (head : Atom) (ordinary : ∀ children, reads.classify head children = .ordinary)
    (unannotated : ∀ children, reads.annotations head children = []) :
    StampKeys.Adequate reads (StampKeys.cKey state) head where
  view := primitive_views_same_key views
  classify _ _ _ := by rw [ordinary, ordinary]
  annotations _ _ _ := by rw [unannotated, unannotated]

theorem existing_table_exact (ops : Ops Atom Bind Atom)
    {reads : Reads Atom Atom Atom} {state : Atom → List Atom}
    {tupleView : List Atom → List Atom} (views : PrimitiveViews reads state tupleView)
    (head : Atom) (ordinary : ∀ children, reads.classify head children = .ordinary)
    (unannotated : ∀ children, reads.annotations head children = [])
    (question : Bool) (children : List Atom)
    {table : StampKeys.Table Atom Atom StampKeys.CChild}
    (valid : StampKeys.Valid ops reads (StampKeys.cKey state) table) :
    StampKeys.read ops reads (StampKeys.cKey state) question head children table =
      sourceNode ops reads question head children :=
  StampKeys.read_eq_source ops reads (StampKeys.cKey state) head
    (existing_key_adequate views head ordinary unannotated) question children valid

open Mettapedia.Machines.RevisionedQueryFacts

structure Request where
  question : Bool
  head : String
  children : List Atom

/-- Cache histories may interleave declaration scopes. The current scope
selects both the primitive readers and the service interpretation. -/
theorem history_exact {Scope : Type} [DecidableEq Scope]
    [DecidableEq TypeAtom] [DecidableEq Kind]
    (ops : Scope → Ops TypeAtom Bind Kind) (reads : Scope → Reads Atom TypeAtom Kind)
    (tupleView : Scope → List TypeAtom → List TypeAtom)
    (queries : List (Scope × Request))
    (admitted : ∀ item ∈ queries, Admitted (reads item.1) (tupleView item.1)
      item.2.question item.2.head item.2.children) :
    (requests (fun scope code => transition (ops scope) (decode (reads scope) (tupleView scope) code))
      (queries.map fun q => ⟨q.1, key (reads q.1) q.2.question q.2.head q.2.children⟩) []).facts =
        queries.map fun q => sourceNode (ops q.1) (reads q.1) q.2.question (.symbol q.2.head)
          q.2.children := by
  rw [requests_exact _ _ _ (valid_nil _), List.map_map]
  apply List.map_congr_left
  intro query member
  exact key_computes_source (ops query.1) (admitted query member)

/-- With no eviction, the service computes once per distinct scoped key.
This is not a bound on constructing the keys, looking them up, or executing
the inference service. Every query occurrence still receives its answer. -/
theorem history_computation_count {Scope : Type} [DecidableEq Scope]
    [DecidableEq TypeAtom] [DecidableEq Kind]
    (ops : Scope → Ops TypeAtom Bind Kind) (reads : Scope → Reads Atom TypeAtom Kind)
    (tupleView : Scope → List TypeAtom → List TypeAtom)
    (queries : List (Scope × Request)) :
    (requests (fun scope code => transition (ops scope) (decode (reads scope) (tupleView scope) code))
      (queries.map fun q => ⟨q.1, key (reads q.1) q.2.question q.2.head q.2.children⟩) []).computations =
      (queries.map fun q => (⟨q.1, key (reads q.1) q.2.question q.2.head q.2.children⟩ :
        Mettapedia.Machines.RevisionedQueryFacts.Request Scope (Key TypeAtom Kind))).toFinset.card :=
  Mettapedia.Machines.RevisionedQueryWork.cold_work_exact _ _

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeSymbolKeys
