import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampInference
import Mettapedia.Machines.RevisionedQueryFacts

/-!
# Question-qualified observations for native type inference

The type carrier is a parameter: full atoms, including numeric type literals,
can be used without translating numbers into symbols. Matching, substitution,
normalization and subtype additions are shared pure services. This is a
cache-relative correctness theorem, not an independent arithmetic verifier.

Two computations are specified independently. The source traversal reads
children as needed by the native argument/tuple branches. The transition
consumes a completed descriptor with distinct inferred and tuple-part views.
Its head classifier retains primitive special cases such as NativeHandle's
literal kind. It never retains the complete root inference as a descriptor
field.

Descriptor fields are completed observations. This module does not authorize
eagerly forcing an unused or nonterminating type query while constructing a
key. Scoped publication and exact history reuse the existing revisioned-fact
cache. Native gate/codec correspondence remains necessary.

Type-state equality here is exact model equality. A native interner must
preserve every observation used by these services, and retained type payloads
must remain valid under the scope. Neither property follows merely from an
empty syntactic variable set, especially for opaque resource-valued types.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViews

variable {Value TypeAtom Bind Kind : Type}

inductive HeadClass where
  | ordinary
  | nativeMork
  | listValue
  deriving DecidableEq

/-- The earlier internal reader stopped at a nonempty application annotation.
The corrected reader additionally scans arrows and removes only derived
answers equal to an annotation-prefix member. Public typing derivations are
not this internal family and keep their own multiplicity. -/
inductive AnnotationPolicy (TypeAtom : Type) where
  | historicalOverride
  | supplement (same : TypeAtom → TypeAtom → Bool)

def supplement (same : TypeAtom → TypeAtom → Bool)
    (annotations derived : List TypeAtom) : List TypeAtom :=
  annotations ++ derived.filter (fun type_ => !(annotations.any (fun prior => same prior type_)))

theorem supplement_empty (same : TypeAtom → TypeAtom → Bool) (derived : List TypeAtom) :
    supplement same [] derived = derived := by simp [supplement]

theorem supplement_no_derived (same : TypeAtom → TypeAtom → Bool) (annotations : List TypeAtom) :
    supplement same annotations [] = annotations := by simp [supplement]

structure Ops (TypeAtom Bind Kind : Type) where
  arrow : TypeAtom → Option (List TypeAtom × TypeAtom)
  initial : Bind
  apply : Bind → TypeAtom → TypeAtom
  unify : Bind → TypeAtom → TypeAtom → Option Bind
  metaCheck : TypeAtom → Kind → Option Bool
  normalize : TypeAtom → TypeAtom
  tuple : List TypeAtom → TypeAtom
  undefined : TypeAtom
  nativeMork : TypeAtom
  listType : TypeAtom
  subtypeAdditions : List TypeAtom → List TypeAtom
  annotationPolicy : AnnotationPolicy TypeAtom := .historicalOverride

def Ops.close (ops : Ops TypeAtom Bind Kind) (types : List TypeAtom) : List TypeAtom :=
  types ++ ops.subtypeAdditions types

structure Reads (Value TypeAtom Kind : Type) where
  classify : Value → List Value → HeadClass
  annotations : Value → List Value → List TypeAtom
  headRows : Value → List TypeAtom
  tupleHead : Value → List TypeAtom
  kind : Value → Kind
  inferred : Value → List TypeAtom
  tuplePart : Value → List TypeAtom

structure ChildView (TypeAtom Kind : Type) where
  kind : Kind
  inferred : List TypeAtom
  tuplePart : List TypeAtom
  deriving DecidableEq

structure Descriptor (Value TypeAtom Kind : Type) where
  head : Value
  question : Bool
  class_ : HeadClass
  annotations : List TypeAtom
  rows : List TypeAtom
  tupleHead : List TypeAtom
  children : List (ChildView TypeAtom Kind)
  deriving DecidableEq

def childView (reads : Reads Value TypeAtom Kind) (value : Value) : ChildView TypeAtom Kind :=
  ⟨reads.kind value, reads.inferred value, reads.tuplePart value⟩

def descriptor (reads : Reads Value TypeAtom Kind) (question : Bool)
    (head : Value) (children : List Value) : Descriptor Value TypeAtom Kind :=
  ⟨head, question, reads.classify head children,
    if question then reads.annotations head children else [], reads.headRows head,
    reads.tupleHead head, children.map (childView reads)⟩

/-- The direct argument loop reads only the view required by each formal. -/
def sourceArgs (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind) :
    List TypeAtom → List Value → Bind → Option Bind
  | [], [], state => some state
  | formal :: formals, value :: values, state =>
      match ops.metaCheck (ops.apply state formal) (reads.kind value) with
      | some true => sourceArgs ops reads formals values state
      | some false => none
      | none =>
          match StampInference.firstResult
              (fun actual => ops.unify state actual (ops.apply state formal)) (reads.inferred value) with
          | none => none
          | some next => sourceArgs ops reads formals values next
  | _, _, _ => none

/-- The descriptor transition uses the recorded inferred view, never its
different tuple-part view, for ordinary argument typing. -/
def transitionArgs (ops : Ops TypeAtom Bind Kind) :
    List TypeAtom → List (ChildView TypeAtom Kind) → Bind → Option Bind
  | [], [], state => some state
  | formal :: formals, child :: children, state =>
      match ops.metaCheck (ops.apply state formal) child.kind with
      | some true => transitionArgs ops formals children state
      | some false => none
      | none =>
          (StampInference.firstResult
            (fun actual => ops.unify state actual (ops.apply state formal)) child.inferred).bind
              (transitionArgs ops formals children)
  | _, _, _ => none

theorem args_factor (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (formals : List TypeAtom) : ∀ values state,
      sourceArgs ops reads formals values state =
        transitionArgs ops formals (values.map (childView reads)) state := by
  induction formals with
  | nil => intro values state; cases values <;> rfl
  | cons formal formals ih =>
      intro values state
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [sourceArgs, List.map_cons, transitionArgs, childView]
          cases metatype : ops.metaCheck (ops.apply state formal) (reads.kind value) with
          | some answer => cases answer <;> simp [ih]
          | none =>
              cases chosen : StampInference.firstResult
                  (fun actual => ops.unify state actual (ops.apply state formal)) (reads.inferred value) with
              | none => rfl
              | some next => exact ih values next

/-- A written-order traversal contributes at most one result per arrow row. -/
def sourceRows (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (values : List Value) : List TypeAtom → List TypeAtom
  | [] => []
  | row :: rows =>
      let rest := sourceRows ops reads values rows
      match ops.arrow row with
      | none => rest
      | some (formals, range) =>
          match sourceArgs ops reads formals values ops.initial with
          | none => rest
          | some state => ops.normalize (ops.apply state range) :: rest

def transitionRow (ops : Ops TypeAtom Bind Kind) (children : List (ChildView TypeAtom Kind))
    (row : TypeAtom) : Option TypeAtom :=
  (ops.arrow row).bind fun signature =>
    (transitionArgs ops signature.1 children ops.initial).map fun state =>
      ops.normalize (ops.apply state signature.2)

def transitionRows (ops : Ops TypeAtom Bind Kind) (children : List (ChildView TypeAtom Kind))
    (rows : List TypeAtom) : List TypeAtom := rows.filterMap (transitionRow ops children)

theorem rows_factor (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (values : List Value) (rows : List TypeAtom) :
    sourceRows ops reads values rows = transitionRows ops (values.map (childView reads)) rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [sourceRows, transitionRows, List.filterMap_cons, transitionRow]
      cases arrow : ops.arrow row with
      | none => exact ih
      | some signature =>
          obtain ⟨formals, range⟩ := signature
          dsimp only
          rw [args_factor]
          cases checked : transitionArgs ops formals (values.map (childView reads)) ops.initial with
          | none => simpa [checked, transitionRows] using ih
          | some state =>
              simpa [checked, transitionRows] using congrArg (ops.normalize (ops.apply state range) :: ·) ih

def defaultTypes (ops : Ops TypeAtom Bind Kind) (types : List TypeAtom) : List TypeAtom :=
  if types.isEmpty then [ops.undefined] else ops.close types

/-- The direct C-shaped node traversal, including the special-head,
annotation, first-match application and raw-tuple branches. -/
def sourceNode (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value) : List TypeAtom :=
  match reads.classify head values with
  | .nativeMork => [ops.nativeMork]
  | .listValue => [ops.listType]
  | .ordinary =>
      let annotations := if question then reads.annotations head values else []
      if annotations.isEmpty then
        let rows := reads.headRows head
        if rows.any (fun row => (ops.arrow row).isSome) then sourceRows ops reads values rows
        else
          let choices := reads.tupleHead head :: values.map reads.tuplePart
          defaultTypes ops ((StampInference.product choices).map ops.tuple)
      else match ops.annotationPolicy with
        | .historicalOverride => ops.close annotations
        | .supplement same =>
            let rows := reads.headRows head
            if rows.any (fun row => (ops.arrow row).isSome) then
              supplement same (ops.close annotations) (sourceRows ops reads values rows)
            else ops.close annotations

/-- A transition consumes primitive observations. No field is the complete
root inference; tuple and inferred child questions remain separate. -/
def transition (ops : Ops TypeAtom Bind Kind) (view : Descriptor Value TypeAtom Kind) : List TypeAtom :=
  match view.class_ with
  | .nativeMork => [ops.nativeMork]
  | .listValue => [ops.listType]
  | .ordinary =>
      if view.annotations.isEmpty then
        if view.rows.any (fun row => (ops.arrow row).isSome) then
          transitionRows ops view.children view.rows
        else defaultTypes ops ((StampInference.product
          (view.tupleHead :: view.children.map ChildView.tuplePart)).map ops.tuple)
      else match ops.annotationPolicy with
        | .historicalOverride => ops.close view.annotations
        | .supplement same =>
            if view.rows.any (fun row => (ops.arrow row).isSome) then
              supplement same (ops.close view.annotations) (transitionRows ops view.children view.rows)
            else ops.close view.annotations

/-- The independently specified source traversal factors through all of its
required question-qualified observations, including order and duplicates. -/
theorem node_factor (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value) :
    sourceNode ops reads question head values = transition ops (descriptor reads question head values) := by
  simp only [sourceNode, transition, descriptor, rows_factor, List.map_map]
  rfl

theorem equal_descriptors_equal_results (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    {q q' : Bool} {head head' : Value} {values values' : List Value}
    (same : descriptor reads q head values = descriptor reads q' head' values') :
    sourceNode ops reads q head values = sourceNode ops reads q' head' values' := by
  rw [node_factor, node_factor, same]

structure Header (Value TypeAtom : Type) where
  head : Value
  question : Bool
  class_ : HeadClass
  annotations : List TypeAtom
  rows : List TypeAtom
  tupleHead : List TypeAtom

def Descriptor.header (view : Descriptor Value TypeAtom Kind) : Header Value TypeAtom :=
  ⟨view.head, view.question, view.class_, view.annotations, view.rows, view.tupleHead⟩

def Header.finish (header : Header Value TypeAtom) (children : List (ChildView TypeAtom Kind)) :
    Descriptor Value TypeAtom Kind :=
  ⟨header.head, header.question, header.class_, header.annotations, header.rows, header.tupleHead, children⟩

structure AvailableChild (TypeAtom Kind : Type) where
  kind : Kind
  inferred : Option (List TypeAtom)
  tuplePart : Option (List TypeAtom)

/-- This operation only reads stored options. It has no inference callback
and cannot force a missing view. -/
def AvailableChild.complete (child : AvailableChild TypeAtom Kind) : Option (ChildView TypeAtom Kind) :=
  child.inferred.bind fun inferred => child.tuplePart.map fun tuplePart =>
    ⟨child.kind, inferred, tuplePart⟩

def AvailableChild.Valid (reads : Reads Value TypeAtom Kind) (value : Value)
    (child : AvailableChild TypeAtom Kind) : Prop :=
  child.kind = reads.kind value ∧
    (∀ answer, child.inferred = some answer → answer = reads.inferred value) ∧
    (∀ answer, child.tuplePart = some answer → answer = reads.tuplePart value)

theorem AvailableChild.complete_sound (reads : Reads Value TypeAtom Kind) (value : Value)
    (child : AvailableChild TypeAtom Kind) (valid : child.Valid reads value)
    {view : ChildView TypeAtom Kind} (completed : child.complete = some view) :
    view = childView reads value := by
  cases inferred : child.inferred with
  | none => simp [AvailableChild.complete, inferred] at completed
  | some types =>
      cases tuplePart : child.tuplePart with
      | none => simp [AvailableChild.complete, inferred, tuplePart] at completed
      | some tupleTypes =>
          have viewEq : (⟨child.kind, types, tupleTypes⟩ : ChildView TypeAtom Kind) = view := by
            simpa [AvailableChild.complete, inferred, tuplePart] using completed
          subst view
          simp only [childView, valid.1, valid.2.1 types inferred, valid.2.2 tupleTypes tuplePart]

def completeChildren : List (AvailableChild TypeAtom Kind) → Option (List (ChildView TypeAtom Kind))
  | [] => some []
  | child :: children => child.complete.bind fun view => (completeChildren children).map (view :: ·)

theorem completeChildren_sound (reads : Reads Value TypeAtom Kind) {values : List Value}
    {children : List (AvailableChild TypeAtom Kind)}
    (valid : List.Forall₂ (AvailableChild.Valid reads) values children)
    {views : List (ChildView TypeAtom Kind)} (completed : completeChildren children = some views) :
    views = values.map (childView reads) := by
  induction valid generalizing views with
  | nil => simpa [completeChildren] using completed.symm
  | @cons value child values children head tail ih =>
      cases first : child.complete with
      | none => simp [completeChildren, first] at completed
      | some view =>
          cases rest : completeChildren children with
          | none => simp [completeChildren, first, rest] at completed
          | some remaining =>
              have eq : view :: remaining = views := by simpa [completeChildren, first, rest] using completed
              subst views
              rw [AvailableChild.complete_sound reads value child head first, ih rest]
              rfl

structure Available (Value TypeAtom Kind : Type) where
  header : Header Value TypeAtom
  children : List (AvailableChild TypeAtom Kind)

/-- Shape-key admission misses if any required stored view is absent. It
does not eagerly execute extra type queries, even when they were unused by
the source branch. More selective descriptors can improve this hit rate. -/
def Available.complete (available : Available Value TypeAtom Kind) : Option (Descriptor Value TypeAtom Kind) :=
  (completeChildren available.children).map available.header.finish

def Available.Valid (reads : Reads Value TypeAtom Kind) (question : Bool) (head : Value)
    (values : List Value) (available : Available Value TypeAtom Kind) : Prop :=
  available.header = (descriptor reads question head values).header ∧
    List.Forall₂ (AvailableChild.Valid reads) values available.children

theorem Available.complete_sound (reads : Reads Value TypeAtom Kind) (question : Bool) (head : Value)
    (values : List Value) (available : Available Value TypeAtom Kind)
    (valid : available.Valid reads question head values) {view : Descriptor Value TypeAtom Kind}
    (completed : available.complete = some view) : view = descriptor reads question head values := by
  cases children : completeChildren available.children with
  | none => simp [Available.complete, children] at completed
  | some views =>
      have eq : available.header.finish views = view := by simpa [Available.complete, children] using completed
      subst view
      rw [valid.1, completeChildren_sound reads valid.2 children]
      rfl

def runAvailable (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value) (available : Available Value TypeAtom Kind) :
    List TypeAtom :=
  match available.complete with
  | none => sourceNode ops reads question head values
  | some view => transition ops view

theorem runAvailable_exact (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (question : Bool) (head : Value) (values : List Value) (available : Available Value TypeAtom Kind)
    (valid : available.Valid reads question head values) :
    runAvailable ops reads question head values available = sourceNode ops reads question head values := by
  cases completed : available.complete with
  | none => simp [runAvailable, completed]
  | some view =>
      rw [runAvailable, completed, Available.complete_sound reads question head values available valid completed]
      exact (node_factor ops reads question head values).symm

open Mettapedia.Machines.RevisionedQueryFacts

structure Query (Value : Type) where
  question : Bool
  head : Value
  children : List Value

/-- A cache history may mix revisions; the same stamp chooses the same
pure services and read environment. -/
def cacheRequest {Scope : Type} (reads : Scope → Reads Value TypeAtom Kind)
    (scope : Scope) (query : Query Value) : Request Scope (Descriptor Value TypeAtom Kind) :=
  ⟨scope, descriptor (reads scope) query.question query.head query.children⟩

theorem cache_history_exact {Scope : Type} [DecidableEq Scope]
    [DecidableEq Value] [DecidableEq TypeAtom] [DecidableEq Kind]
    (ops : Scope → Ops TypeAtom Bind Kind) (reads : Scope → Reads Value TypeAtom Kind)
    (queries : List (Scope × Query Value)) :
    (requests (fun scope view => transition (ops scope) view)
      (queries.map fun q => cacheRequest reads q.1 q.2) []).facts =
      queries.map (fun q => sourceNode (ops q.1) (reads q.1) q.2.question q.2.head q.2.children) := by
  rw [requests_exact _ _ _ (valid_nil _), List.map_map]
  apply List.map_congr_left
  intro query _
  exact (node_factor (ops query.1) (reads query.1) query.2.question query.2.head query.2.children).symm

/-- A retained key has one immutable observation within a scope. The round
trip below is a representation obligation, not an inference-correctness
premise. Groundness alone does not establish it for native type payloads. -/
structure Codec (Key Value TypeAtom Kind : Type) where
  retain : Descriptor Value TypeAtom Kind → Option Key
  observe : Key → Option (Descriptor Value TypeAtom Kind)

def Codec.Lawful {Key : Type} (codec : Codec Key Value TypeAtom Kind) : Prop :=
  ∀ view key, codec.retain view = some key → codec.observe key = some view

theorem retained_key_source_congr {Key : Type} (codec : Codec Key Value TypeAtom Kind)
    (lawful : codec.Lawful) (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind)
    (left right : Query Value) (key : Key)
    (hl : codec.retain (descriptor reads left.question left.head left.children) = some key)
    (hr : codec.retain (descriptor reads right.question right.head right.children) = some key) :
    sourceNode ops reads left.question left.head left.children =
      sourceNode ops reads right.question right.head right.children := by
  apply equal_descriptors_equal_results
  exact Option.some.inj ((lawful _ _ hl).symm.trans (lawful _ _ hr))

def retainedCompute {Key : Type} (ops : Ops TypeAtom Bind Kind)
    (codec : Codec Key Value TypeAtom Kind) (key : Key) : List TypeAtom :=
  ((codec.observe key).map (transition ops)).getD []

/-- Retaining and retrieving through a stable codec preserves a mixed-scope
cache history. Native interning must implement this codec contract; the
theorem does not infer it from hashes, pointer identities or variable absence. -/
theorem retained_cache_history_exact {Scope Key : Type} [DecidableEq Scope] [DecidableEq Key]
    (ops : Scope → Ops TypeAtom Bind Kind) (reads : Scope → Reads Value TypeAtom Kind)
    (codec : Scope → Codec Key Value TypeAtom Kind) (lawful : ∀ scope, (codec scope).Lawful)
    (queries : List (Scope × Query Value × Key))
    (published : ∀ item ∈ queries, (codec item.1).retain
      (descriptor (reads item.1) item.2.1.question item.2.1.head item.2.1.children) = some item.2.2) :
    (requests (fun scope key => retainedCompute (ops scope) (codec scope) key)
      (queries.map fun q => ⟨q.1, q.2.2⟩) []).facts =
      queries.map (fun q => sourceNode (ops q.1) (reads q.1)
        q.2.1.question q.2.1.head q.2.1.children) := by
  rw [requests_exact _ _ _ (valid_nil _), List.map_map]
  apply List.map_congr_left
  intro query hquery
  have observed := lawful query.1 _ _ (published query hquery)
  simp only [Function.comp_apply, retainedCompute, observed, Option.map_some, Option.getD_some]
  exact (node_factor (ops query.1) (reads query.1)
    query.2.1.question query.2.1.head query.2.1.children).symm

/-- The previous Ty-based matcher is an instance of the carrier-generic
driver. This bridge preserves its argument and row semantics. -/
def legacyOps (matcher : StampInference.Matcher Bind) : Ops (Ty String) Bind String where
  arrow := arrowSplit
  initial := matcher.initial
  apply := matcher.apply
  unify := matcher.unify
  metaCheck := StampInference.metaCheck
  normalize := matcher.normalize
  tuple := Ty.app
  undefined := undefinedTy
  nativeMork := .sym "MorkSpace"
  listType := .sym "List"
  subtypeAdditions := fun _ => []

def legacyChild (child : StampInference.Stamp) : ChildView (Ty String) String :=
  ⟨child.kind, child.types, StampInference.tuplePart false child.types⟩

theorem args_legacy (matcher : StampInference.Matcher Bind) (formals : List (Ty String)) :
    ∀ (children : List StampInference.Stamp) (state : Bind),
      transitionArgs (legacyOps matcher) formals (children.map legacyChild) state =
        StampInference.checkArgs matcher formals children state := by
  induction formals with
  | nil => intro children state; cases children <;> rfl
  | cons formal formals ih =>
      intro children state
      cases children with
      | nil => rfl
      | cons child children =>
          simp only [transitionArgs, List.map_cons, legacyOps, legacyChild, StampInference.checkArgs]
          cases metatype : StampInference.metaCheck (matcher.apply state formal) child.kind with
          | some answer =>
              cases answer with
              | false => rfl
              | true => exact ih children state
          | none =>
              cases chosen : StampInference.firstResult
                  (fun actual => matcher.unify state actual (matcher.apply state formal)) child.types with
              | none => rfl
              | some next => exact ih children next

theorem row_legacy (matcher : StampInference.Matcher Bind) (children : List StampInference.Stamp)
    (row : Ty String) :
    transitionRow (legacyOps matcher) (children.map legacyChild) row =
      StampInference.rowResult matcher children row := by
  simp only [transitionRow, legacyOps, StampInference.rowResult]
  cases arrow : arrowSplit row with
  | none => rfl
  | some signature =>
      obtain ⟨formals, range⟩ := signature
      change (transitionArgs (legacyOps matcher) formals (children.map legacyChild)
        matcher.initial).map (fun state => matcher.normalize (matcher.apply state range)) = _
      rw [args_legacy]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViews
