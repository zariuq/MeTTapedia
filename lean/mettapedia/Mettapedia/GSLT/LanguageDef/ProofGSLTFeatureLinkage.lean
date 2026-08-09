import Mathlib.Data.Finset.Basic

/-!
# Affine feature linkage for proof-GSLT components

This module isolates one optional composition discipline for components that
advertise named input and output features.  It is deliberately separate from
rule-table joins and proof-theory interpretations: not every proof GSLT has an
affine interface.

Gluing combines endpoints subject only to global at-most-one producer and
at-most-one consumer constraints.  Open inputs are legal in intermediate
components.  Ordering and closure are checked on the completed component
sequence, so they cannot make a bracketing inadmissible merely because an
enclosing component supplies an input.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.FeatureLinkage

variable {Feature : Type*} [DecidableEq Feature]

/-- The complete endpoint inventory of one component or composite.  Finsets
encode the affine multiplicity invariant after authoring-time duplicate
validation. -/
@[ext] structure Endpoints (Feature : Type*) where
  producers : Finset Feature
  consumers : Finset Feature
deriving DecidableEq

namespace Endpoints

/-- Two endpoint inventories can be glued when neither introduces a second
writer or a second reader for any channel. -/
def Composable (left right : Endpoints Feature) : Prop :=
  Disjoint left.producers right.producers ∧
    Disjoint left.consumers right.consumers

/-- Combine two endpoint inventories.  This operation is total as data;
`Composable` is the admission predicate for using it as affine linkage. -/
def glue (left right : Endpoints Feature) : Endpoints Feature :=
  { producers := left.producers ∪ right.producers
    consumers := left.consumers ∪ right.consumers }

/-- The empty component is the linkage unit. -/
def empty : Endpoints Feature :=
  { producers := ∅, consumers := ∅ }

/-- Reads not supplied anywhere in the composite. -/
def imports (component : Endpoints Feature) : Finset Feature :=
  component.consumers \ component.producers

/-- Writes not consumed anywhere in the composite. -/
def exports (component : Endpoints Feature) : Finset Feature :=
  component.producers \ component.consumers

/-- A completed composite has no unsupplied reads. -/
def Closed (component : Endpoints Feature) : Prop :=
  component.imports = ∅

@[simp] theorem glue_producers (left right : Endpoints Feature) :
    (left.glue right).producers = left.producers ∪ right.producers := rfl

@[simp] theorem glue_consumers (left right : Endpoints Feature) :
    (left.glue right).consumers = left.consumers ∪ right.consumers := rfl

@[simp] theorem glue_empty_left (component : Endpoints Feature) :
    empty.glue component = component := by
  ext <;> simp [empty, glue]

@[simp] theorem glue_empty_right (component : Endpoints Feature) :
    component.glue empty = component := by
  ext <;> simp [empty, glue]

/-- Endpoint gluing is associative as data.  Provenance may still retain a
particular component tree; this theorem concerns the semantic interface. -/
theorem glue_assoc (first second third : Endpoints Feature) :
    (first.glue second).glue third =
      first.glue (second.glue third) := by
  ext <;> simp [glue, Finset.union_assoc]

omit [DecidableEq Feature] in
theorem composable_comm {left right : Endpoints Feature} :
    left.Composable right ↔ right.Composable left := by
  simp only [Composable]
  constructor <;> rintro ⟨hp, hc⟩ <;>
    exact ⟨Disjoint.symm hp, Disjoint.symm hc⟩

/-- The affine side condition is independent of binary bracketing. -/
theorem composable_assoc_iff
    (first second third : Endpoints Feature) :
    (first.Composable second ∧
        (first.glue second).Composable third) ↔
      (second.Composable third ∧
        first.Composable (second.glue third)) := by
  simp only [Composable, glue_producers, glue_consumers]
  simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
  tauto

@[simp] theorem imports_empty : (empty : Endpoints Feature).imports = ∅ := by
  simp [imports, empty]

@[simp] theorem exports_empty : (empty : Endpoints Feature).exports = ∅ := by
  simp [exports, empty]

@[simp] theorem closed_iff_consumers_subset_producers
    (component : Endpoints Feature) :
    component.Closed ↔ component.consumers ⊆ component.producers := by
  simp [Closed, imports, Finset.sdiff_eq_empty_iff_subset]

end Endpoints

/-! ## Authoring-time duplicate validation -/

/-- Raw authored endpoints retain multiplicity so duplicate declarations can
be rejected rather than silently collapsed by `Finset`. -/
structure AuthoredEndpoints (Feature : Type*) where
  producers : List Feature
  consumers : List Feature

namespace AuthoredEndpoints

/-- The authored representation satisfies the affine multiplicity policy. -/
def Affine (raw : AuthoredEndpoints Feature) : Prop :=
  raw.producers.Nodup ∧ raw.consumers.Nodup

/-- Forget ordering only after affine multiplicity has been validated. -/
def validate (raw : AuthoredEndpoints Feature) (valid : raw.Affine) :
    Endpoints Feature :=
  { producers := ⟨raw.producers, valid.1⟩
    consumers := ⟨raw.consumers, valid.2⟩ }

/-- Positive authoring canary: one writer and one reader are admitted. -/
example (feature : Feature) :
    (AuthoredEndpoints.mk [feature] [feature]).Affine := by
  simp [Affine]

omit [DecidableEq Feature] in
/-- Negative authoring canary: a repeated writer is rejected. -/
theorem duplicateProducer_not_affine (feature : Feature) :
    ¬(AuthoredEndpoints.mk [feature, feature] []).Affine := by
  simp [Affine]

omit [DecidableEq Feature] in
/-- Negative authoring canary: a repeated reader is rejected. -/
theorem duplicateConsumer_not_affine (feature : Feature) :
    ¬(AuthoredEndpoints.mk [] [feature, feature]).Affine := by
  simp [Affine]

end AuthoredEndpoints

/-! ## Ordering belongs to the finished sequence -/

/-- Every read in a component is supplied by an earlier component.  This is a
property of a completed ordered sequence, not a binary composability gate. -/
def ProducerBeforeConsumer :
    List (Endpoints Feature) → Prop
  | [] => True
  | component :: rest =>
      component.consumers = ∅ ∧
        ProducerBeforeConsumer
          (rest.map fun later =>
            { later with
              consumers := later.consumers \ component.producers })
termination_by components => components.length
decreasing_by simp_wf

/-- Flatten an ordered component sequence without imposing ordering or closure
during intermediate gluing. -/
def glueAll : List (Endpoints Feature) → Endpoints Feature
  | [] => Endpoints.empty
  | component :: rest => component.glue (glueAll rest)

@[simp] theorem glueAll_nil :
    glueAll ([] : List (Endpoints Feature)) = Endpoints.empty := rfl

@[simp] theorem glueAll_cons (component : Endpoints Feature)
    (rest : List (Endpoints Feature)) :
    glueAll (component :: rest) = component.glue (glueAll rest) := rfl

/-- Flattening concatenated sequences agrees with endpoint gluing. -/
theorem glueAll_append (left right : List (Endpoints Feature)) :
    glueAll (left ++ right) = (glueAll left).glue (glueAll right) := by
  induction left with
  | nil => simp
  | cons component rest ih =>
      simp only [List.cons_append, glueAll_cons, ih]
      exact (Endpoints.glue_assoc (Feature := Feature) _ _ _).symm

section Canaries

variable (feature : Feature)

private def writer : Endpoints Feature :=
  { producers := {feature}, consumers := ∅ }

private def reader : Endpoints Feature :=
  { producers := ∅, consumers := {feature} }

/-- An open reader is legal linkage data; closure is intentionally deferred. -/
theorem openReader_not_closed :
    ¬(reader feature).Closed := by
  simp [reader, Endpoints.Closed, Endpoints.imports]

/-- Supplying the open reader from an earlier component closes the completed
composite. -/
theorem writer_reader_closed :
    ((writer feature).glue (reader feature)).Closed := by
  rw [Endpoints.closed_iff_consumers_subset_producers]
  intro candidate member
  simpa [writer, reader, Endpoints.glue] using member

/-- The same completed sequence satisfies the ordering discipline. -/
theorem writer_before_reader :
    ProducerBeforeConsumer [writer feature, reader feature] := by
  simp [ProducerBeforeConsumer, writer, reader]

/-- Reversing the sequence is closed extensionally but violates the authored
producer-before-consumer discipline. -/
theorem reader_before_writer_rejected :
    ¬ProducerBeforeConsumer [reader feature, writer feature] := by
  simp [ProducerBeforeConsumer, writer, reader]

end Canaries

end Mettapedia.GSLT.LanguageDef.ProofGSLT.FeatureLinkage
