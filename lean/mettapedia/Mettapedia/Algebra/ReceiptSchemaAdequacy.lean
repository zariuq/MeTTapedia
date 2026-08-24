import Mettapedia.Algebra.WorkSpanInformationLoss

/-!
# What a receipt must carry to support exact replay

A receipt is a projection of an execution.  Replay compares receipts, so a
receipt determines exactly as much as its schema records — no more.  The
cost-layer iteration non-factorization results say compact syntax is an unsound key for
cost-bearing normalization; this module states the corresponding contract
at the receipt boundary, so that a replay checker's schema requirement is
a theorem rather than a convention.

The shape is uniform.  A schema is a projection `Execution → Record`.
It **separates** two executions when their records differ, and **conflates**
them when the records agree.  A checker built on a schema can distinguish
exactly the executions that schema separates — so any attribute the schema
omits is an attribute replay cannot check.

The practical reading, for the Prime/NIK replay path: a receipt that omits
colour, declaration identity, boundary evidence, or elaboration path
cannot detect a swap in that field.  The provenance-swap fixture is
therefore a genuine tamper test, not a formality.
-/

namespace Mettapedia.Algebra

namespace ReceiptSchema

/-- A schema is a projection from executions to recorded data. -/
abbrev Schema (Execution Record : Type) := Execution → Record

/-- A schema separates two executions when it records a difference. -/
def Separates {Execution Record : Type} (schema : Schema Execution Record)
    (left right : Execution) : Prop :=
  schema left ≠ schema right

/-- A checker deciding equality of records accepts exactly the pairs the
schema conflates.  This is the whole content of "replay compares
receipts". -/
def ChecksAsEqual {Execution Record : Type}
    (schema : Schema Execution Record) (left right : Execution) : Prop :=
  schema left = schema right

theorem checksAsEqual_iff_not_separates {Execution Record : Type}
    (schema : Schema Execution Record) (left right : Execution) :
    ChecksAsEqual schema left right ↔ ¬ Separates schema left right := by
  unfold ChecksAsEqual Separates
  exact ⟨fun equal contra => contra equal, fun notNe => not_not.mp notNe⟩

/-- **Omission is undetectability.**  If a schema factors through a
projection that forgets an attribute, then executions differing only in
that attribute are accepted as equal — the checker cannot see the
difference. -/
theorem omitted_attribute_undetectable {Execution Record Attribute : Type}
    (schema : Schema Execution Record)
    (observe : Execution → Attribute)
    {left right : Execution}
    (conflated : schema left = schema right)
    (differs : observe left ≠ observe right) :
    ChecksAsEqual schema left right ∧ observe left ≠ observe right :=
  ⟨conflated, differs⟩

/-- **The schema requirement, positively.**  A schema that records an
attribute separates every pair the attribute separates: recording is
sufficient for detection. -/
theorem recorded_attribute_detectable {Execution Attribute : Type}
    (observe : Execution → Attribute) {left right : Execution}
    (differs : observe left ≠ observe right) :
    Separates observe left right :=
  differs

/-- A schema built as a tuple of field projections separates a pair as soon
as **any** recorded field differs.  This is the composition law a receipt
schema needs: adding fields never loses detection power. -/
theorem tuple_separates_of_left {Execution First Second : Type}
    (firstField : Execution → First) (secondField : Execution → Second)
    {left right : Execution}
    (differs : firstField left ≠ firstField right) :
    Separates (fun execution => (firstField execution, secondField execution))
      left right := by
  intro equal
  exact differs (congrArg Prod.fst equal)

theorem tuple_separates_of_right {Execution First Second : Type}
    (firstField : Execution → First) (secondField : Execution → Second)
    {left right : Execution}
    (differs : secondField left ≠ secondField right) :
    Separates (fun execution => (firstField execution, secondField execution))
      left right := by
  intro equal
  exact differs (congrArg Prod.snd equal)

/-- **Dropping a field can only lose detection.**  If the reduced schema
separates a pair then so does the full one; the converse fails exactly at
pairs the dropped field distinguished. -/
theorem drop_field_monotone {Execution First Second : Type}
    (firstField : Execution → First) (secondField : Execution → Second)
    {left right : Execution}
    (reducedSeparates : Separates firstField left right) :
    Separates (fun execution => (firstField execution, secondField execution))
      left right :=
  tuple_separates_of_left firstField secondField reducedSeparates

/-- **The tamper test is genuine.**  Two executions agreeing on every
recorded field except a dropped one are accepted by the reduced checker
and rejected by the full one.  A provenance-swap fixture therefore
distinguishes a compliant replay checker from a non-compliant one. -/
theorem dropped_field_admits_tamper {Execution First Second : Type}
    (firstField : Execution → First) (secondField : Execution → Second)
    {left right : Execution}
    (agreeOnKept : firstField left = firstField right)
    (differOnDropped : secondField left ≠ secondField right) :
    ChecksAsEqual firstField left right ∧
      Separates (fun execution =>
        (firstField execution, secondField execution)) left right :=
  ⟨agreeOnKept, tuple_separates_of_right firstField secondField
    differOnDropped⟩

end ReceiptSchema

end Mettapedia.Algebra
