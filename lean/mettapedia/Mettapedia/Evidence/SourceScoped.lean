import Mettapedia.Evidence.SourceScope

/-!
# Evidence objects with retained source scope

Many evidential systems retain a finite set of source occurrences while
disagreeing about their truth values, inference rules, and conflict policies.
This module isolates only that shared interface.  It does not choose an
evidence carrier or license any particular merge operation.

NARS path-scoped beliefs and PLN stamped evidence are instances.  Their common
independence test is therefore a theorem about retained source identity rather
than an identification of the two reasoning systems.
-/

namespace Mettapedia.Evidence

universe uSource uPacket uLeftPacket uRightPacket

/-- An evidence-bearing object whose finite source-occurrence scope can be
inspected.  The source type is an output parameter because a packet normally
has one canonical provenance vocabulary. -/
class SourceScoped (Packet : Type uPacket) (Source : outParam (Type uSource)) where
  sourceScope : Packet → Finset Source

export SourceScoped (sourceScope)

namespace SourceScoped

variable {Packet : Type uPacket} {LeftPacket : Type uLeftPacket}
  {RightPacket : Type uRightPacket} {Source : Type uSource}
  [DecidableEq Source]

/-- Two packets are source-independent when their retained scopes are
disjoint.  The packets may have different carrier types; only their source
vocabulary is shared. -/
def Independent [SourceScoped LeftPacket Source] [SourceScoped RightPacket Source]
    (left : LeftPacket) (right : RightPacket) : Prop :=
  SourceScope.Independent (sourceScope left) (sourceScope right)

instance instDecidableIndependent
    [SourceScoped LeftPacket Source] [SourceScoped RightPacket Source]
    (left : LeftPacket) (right : RightPacket) :
    Decidable (Independent left right) := by
  unfold Independent
  infer_instance

/-- A packet family is source-independent when every earlier/later pair is
source-independent. -/
def FamilyIndependent [SourceScoped Packet Source] (packets : List Packet) : Prop :=
  packets.Pairwise Independent

omit [DecidableEq Source] in
theorem independent_iff_scope_independent
    [SourceScoped LeftPacket Source] [SourceScoped RightPacket Source]
    (left : LeftPacket) (right : RightPacket) :
    Independent left right ↔
      SourceScope.Independent (sourceScope left) (sourceScope right) :=
  Iff.rfl

omit [DecidableEq Source] in
theorem independent_comm
    [SourceScoped LeftPacket Source] [SourceScoped RightPacket Source]
    (left : LeftPacket) (right : RightPacket) :
    Independent left right ↔ Independent right left := by
  exact SourceScope.independent_comm (sourceScope left) (sourceScope right)

omit [DecidableEq Source] in
theorem independent_self_iff_scope_eq_empty [SourceScoped Packet Source]
    (packet : Packet) :
    Independent packet packet ↔ sourceScope packet = ∅ := by
  exact SourceScope.independent_self_iff_eq_empty (sourceScope packet)

omit [DecidableEq Source] in
theorem not_independent_of_shared_source
    [SourceScoped LeftPacket Source] [SourceScoped RightPacket Source]
    {left : LeftPacket} {right : RightPacket} {source : Source}
    (left_mem : source ∈ sourceScope left)
    (right_mem : source ∈ sourceScope right) :
    ¬ Independent left right := by
  exact SourceScope.not_independent_of_mem left_mem right_mem

/-! ## Interface canaries -/

namespace Examples

structure ExamplePacket where
  label : Nat
  sources : Finset (Fin 3)

structure OtherPacket where
  explanation : String
  sources : Finset (Fin 3)

instance : SourceScoped ExamplePacket (Fin 3) where
  sourceScope := ExamplePacket.sources

instance : SourceScoped OtherPacket (Fin 3) where
  sourceScope := OtherPacket.sources

def left : ExamplePacket := ⟨10, {0}⟩
def right : ExamplePacket := ⟨20, {1, 2}⟩
def overlapping : ExamplePacket := ⟨30, {0, 2}⟩
def otherRight : OtherPacket := ⟨"different carrier", {1, 2}⟩
def otherOverlapping : OtherPacket := ⟨"shared source", {0, 2}⟩

/-- Positive canary: payload identity is irrelevant when source scopes are
disjoint. -/
theorem left_right_independent : Independent left right := by
  decide

/-- Negative canary: different payloads do not make a shared source
independent. -/
theorem left_overlapping_not_independent : ¬ Independent left overlapping := by
  decide

/-- Positive heterogeneous canary: independence compares provenance rather
than requiring both evidence systems to share one packet representation. -/
theorem left_otherRight_independent : Independent left otherRight := by
  decide

/-- Negative heterogeneous canary: changing the packet representation cannot
hide a shared source occurrence. -/
theorem left_otherOverlapping_not_independent :
    ¬ Independent left otherOverlapping := by
  decide

end Examples

#print axioms independent_self_iff_scope_eq_empty
#print axioms Examples.left_right_independent
#print axioms Examples.left_overlapping_not_independent
#print axioms Examples.left_otherRight_independent
#print axioms Examples.left_otherOverlapping_not_independent

end SourceScoped
end Mettapedia.Evidence
