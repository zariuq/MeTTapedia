import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.TypeTheory.ExtensionalReadout

/-!
# Occurrence support and type extents

This module formalizes one small boundary: set-valued observations of
occurrence bags and intensional typing evidence.  It does **not** define an
object-language set theory, and it does not characterize a future `set:`
service.  A foundational set authority such as Egal/HOTG additionally has its
own syntax, membership relation, logic, theory environment, proof objects,
native checking kernel, and semantic adequacy obligations.  Those structures
are orthogonal to the support map proved here.

Three objects that are often called a "space" must remain distinct.

* An occurrence space is a multiset.  It remembers how many copies of an
  atom are present.
* The support of an occurrence space is a set-level observation.  It remembers
  only whether an atom is present.
* A type interpretation assigns an extensional set of atoms to each type code,
  while retaining an intensional evidence type for the typing judgment.

The bridges are directional.  A typing witness maps to membership in its
extent, but the reverse requires a separate completeness property.  A typed
occurrence maps to the intersection of space support and type extent.  Bag
addition maps to set union, but the map is not faithful because multiplicity
is lost.  Likewise, equality of type codes maps to equality of extents, while
the converse requires a separate faithfulness property.

These distinctions make the intended division of labor precise: storage and
search may remain occurrence-sensitive, selected observations may use support
or type extents, and type-level operations retain their evidence.  Nothing in
this module reduces general set-theoretic mathematics to those observations.
No choice of dependent type theory, object-language set theory, revision
algebra, or surface namespace is fixed here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.OccurrenceSpaceTypeExtent

open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.TypeTheory.ExtensionalReadout

universe uAtom uCode uEvidence uRevision

/-! ## Intensional typing evidence with an extensional readout -/

/-- A type interpretation with proof-relevant typing evidence and a set-valued
readout.  `sound` is deliberately one-way: extensional membership need not
construct an intensional typing witness. -/
structure TypeExtentSemantics
    (Atom : Type uAtom) (Code : Type uCode) where
  Evidence : Atom -> Code -> Type uEvidence
  extent : Code -> Set Atom
  sound : forall {atom code}, Evidence atom code -> atom ∈ extent code

namespace TypeExtentSemantics

variable {Atom : Type uAtom} {Code : Type uCode}
variable (semantics : TypeExtentSemantics.{uAtom, uCode, uEvidence} Atom Code)

/-- Extensional membership is complete for typing evidence.  This is extra
structure, not part of the definition of a type extent. -/
def Complete : Prop :=
  forall {atom code}, atom ∈ semantics.extent code ->
    Nonempty (semantics.Evidence atom code)

/-- The extensional interpretation distinguishes all type codes. -/
def ExtentFaithful : Prop := Function.Injective semantics.extent

/-- The represented type fragment is closed under extensional union.  The
existence of set union alone does not imply this property. -/
def UnionClosed : Prop :=
  forall left right, exists joined,
    semantics.extent joined =
      semantics.extent left ∪ semantics.extent right

/-- Equality of intensional codes always has equal extensional readout. -/
theorem extent_eq_of_code_eq {left right : Code} (equal : left = right) :
    semantics.extent left = semantics.extent right :=
  congrArg semantics.extent equal

/-- Extensional equality reflects code equality exactly when the
interpretation is faithful. -/
theorem code_eq_of_extent_eq (faithful : semantics.ExtentFaithful)
    {left right : Code}
    (equal : semantics.extent left = semantics.extent right) : left = right :=
  faithful equal

end TypeExtentSemantics

/-! ## Occurrence bags and their support -/

/-- A finite occurrence-sensitive space. -/
abbrev OccurrenceSpace (Atom : Type uAtom) := Multiset Atom

variable {Atom : Type uAtom} {Code : Type uCode}

/-- The finite set-level observation of an occurrence space. -/
noncomputable def support [DecidableEq Atom]
    (space : OccurrenceSpace Atom) : Finset Atom :=
  space.toFinset

/-- The atoms both present in an occurrence space and belonging to a type
extent.  This is a set-level query result, not a replacement for occurrence
or typing evidence. -/
def typedSupport [DecidableEq Atom]
    (semantics : TypeExtentSemantics.{uAtom, uCode, uEvidence} Atom Code)
    (space : OccurrenceSpace Atom) (code : Code) : Set Atom :=
  { atom | atom ∈ support space ∧ atom ∈ semantics.extent code }

/-- Bag addition becomes union after taking finite support. -/
theorem support_add [DecidableEq Atom]
    (left right : OccurrenceSpace Atom) :
    support (left + right) = support left ∪ support right := by
  classical
  exact Multiset.toFinset_add left right

/-- The occurrence-to-support map is exactly the already-lawful GSLT answer
effect morphism from bags to finite support.  Thus the bridge preserves empty
answers, choice, singleton answers, and dependent sequencing; it is not merely
an isolated coincidence about union. -/
theorem support_eq_bagToSupport_map [DecidableEq Atom]
    (space : OccurrenceSpace Atom) :
    support space = bagToSupport.map space := by
  classical
  simp [support]

/-- Typed support distributes over occurrence-space addition. -/
theorem typedSupport_add [DecidableEq Atom]
    (semantics : TypeExtentSemantics.{uAtom, uCode, uEvidence} Atom Code)
    (left right : OccurrenceSpace Atom) (code : Code) :
    typedSupport semantics (left + right) code =
      typedSupport semantics left code ∪ typedSupport semantics right code := by
  classical
  ext atom
  simp only [typedSupport, Set.mem_setOf_eq, Set.mem_union,
    support, Multiset.mem_toFinset, Multiset.mem_add]
  tauto

/-! ## Revisioned support is a split, lossy observation -/

/-- A revision label and its occurrence bag.  No algebra on revisions is
assumed, so there is intentionally no canonical addition on snapshots. -/
structure Snapshot (Revision : Type uRevision) (Atom : Type uAtom) where
  revision : Revision
  occurrences : OccurrenceSpace Atom

namespace Snapshot

variable {Revision : Type uRevision} {Atom : Type uAtom}

/-- Support keeps the revision label while forgetting occurrence
multiplicity. -/
noncomputable def supportPacket [DecidableEq Atom]
    (snapshot : Snapshot Revision Atom) : Revision × Finset Atom :=
  (snapshot.revision, support snapshot.occurrences)

/-- A canonical duplicate-free representative of a revisioned support
packet. -/
def ofSupportPacket (packet : Revision × Finset Atom) :
    Snapshot Revision Atom where
  revision := packet.1
  occurrences := packet.2.1

/-- Revisioned finite support is a split extensional readout of revisioned
occurrence bags. -/
noncomputable def supportReadout [DecidableEq Atom] :
    SplitReadout (Snapshot Revision Atom) (Revision × Finset Atom) := by
  classical
  exact
    { observe := supportPacket
      representative := ofSupportPacket
      observe_representative := by
        rintro ⟨revision, atoms⟩
        simp [supportPacket, ofSupportPacket, support] }

/-- Revision is retained by the support packet. -/
def revisionObserver (snapshot : Snapshot Revision Atom) : Revision :=
  snapshot.revision

/-- Total multiplicity observes information discarded by support. -/
def multiplicityObserver (snapshot : Snapshot Revision Atom) : Nat :=
  snapshot.occurrences.card

end Snapshot

/-! ## Typed occurrences retain both kinds of evidence -/

/-- One selected occurrence together with evidence that its atom has the
declared type.  The occurrence index distinguishes duplicate copies. -/
structure TypedOccurrence [DecidableEq Atom]
    (semantics : TypeExtentSemantics.{uAtom, uCode, uEvidence} Atom Code)
    (space : OccurrenceSpace Atom) (code : Code) where
  atom : Atom
  occurrence : Nat
  occurrence_lt_count : occurrence < Multiset.count atom space
  typing : semantics.Evidence atom code

namespace TypedOccurrence

variable {Atom : Type uAtom} {Code : Type uCode}
variable [DecidableEq Atom]
variable {semantics : TypeExtentSemantics.{uAtom, uCode, uEvidence} Atom Code}
variable {space : OccurrenceSpace Atom} {code : Code}

/-- Erasing a typed occurrence lands in the intersection of current support
and the declared type extent. -/
theorem mem_typedSupport (witness : TypedOccurrence semantics space code) :
    witness.atom ∈ typedSupport semantics space code := by
  constructor
  · simpa [support] using
      (Multiset.count_pos.mp
        (Nat.zero_lt_of_lt witness.occurrence_lt_count))
  · exact semantics.sound witness.typing

/-- Conversely, a point of typed support yields a typed occurrence only when
extensional membership is complete for intensional typing evidence. -/
theorem exists_of_mem_typedSupport
    (complete : semantics.Complete) {atom : Atom}
    (member : atom ∈ typedSupport semantics space code) :
    Nonempty (Subtype (fun witness : TypedOccurrence semantics space code =>
      witness.atom = atom)) := by
  rcases member with ⟨present, typed⟩
  rcases complete typed with ⟨typing⟩
  have presentInBag : atom ∈ space := by
    simpa [support] using present
  exact ⟨⟨
    { atom := atom
      occurrence := 0
      occurrence_lt_count := Multiset.count_pos.mpr presentInBag
      typing := typing },
    rfl⟩⟩

end TypedOccurrence

/-! ## Separating examples -/

namespace Canary

/-- Each Boolean type code denotes its singleton. -/
def singletonSemantics : TypeExtentSemantics Bool Bool where
  Evidence atom code := Subtype (fun _ : Unit => atom = code)
  extent code := { atom | atom = code }
  sound evidence := evidence.property

/-- Although unions of extents exist as sets, this two-code type language has
no code for the union of its two singleton extents. -/
theorem singletonSemantics_not_unionClosed :
    ¬ singletonSemantics.UnionClosed := by
  intro closed
  rcases closed false true with ⟨joined, equal⟩
  have falseMember : false ∈ singletonSemantics.extent joined := by
    rw [equal]
    simp [singletonSemantics]
  have trueMember : true ∈ singletonSemantics.extent joined := by
    rw [equal]
    simp [singletonSemantics]
  exact Bool.false_ne_true (falseMember.trans trueMember.symm)

/-- Two distinct codes may deliberately have the same extent. -/
def coincidentSemantics : TypeExtentSemantics Unit Bool where
  Evidence _ _ := Unit
  extent _ := Set.univ
  sound _ := Set.mem_univ _

/-- Set equality therefore does not in general reflect type-code equality. -/
theorem coincident_extents_do_not_reflect_codes :
    coincidentSemantics.extent false = coincidentSemantics.extent true ∧
      false ≠ true :=
  ⟨rfl, Bool.false_ne_true⟩

/-- A sound extent can contain more atoms than the intensional typing system
can witness. -/
def incompleteSemantics : TypeExtentSemantics Bool Unit where
  Evidence atom _ := Subtype (fun _ : Unit => atom = false)
  extent _ := Set.univ
  sound _ := Set.mem_univ _

/-- Soundness alone does not manufacture completeness. -/
theorem incompleteSemantics_not_complete :
    ¬ incompleteSemantics.Complete := by
  intro complete
  rcases complete (atom := true) (code := ()) (by
    change true ∈ (Set.univ : Set Bool)
    exact Set.mem_univ true) with
    ⟨evidence⟩
  exact Bool.false_ne_true evidence.property.symm

/-- A typing judgment may have multiple proofs even when its extent is a
single extensional fact. -/
def proofRelevantSemantics : TypeExtentSemantics Unit Unit where
  Evidence _ _ := Bool
  extent _ := Set.univ
  sound _ := Set.mem_univ _

abbrev ProofRelevantWitness :=
  Sigma (fun atom => proofRelevantSemantics.Evidence atom ())

def firstTypingWitness : ProofRelevantWitness := ⟨(), false⟩
def secondTypingWitness : ProofRelevantWitness := ⟨(), true⟩

/-- Extensional erasure identifies two genuinely distinct typing witnesses. -/
theorem typing_evidence_is_not_extent_membership :
    firstTypingWitness ≠ secondTypingWitness ∧
      firstTypingWitness.1 = secondTypingWitness.1 := by
  constructor
  · intro equal
    have evidenceEqual : false = true :=
      congrArg (fun witness : ProofRelevantWitness => witness.2) equal
    exact Bool.false_ne_true evidenceEqual
  · rfl

def oneSnapshot : Snapshot Unit Unit where
  revision := ()
  occurrences := {()}

def twoSnapshot : Snapshot Unit Unit where
  revision := ()
  occurrences := {(), ()}

/-- Revisioned support forgets multiplicity and is therefore not faithful. -/
theorem snapshotSupportReadout_not_faithful :
    ¬ (Snapshot.supportReadout (Revision := Unit)
      (Atom := Unit)).Faithful := by
  intro faithful
  have equalSnapshots : oneSnapshot = twoSnapshot := faithful (by
    change ((), ({()} : Multiset Unit).toFinset) =
      ((), ({(), ()} : Multiset Unit).toFinset)
    simp)
  have equalCards := congrArg
    (fun snapshot : Snapshot Unit Unit => snapshot.occurrences.card)
    equalSnapshots
  norm_num [oneSnapshot, twoSnapshot] at equalCards

/-- Multiplicity cannot be reconstructed as an observer of finite support. -/
theorem multiplicity_does_not_descend_to_support :
    ¬ (Snapshot.supportReadout (Revision := Unit)
      (Atom := Unit)).FactorsObserver Snapshot.multiplicityObserver := by
  rw [(Snapshot.supportReadout (Revision := Unit)
    (Atom := Unit)).factorsObserver_iff_fibreInvariant]
  intro invariant
  have equalMultiplicity := invariant
    (left := oneSnapshot) (right := twoSnapshot) (by
      change ((), ({()} : Multiset Unit).toFinset) =
        ((), ({(), ()} : Multiset Unit).toFinset)
      simp)
  norm_num [Snapshot.multiplicityObserver, oneSnapshot, twoSnapshot]
    at equalMultiplicity

/-- The support readout does retain revision identity. -/
theorem revision_descends_to_support :
    (Snapshot.supportReadout (Revision := Bool)
      (Atom := Unit)).FactorsObserver Snapshot.revisionObserver := by
  refine ⟨Prod.fst, ?_⟩
  intro snapshot
  rfl

def trueOnlySpace : OccurrenceSpace Bool := {true}
def falseOnlySpace : OccurrenceSpace Bool := {false}

/-- Storage presence and type membership are independent: a stored atom can
fall outside an extent, and an atom in an extent can be absent from storage. -/
theorem storage_and_typing_are_orthogonal :
    true ∈ support trueOnlySpace ∧
      true ∉ singletonSemantics.extent false ∧
      true ∈ singletonSemantics.extent true ∧
      true ∉ support falseOnlySpace := by
  simp [support, trueOnlySpace, falseOnlySpace, singletonSemantics]

/-- One compact boundary theorem: bags admit a support quotient, but neither
multiplicity, type evidence, type-code identity, nor union closure follows
back from the set-level view. -/
theorem occurrence_type_set_boundary :
    (support ({(), ()} : OccurrenceSpace Unit) =
      support ({()} : OccurrenceSpace Unit)) ∧
      (¬ (Snapshot.supportReadout (Revision := Unit)
        (Atom := Unit)).Faithful) ∧
      firstTypingWitness ≠ secondTypingWitness ∧
      coincidentSemantics.extent false = coincidentSemantics.extent true ∧
      false ≠ true ∧
      ¬ singletonSemantics.UnionClosed := by
  exact ⟨by simp [support],
    snapshotSupportReadout_not_faithful,
    typing_evidence_is_not_extent_membership.1,
    rfl,
    Bool.false_ne_true,
    singletonSemantics_not_unionClosed⟩

end Canary

#print axioms TypeExtentSemantics.extent_eq_of_code_eq
#print axioms TypeExtentSemantics.code_eq_of_extent_eq
#print axioms support_add
#print axioms support_eq_bagToSupport_map
#print axioms typedSupport_add
#print axioms TypedOccurrence.mem_typedSupport
#print axioms TypedOccurrence.exists_of_mem_typedSupport
#print axioms Canary.singletonSemantics_not_unionClosed
#print axioms Canary.coincident_extents_do_not_reflect_codes
#print axioms Canary.incompleteSemantics_not_complete
#print axioms Canary.typing_evidence_is_not_extent_membership
#print axioms Canary.snapshotSupportReadout_not_faithful
#print axioms Canary.multiplicity_does_not_descend_to_support
#print axioms Canary.revision_descends_to_support
#print axioms Canary.storage_and_typing_are_orthogonal
#print axioms Canary.occurrence_type_set_boundary

end Mettapedia.TypeTheory.OccurrenceSpaceTypeExtent
