import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.Languages.MeTTa.NativeTypeTheoryDerivation
import Mettapedia.Languages.MeTTa.PureKernel.Universe.RelationalInternalLanguage

/-!
# Occurrence bags for Prime relations

This module connects the proof-relevant relation at the center of Prime's
GSLT-IL interpretation to the occurrence-sensitive answer effect used by an
engine.  An answer occurrence retains its visible target and the exact
derivation inhabiting the relation fibre.  Relational `Chain` is realized by
bag bind: the generated occurrence stores the intermediate target and both
input derivations.

Truth support is a derived quotient.  It is sound for every bag and complete
only when the bag is explicitly certified complete.  Erasing multiplicity is
proved non-faithful, and the existing native-typing Galois connection and PLN
non-factorization theorem are exposed as the typing instance of this relation
layer.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe

namespace RelationalEvidence

open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.Languages.MeTTa.NativeTypeTheory

universe u

/-- Short name for the Prime semantic relation, kept distinct from Lean's
root-level proposition-valued `Rel`. -/
abbrev ProofRel := RelationalInternalLanguage.Semantic.Rel

/-! ## Proof-relevant answer occurrences -/

/-- One engine answer together with the exact derivation that produced it. -/
structure AnswerOccurrence {Source Target : Type u}
    (relation : ProofRel Source Target) (source : Source) where
  target : Target
  derivation : relation.evidence source target

/-- An unordered, occurrence-sensitive engine result. -/
abbrev AnswerBag {Source Target : Type u}
    (relation : ProofRel Source Target) (source : Source) :=
  Multiset (AnswerOccurrence relation source)

namespace AnswerBag

/-- Forget derivations while retaining every visible target occurrence. -/
def targets {Source Target : Type u} {relation : ProofRel Source Target}
    {source : Source} (bag : AnswerBag relation source) : Multiset Target :=
  bag.map AnswerOccurrence.target

/-- Boolean-level support, stated propositionally so no decidable equality is
required of target values. -/
def support {Source Target : Type u} {relation : ProofRel Source Target}
    {source : Source} (bag : AnswerBag relation source) : Set Target :=
  { target | ∃ occurrence, occurrence ∈ bag ∧ occurrence.target = target }

/-- Every supported answer is true in the underlying relation. -/
theorem support_sound {Source Target : Type u}
    {relation : ProofRel Source Target}
    {source : Source} {bag : AnswerBag relation source} {target : Target}
    (supported : target ∈ support bag) :
    Nonempty (relation.evidence source target) := by
  rcases supported with ⟨occurrence, _member, rfl⟩
  exact ⟨occurrence.derivation⟩

/-- A bag is complete when it contains at least one occurrence for every
inhabited relation fibre and no unsupported occurrence. -/
def Complete {Source Target : Type u} {relation : ProofRel Source Target}
    {source : Source} (bag : AnswerBag relation source) : Prop :=
  ∀ target, Nonempty (relation.evidence source target) ↔ target ∈ support bag

/-- Support erasure recovers relational truth exactly from a certified
complete bag. -/
theorem complete_support_iff {Source Target : Type u}
    {relation : ProofRel Source Target} {source : Source}
    {bag : AnswerBag relation source} (complete : Complete bag)
    (target : Target) :
    target ∈ support bag ↔ Nonempty (relation.evidence source target) :=
  (complete target).symm

/-- Dropping derivations does not drop answer occurrences. -/
@[simp] theorem card_targets {Source Target : Type u}
    {relation : ProofRel Source Target} {source : Source}
    (bag : AnswerBag relation source) :
    (targets bag).card = bag.card := by
  simp [targets]

/-- Transport every derivation through an exact fibrewise equivalence. -/
def mapEvidence {Source Target : Type u}
    {first second : ProofRel Source Target}
    (equivalence : ∀ source target,
      first.evidence source target ≃ second.evidence source target)
    {source : Source} (bag : AnswerBag first source) :
    AnswerBag second source :=
  bag.map fun occurrence =>
    ⟨occurrence.target,
      equivalence source occurrence.target occurrence.derivation⟩

/-- Exact evidence transport preserves occurrence multiplicity. -/
@[simp] theorem card_mapEvidence {Source Target : Type u}
    {first second : ProofRel Source Target}
    (equivalence : ∀ source target,
      first.evidence source target ≃ second.evidence source target)
    {source : Source} (bag : AnswerBag first source) :
    (mapEvidence equivalence bag).card = bag.card := by
  simp [mapEvidence]

/-! ## Chain as occurrence-bag bind -/

/-- Pair one earlier and one later occurrence into the genuine relational
`Chain` fibre. -/
def chainOccurrence {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    {source : First} (first : AnswerOccurrence earlier source)
    (second : AnswerOccurrence later first.target) :
    AnswerOccurrence
      (RelationalInternalLanguage.Semantic.Rel.Chain earlier later) source where
  target := second.target
  derivation := ⟨first.target, first.derivation, second.derivation⟩

/-- Engine realization of relational `Chain`.  This is precisely the existing
unordered answer-effect bind followed by evidence pairing. -/
def chain {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    {source : First} (answers : AnswerBag earlier source)
    (next : (answer : AnswerOccurrence earlier source) →
      AnswerBag later answer.target) :
    AnswerBag
      (RelationalInternalLanguage.Semantic.Rel.Chain earlier later) source :=
  bagEffect.bind answers fun answer =>
    (next answer).map (chainOccurrence answer)

/-- The engine operation used by `chain` is bag bind, not function
composition or support-set composition. -/
theorem chain_eq_bag_bind {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    {source : First} (answers : AnswerBag earlier source)
    (next : (answer : AnswerOccurrence earlier source) →
      AnswerBag later answer.target) :
    chain answers next =
      bagEffect.bind answers fun answer =>
        (next answer).map (chainOccurrence answer) :=
  rfl

/-- Membership in a chained bag exposes the retained intermediate occurrence
and the later occurrence used to produce the answer. -/
theorem mem_chain_iff {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    {source : First} (answers : AnswerBag earlier source)
    (next : (answer : AnswerOccurrence earlier source) →
      AnswerBag later answer.target)
    (result : AnswerOccurrence
      (RelationalInternalLanguage.Semantic.Rel.Chain earlier later) source) :
    result ∈ chain answers next ↔
      ∃ first, first ∈ answers ∧
        ∃ second, second ∈ next first ∧
          chainOccurrence first second = result := by
  simp [chain, bagEffect]

/-- Chaining counts every pair of derivation occurrences. -/
theorem card_chain {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    {source : First} (answers : AnswerBag earlier source)
    (next : (answer : AnswerOccurrence earlier source) →
      AnswerBag later answer.target) :
    (chain answers next).card =
      (answers.map fun answer => (next answer).card).sum := by
  simp [chain, bagEffect, Multiset.card_bind]

/-- The evidence produced by bag bind is definitionally the horizontal
composition evidence in the selected relational equipment. -/
def chainEvidenceEquipmentEquiv {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    (source : First) (target : Last) :
    (RelationalInternalLanguage.Semantic.Rel.Chain earlier later).evidence
        source target ≃
      Mettapedia.GSLT.LooseRelationEquipment.comp
        earlier.toLoose later.toLoose source target :=
  RelationalInternalLanguage.Semantic.Rel.chainWitnessEquiv
    earlier later source target

end AnswerBag

/-! ## The native-typing instance of the relation layer -/

/-- Native typing is a relation from the unique query point to claims, with
authored derivation-plus-PLN evidence as its proof fibre. -/
def nativeTypingRel : ProofRel Unit NativeTypingClaim where
  evidence _ claim := NativeEvidenceDerivation claim

/-- The established native derivation bag is exactly a fibrewise bag for the
native typing relation. -/
abbrev NativeRelFibreBag :=
  (claim : NativeTypingClaim) →
    Multiset (nativeTypingRel.evidence () claim)

def nativeDerivationBagEquiv : NativeDerivationBag ≃ NativeRelFibreBag :=
  Equiv.refl _

/-- Truth erasure for the relation instance is the already-proved Galois
connection between unit truth bags and positive multiplicity support. -/
theorem nativeRel_truthSet_galois :
    GaloisConnection NativeDerivationCountBag.ofTruthSet
      NativeDerivationCountBag.truthSet :=
  NativeDerivationCountBag.truthSet_galois

/-- The relation interpretation does not make a PLN strength readout
recoverable from Boolean truth. -/
theorem nativeRel_strength_does_not_factor_through_truth :
    ¬ NativeDerivationBag.StrengthFactorsThroughTruthAt
      primitiveLetTypingClaim :=
  nativeEvidence_strength_does_not_factor_through_truth

/-! ## Loss canary -/

/-- Multiplicity support is a proper quotient of the engine bag profile. -/
theorem occurrence_bag_to_support_not_faithful :
    ¬ bagToSupport.{0}.Faithful :=
  bagToSupport_not_faithful

#print axioms AnswerBag.support_sound
#print axioms AnswerBag.card_mapEvidence
#print axioms AnswerBag.mem_chain_iff
#print axioms AnswerBag.card_chain
#print axioms AnswerBag.chainEvidenceEquipmentEquiv
#print axioms nativeRel_truthSet_galois
#print axioms nativeRel_strength_does_not_factor_through_truth
#print axioms occurrence_bag_to_support_not_faithful

end RelationalEvidence

end Mettapedia.Languages.MeTTa.PureKernel.Universe
