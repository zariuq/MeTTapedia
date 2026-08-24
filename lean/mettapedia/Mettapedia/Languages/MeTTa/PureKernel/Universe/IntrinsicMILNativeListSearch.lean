import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILNativeSearch
import Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeRelationLifting

/-!
# Exact native search through the strictly-positive List relator

An exact finite evidence provider for an element relation lifts structurally
through Prime's native polynomial List.  The lifted index is the product of
one exact head occurrence and the recursively derived tail occurrence.  Its
equivalence with the complete dependent answer fibre retains target values and
all proof multiplicity.

This is a capability of the strictly-positive data former, not a special MIL
evaluator.  Functional representation implies this capability, but finite
nondeterministic evidence also lifts.  An infinite singleton head fibre gives
the refusing boundary and remains meaningful relationally.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace IntrinsicMILNativeListSearch

open Mettapedia.TypeTheory.IndexedPolynomial
open RelationalInternalLanguage.Semantic
open RelationalEvidence
open IntrinsicMILNativeSearch

universe u

/-! ## Exact finite fibres over ordinary List spines -/

/-- The ordinary-spine presentation of pointwise proof-relevant List lifting.
It is used only to perform structural recursion; the public provider below is
transported to the native polynomial List. -/
def ordinaryListRelation {Source Target : Type u}
    (relation : IntrinsicMILNativeSearch.ProofRel Source Target) :
    IntrinsicMILNativeSearch.ProofRel (List Source) (List Target) where
  evidence source target :=
    ListExample.ListRel relation.evidence source target

/-- A cons-result occurrence is exactly a head occurrence paired with one
tail occurrence.  The equivalence retains both targets and both derivations. -/
def consOccurrenceEquiv {Source Target : Type u}
    (relation : IntrinsicMILNativeSearch.ProofRel Source Target)
    (head : Source) (tail : List Source) :
    (AnswerOccurrence relation head ×
        AnswerOccurrence (ordinaryListRelation relation) tail) ≃
      AnswerOccurrence (ordinaryListRelation relation) (head :: tail) where
  toFun occurrences :=
    ⟨occurrences.1.target :: occurrences.2.target,
      .cons occurrences.1.derivation occurrences.2.derivation⟩
  invFun occurrence := by
    rcases occurrence with ⟨target, evidence⟩
    cases evidence with
    | cons headEvidence tailEvidence =>
        exact (⟨_, headEvidence⟩, ⟨_, tailEvidence⟩)
  left_inv := by
    rintro ⟨⟨headTarget, headEvidence⟩, ⟨tailTarget, tailEvidence⟩⟩
    rfl
  right_inv := by
    rintro ⟨target, evidence⟩
    cases evidence
    rfl

/-- Exact finite evidence enumeration is closed under ordinary List spines.
The cons index is a product of the exact head occurrence and the recursively
exact tail occurrence. -/
noncomputable def ordinaryListFibre {Source Target : Type u}
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    (source : List Source) →
      FiniteEvidenceFibre (ordinaryListRelation relation) source
  | [] =>
      { Index := PUnit
        indexFintype := inferInstance
        occurrenceEquiv :=
          { toFun := fun _ => ⟨[], .nil⟩
            invFun := fun _ => PUnit.unit
            left_inv := fun _ => rfl
            right_inv := by
              rintro ⟨target, evidence⟩
              cases evidence
              rfl } }
  | head :: tail => by
      let headFibre := provider.fibre head
      let tailFibre := ordinaryListFibre provider tail
      letI : Fintype headFibre.Index := headFibre.indexFintype
      letI : Fintype tailFibre.Index := tailFibre.indexFintype
      exact
        { Index := headFibre.Index × tailFibre.Index
          indexFintype := inferInstance
          occurrenceEquiv :=
            (Equiv.prodCongr headFibre.occurrenceEquiv
              tailFibre.occurrenceEquiv).trans
                (consOccurrenceEquiv relation head tail) }

/-! ## Transport to the native polynomial List -/

/-- Ordinary and native List answer occurrences are exactly equivalent.  The
target List is transported through the proved no-junk/no-confusion
representation; the proof spine is unchanged. -/
def occurrenceSigmaEquiv {Source Target : Type u}
    (relation : IntrinsicMILNativeSearch.ProofRel Source Target)
    (source : Source) :
    AnswerOccurrence relation source ≃
      (Sigma fun target => relation.evidence source target) where
  toFun occurrence := ⟨occurrence.target, occurrence.derivation⟩
  invFun occurrence := ⟨occurrence.1, occurrence.2⟩
  left_inv := by
    rintro ⟨target, evidence⟩
    rfl
  right_inv := by
    rintro ⟨target, evidence⟩
    rfl

noncomputable def nativeOccurrenceEquiv {Source Target : Type u}
    (relation : IntrinsicMILNativeSearch.ProofRel Source Target)
    (source : NativeIndexedFamilies.Semantic.List Source) :
    AnswerOccurrence (ordinaryListRelation relation)
        (ListExample.toList source) ≃
      AnswerOccurrence (NativeIndexedFamilies.Semantic.mapRel relation)
        source := by
  refine (occurrenceSigmaEquiv (ordinaryListRelation relation)
    (ListExample.toList source)).trans ?_
  refine (Equiv.sigmaCongr (ListExample.equivList Target).symm
    (fun target => ?_)).trans
      (occurrenceSigmaEquiv
        (NativeIndexedFamilies.Semantic.mapRel relation) source).symm
  apply Equiv.cast
  change ListExample.ListRel relation.evidence
      (ListExample.toList source) target =
    ListExample.ListRel relation.evidence
      (ListExample.toList source) (ListExample.toList (ListExample.ofList target))
  rw [ListExample.toList_ofList]

/-- The exact native List fibre is obtained by structural enumeration over
the represented ordinary spine followed by the exact occurrence transport. -/
noncomputable def mapRelFibre {Source Target : Type u}
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (source : NativeIndexedFamilies.Semantic.List Source) :
    FiniteEvidenceFibre (NativeIndexedFamilies.Semantic.mapRel relation)
      source := by
  let ordinary := ordinaryListFibre provider (ListExample.toList source)
  exact
    { Index := ordinary.Index
      indexFintype := ordinary.indexFintype
      occurrenceEquiv := ordinary.occurrenceEquiv.trans
        (nativeOccurrenceEquiv relation source) }

/-- Exact finite element search lifts through Prime's strictly-positive
native List relator. -/
noncomputable def mapRelProvider {Source Target : Type u}
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    FiniteEvidenceProvider
      (NativeIndexedFamilies.Semantic.mapRel relation) where
  fibre := mapRelFibre provider

/-- The lifted native operation enumerates the complete target/derivation
fibre for every source List. -/
theorem mapRel_run_complete {Source Target : Type u}
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (source : NativeIndexedFamilies.Semantic.List Source) :
    AnswerBag.Complete ((mapRelProvider provider).run source).answers :=
  (mapRelProvider provider).run_complete source

/-! ## Functional specialization is earned -/

/-- Representability of an element relation lifts to representability of its
native List relator.  The direct map is the native structurally recursive
`List.map`; the exact fibre equivalence is inherited pointwise. -/
noncomputable def mapRelRepresentation {Source Target : Type u}
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (representation : Rel.Representation relation) :
    Rel.Representation (NativeIndexedFamilies.Semantic.mapRel relation) where
  map := NativeIndexedFamilies.Semantic.map representation.map
  exact source target :=
    (ListExample.ListRel.evidenceEquiv
      (fun left right => representation.exact left right)
      (ListExample.toList source) (ListExample.toList target)).trans
        (NativeIndexedFamilies.Semantic.mapRel_graph_equiv_graph_map
          representation.map source target)

@[simp] theorem mapRelRepresentation_map {Source Target : Type u}
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (representation : Rel.Representation relation) :
    (mapRelRepresentation representation).map =
      NativeIndexedFamilies.Semantic.map representation.map :=
  rfl

/-! ## Positive and refusing controls -/

namespace Canary

/-- The two element-level derivations form one exact finite fibre. -/
def branchingFibre : FiniteEvidenceFibre
    NativeIndexedFamilies.Semantic.branchingRelation () where
  Index := Bool
  indexFintype := inferInstance
  occurrenceEquiv :=
    { toFun
        | false => ⟨(), .left⟩
        | true => ⟨(), .right⟩
      invFun := fun occurrence =>
        match occurrence.derivation with
        | .left => false
        | .right => true
      left_inv := by
        intro branch
        cases branch <;> rfl
      right_inv := by
        rintro ⟨target, evidence⟩
        cases target
        cases evidence <;> rfl }

def branchingProvider : FiniteEvidenceProvider
    NativeIndexedFamilies.Semantic.branchingRelation where
  fibre := fun source => by
    cases source
    exact branchingFibre

noncomputable def branchingListProvider : FiniteEvidenceProvider
    (NativeIndexedFamilies.Semantic.mapRel
      NativeIndexedFamilies.Semantic.branchingRelation) :=
  mapRelProvider branchingProvider

/-- List lifting retains both derivations at the singleton head; endpoint
support is not mistaken for one occurrence. -/
theorem branching_list_search_retains_two_proofs :
    (branchingListProvider.run ListExample.singletonUnit).answers.card = 2 := by
  change (branchingListProvider.answers ListExample.singletonUnit).card = 2
  rw [FiniteEvidenceProvider.answers_card]
  change Fintype.card (Bool × PUnit) = 2
  decide

/-- Functional element evidence earns the graph-of-native-map realization. -/
noncomputable def boolNotListRepresentation :
    Rel.Representation
      (NativeIndexedFamilies.Semantic.mapRel (Rel.graph Bool.not)) :=
  mapRelRepresentation (Rel.graphRepresentation Bool.not)

@[simp] theorem boolNotListRepresentation_map :
    boolNotListRepresentation.map =
      NativeIndexedFamilies.Semantic.map Bool.not :=
  rfl

/-- One singleton List occurrence of the infinite element relation still
carries exactly one natural-number proof choice. -/
noncomputable def infiniteOrdinaryOccurrenceEquiv :
    AnswerOccurrence
        (ordinaryListRelation IntrinsicMILNativeSearch.Canary.infinitelyManyProofs)
        [()] ≃ Nat where
  toFun := fun occurrence => by
    rcases occurrence with ⟨target, evidence⟩
    cases evidence with
    | cons headEvidence tailEvidence => exact headEvidence
  invFun := fun evidence => ⟨[()], .cons evidence .nil⟩
  left_inv := by
    rintro ⟨target, evidence⟩
    cases evidence with
    | cons headEvidence tailEvidence =>
        cases tailEvidence
        rfl
  right_inv := fun _ => rfl

noncomputable def infiniteListOccurrenceEquiv :
    AnswerOccurrence
        (NativeIndexedFamilies.Semantic.mapRel
          IntrinsicMILNativeSearch.Canary.infinitelyManyProofs)
        ListExample.singletonUnit ≃ Nat :=
  (nativeOccurrenceEquiv
      IntrinsicMILNativeSearch.Canary.infinitelyManyProofs
      ListExample.singletonUnit).symm.trans infiniteOrdinaryOccurrenceEquiv

/-- Strict positivity does not make an infinite evidence fibre finite.  The
lifted relation remains meaningful, but exact finite native search is
unavailable already on its singleton source. -/
theorem infinite_element_fibre_has_no_finite_list_provider :
    ¬ Nonempty
      (FiniteEvidenceProvider
        (NativeIndexedFamilies.Semantic.mapRel
          IntrinsicMILNativeSearch.Canary.infinitelyManyProofs)) := by
  rintro ⟨provider⟩
  let fibre := provider.fibre ListExample.singletonUnit
  let indexEquivNat : fibre.Index ≃ Nat :=
    fibre.occurrenceEquiv.trans infiniteListOccurrenceEquiv
  letI : Fintype Nat := Fintype.ofEquiv fibre.Index indexEquivNat
  exact not_finite Nat

end Canary

#print axioms ordinaryListFibre
#print axioms nativeOccurrenceEquiv
#print axioms mapRelProvider
#print axioms mapRelRepresentation
#print axioms Canary.branching_list_search_retains_two_proofs
#print axioms Canary.boolNotListRepresentation
#print axioms Canary.infinite_element_fibre_has_no_finite_list_provider

end IntrinsicMILNativeListSearch
end Mettapedia.Languages.MeTTa.PureKernel.Universe
