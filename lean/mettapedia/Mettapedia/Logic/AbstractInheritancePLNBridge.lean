import Mettapedia.Logic.AbstractInheritanceWitness
import Mettapedia.Logic.ConceptOntology.WMBridge

/-!
# Abstract Inheritance Bridge for WM-PLN

This module makes the new `AbstractInheritance` spine explicit in the current
WM-PLN / Chapter-12 surface:

- typed WM membership evidence induces an abstract interpretation
- crisp extensional inheritance is exactly full abstract inheritance for that
  derived interpretation
- ASSOC/PAT subset semantics can therefore be stated downstream of the
  abstract inheritance layer
- finite abstract witness-evidence is available for finite WM canaries
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel
open Mettapedia.Logic.AbstractInheritance

universe u v w x y

namespace MembershipQueryBuilder

variable {State : Type u} {Obj : Type v} {Con : Type w} {Srt : Type x} {Query : Srt → Type y}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- The abstract inheritance interpretation induced by a typed WM membership
query family at a fixed state and gate. -/
def abstractInterpretationAt
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) :
    AbstractInheritance.Interpretation Con Obj Con :=
  AbstractInheritance.crispInterpretation G (memberEvidence W enc)

@[simp] theorem abstractInterpretationAt_meaning
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c : Con) :
    (abstractInterpretationAt G W enc).meaning c =
      AbstractInheritance.ofCrispBaseConcept G (memberEvidence W enc) c := rfl

theorem self_mem_intent_abstractInterpretationAt
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c : Con) :
    c ∈ ((abstractInterpretationAt G W enc).meaning c).intent := by
  change c ∈ (AbstractInheritance.ofCrispBaseConcept G (memberEvidence W enc) c).intent
  exact AbstractInheritance.self_mem_intent_ofCrispBaseConcept
    (G := G) (M := memberEvidence W enc) c

@[simp] theorem abstractInterpretationAt_extensionalInherits_iff
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c d : Con) :
    (abstractInterpretationAt G W enc).ExtensionalInherits c d ↔
      crispExtensionalInheritsAt G W enc c d := by
  exact AbstractInheritance.crispInterpretation_extensionalInherits_iff
    G (memberEvidence W enc) c d

theorem abstractInterpretationAt_inherits_iff
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c d : Con) :
    (abstractInterpretationAt G W enc).Inherits c d ↔
      crispExtensionalInheritsAt G W enc c d := by
  exact AbstractInheritance.crispInterpretation_inherits_iff
    G (memberEvidence W enc) c d

section Finite

variable [Fintype Obj] [DecidableEq Obj] [Fintype Con] [DecidableEq Con]

/-- Finite abstract witness-evidence extracted from the WM-induced abstract
interpretation. -/
noncomputable def abstractFiniteInheritanceEvidenceAt
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c d : Con) :
    BinaryEvidence :=
  (abstractInterpretationAt G W enc).finiteInheritanceEvidence c d

theorem abstractFiniteInheritanceEvidenceAt_neg_eq_zero_of_crispExtensionalInherits
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) {c d : Con}
    (hInh : crispExtensionalInheritsAt G W enc c d) :
    (abstractFiniteInheritanceEvidenceAt G W enc c d).neg = 0 := by
  exact AbstractInheritance.Interpretation.finiteInheritanceEvidence_neg_eq_zero_of_inherits
    (I := abstractInterpretationAt G W enc)
    ((abstractInterpretationAt_inherits_iff G W enc c d).2 hInh)

end Finite

end MembershipQueryBuilder

section AbstractSubset

variable {State Obj Con MemberSrt PairQuery : Type}
variable {MemberQuery : MemberSrt → Type}
variable [EvidenceType State]
variable [WorldModelSigma State MemberSrt MemberQuery]
variable [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]

/-- The pairwise subset relation expressed through the abstract inheritance
interpretation rather than raw extent inclusion. -/
def AbstractExtentPairSubsetRel
    (State Obj Con MemberSrt : Type)
    (MemberQuery : MemberSrt → Type)
    [EvidenceType State]
    [WorldModelSigma State MemberSrt MemberQuery]
    (G : EvidenceGate BinaryEvidence)
    (memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery)
    (W : State) (a b c d : Con) : Prop :=
  (MembershipQueryBuilder.abstractInterpretationAt G W memberEnc).PairSubsetRel a b c d

theorem abstractExtentPairSubsetRel_iff
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    {W : State} {a b c d : Con} :
    AbstractExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc W a b c d ↔
      ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc W a b c d := by
  constructor
  · rintro ⟨hLeft, hRight⟩
    exact ⟨(MembershipQueryBuilder.abstractInterpretationAt_inherits_iff G W memberEnc c a).mp hLeft,
      (MembershipQueryBuilder.abstractInterpretationAt_inherits_iff G W memberEnc b d).mp hRight⟩
  · rintro ⟨hLeft, hRight⟩
    exact ⟨(MembershipQueryBuilder.abstractInterpretationAt_inherits_iff G W memberEnc c a).mpr hLeft,
      (MembershipQueryBuilder.abstractInterpretationAt_inherits_iff G W memberEnc b d).mpr hRight⟩

theorem extensionalEvidenceSubsetRel_of_abstractInherits
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    {pairEnc : InheritanceQueryBuilder Con PairQuery}
    (hFactor :
      ExtensionalHookFactorization
        State Obj Con MemberSrt PairQuery MemberQuery G memberEnc pairEnc)
    {W : State} {a b : Con}
    (hInh :
      (MembershipQueryBuilder.abstractInterpretationAt G W memberEnc).Inherits a b) :
    InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a a ≤
      InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b := by
  exact extensionalEvidenceSubsetRel_of_crispExtensionalInherits
    (hFactor := hFactor)
    ((MembershipQueryBuilder.abstractInterpretationAt_inherits_iff G W memberEnc a b).mp hInh)

theorem assocEvidence_mono_of_abstractSubsetSemantics
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    (pairEnc : InheritanceQueryBuilder Con PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Con) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Con) (Query := PairQuery)
        pairEnc model
        (AbstractExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc))
    {W : State} {a b c d : Con}
    (hRel :
      AbstractExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc W a b c d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc c d := by
  have hSubset' :
      InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Con) (Query := PairQuery)
        pairEnc model
        (ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc) := by
    intro W a b c d hExtent
    exact hSubset W a b c d ((abstractExtentPairSubsetRel_iff
      (State := State) (Obj := Obj) (Con := Con) (MemberSrt := MemberSrt)
      (MemberQuery := MemberQuery) (G := G) (memberEnc := memberEnc)
      (W := W) (a := a) (b := b) (c := c) (d := d)).2 hExtent)
  exact assocEvidence_mono_of_extentPairSubsetSemantics
    (G := G) (memberEnc := memberEnc)
    pairEnc model hSubset'
    ((abstractExtentPairSubsetRel_iff
      (State := State) (Obj := Obj) (Con := Con) (MemberSrt := MemberSrt)
      (MemberQuery := MemberQuery) (G := G) (memberEnc := memberEnc)
      (W := W) (a := a) (b := b) (c := c) (d := d)).1 hRel)

theorem patEvidence_mono_of_abstractSubsetSemantics
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    (pairEnc : InheritanceQueryBuilder Con PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Con) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Con) (Query := PairQuery)
        pairEnc model
        (AbstractExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc))
    {W : State} {a b c d : Con}
    (hRel :
      AbstractExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc W a b c d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc c d := by
  have hSubset' :
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Con) (Query := PairQuery)
        pairEnc model
        (ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc) := by
    intro W a b c d hExtent
    exact hSubset W a b c d ((abstractExtentPairSubsetRel_iff
      (State := State) (Obj := Obj) (Con := Con) (MemberSrt := MemberSrt)
      (MemberQuery := MemberQuery) (G := G) (memberEnc := memberEnc)
      (W := W) (a := a) (b := b) (c := c) (d := d)).2 hExtent)
  exact patEvidence_mono_of_extentPairSubsetSemantics
    (G := G) (memberEnc := memberEnc)
    pairEnc model hSubset'
    ((abstractExtentPairSubsetRel_iff
      (State := State) (Obj := Obj) (Con := Con) (MemberSrt := MemberSrt)
      (MemberQuery := MemberQuery) (G := G) (memberEnc := memberEnc)
      (W := W) (a := a) (b := b) (c := c) (d := d)).1 hRel)

end AbstractSubset

end Mettapedia.Logic.ConceptOntology
