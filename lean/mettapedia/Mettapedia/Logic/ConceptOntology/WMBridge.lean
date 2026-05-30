import Mettapedia.Logic.ConceptOntology.WeakRepresentation
import Mettapedia.Logic.PLNIntensionalWorldModel

/-!
# World-Model Bridge for Evidence-Valued Concept Ontology

This module connects typed world-model query extraction to the ontology core:

- object/concept membership can be read from a typed `WorldModelSigma`
- the resulting membership relation induces crisp extents and intents
- current pairwise extensional hooks can be stated as downstream summaries of
  extent inclusion, via an explicit factorization witness
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel

universe u v w x y

/-- Builder for the typed query family that returns membership evidence for
object/concept pairs. -/
structure MembershipQueryBuilder
    (Obj : Type u) (Con : Type v) (Srt : Type w) (Query : Srt → Type x) where
  memberSort : Srt
  member : Obj → Con → Query memberSort

namespace MembershipQueryBuilder

variable {State : Type u} {Obj : Type v} {Con : Type w} {Srt : Type x} {Query : Srt → Type y}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Read typed WM evidence as object/concept membership evidence. -/
def memberEvidence
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (x : Obj) (c : Con) :
    BinaryEvidence :=
  WorldModelSigma.evidenceAt W (enc.member x c)

@[simp] theorem memberEvidence_add
    (W₁ W₂ : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (x : Obj) (c : Con) :
    memberEvidence (W₁ + W₂) enc x c =
      memberEvidence W₁ enc x c + memberEvidence W₂ enc x c := by
  simpa [memberEvidence] using
    (WorldModelSigma.evidenceAt_add (State := State) (Srt := Srt)
      (Query := Query) W₁ W₂ (enc.member x c))

/-- Every typed membership-query builder induces an additive evidence
membership context. -/
def toEvidenceMembershipContext
    (enc : MembershipQueryBuilder Obj Con Srt Query) :
    EvidenceMembershipContext State Obj Con BinaryEvidence where
  memberEvidence := fun W x c => MembershipQueryBuilder.memberEvidence W enc x c
  memberEvidence_add := fun W₁ W₂ x c =>
    MembershipQueryBuilder.memberEvidence_add W₁ W₂ enc x c

/-- View the typed WM membership evidence as a gated crisp extent. -/
def crispExtentAt
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c : Con) : Set Obj :=
  crispExtent G (memberEvidence W enc) c

/-- View the typed WM membership evidence as a gated crisp intent. -/
def crispIntentAt
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (x : Obj) : Set Con :=
  crispIntent G (memberEvidence W enc) x

/-- Derived extensional inheritance from typed WM membership evidence. -/
def crispExtensionalInheritsAt
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c d : Con) : Prop :=
  crispExtensionalInherits G (memberEvidence W enc) c d

@[simp] theorem mem_crispExtentAt_iff
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (x : Obj) (c : Con) :
    x ∈ crispExtentAt G W enc c ↔ G.accept (memberEvidence W enc x c) := by
  simp [crispExtentAt, memberEvidence]

@[simp] theorem mem_crispIntentAt_iff
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (x : Obj) (c : Con) :
    c ∈ crispIntentAt G W enc x ↔ G.accept (memberEvidence W enc x c) := by
  simp [crispIntentAt, memberEvidence]

@[simp] theorem crispExtensionalInheritsAt_iff
    (G : EvidenceGate BinaryEvidence)
    (W : State) (enc : MembershipQueryBuilder Obj Con Srt Query) (c d : Con) :
    crispExtensionalInheritsAt G W enc c d ↔
      ∀ x, G.accept (memberEvidence W enc x c) → G.accept (memberEvidence W enc x d) := by
  exact crispExtensionalInherits_iff G (memberEvidence W enc) c d

/-- Convenience builder for the one-sort typed view of an untyped query family. -/
def ofUntyped
    {Query : Type x} (member : Obj → Con → Query) :
    MembershipQueryBuilder Obj Con PUnit (fun _ : PUnit => Query) where
  memberSort := PUnit.unit
  member := member

@[simp] theorem ofUntyped_member
    {Query : Type x} (member : Obj → Con → Query) (x : Obj) (c : Con) :
    (ofUntyped (Obj := Obj) (Con := Con) member).member x c = member x c := rfl

end MembershipQueryBuilder

section AtomQueryBridge

variable {State : Type u} {Obj : Type v} {Con : Type w} {Atom : Type x}
variable [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- Encode object/concept membership as a canonical `AtomQuery.prop` query. -/
structure MembershipAtomEncoder (Obj : Type v) (Con : Type w) (Atom : Type x) where
  atomOf : Obj → Con → Atom

namespace MembershipAtomEncoder

/-- The real WM query-family instantiation for membership on the standard
`AtomQuery` surface. -/
def toMembershipQueryBuilder
    (enc : MembershipAtomEncoder Obj Con Atom) :
    MembershipQueryBuilder Obj Con PUnit (fun _ : PUnit => AtomQuery Atom) :=
  MembershipQueryBuilder.ofUntyped (fun x c => AtomQuery.prop (enc.atomOf x c))

/-- The corresponding evidence-valued membership context on the live WM query
surface. -/
noncomputable def toEvidenceMembershipContext
    (enc : MembershipAtomEncoder Obj Con Atom) :
    EvidenceMembershipContext State Obj Con BinaryEvidence where
  memberEvidence := fun W x c =>
    AtomQuery.propEvidence (State := State) (Atom := Atom) W (enc.atomOf x c)
  memberEvidence_add := by
    intro W₁ W₂ x c
    simpa using AtomQuery.propEvidence_add
      (State := State) (Atom := Atom) W₁ W₂ (enc.atomOf x c)

@[simp] theorem memberEvidence_eq_propEvidence
    (enc : MembershipAtomEncoder Obj Con Atom)
    (W : State) (x : Obj) (c : Con) :
    enc.toEvidenceMembershipContext.memberEvidence W x c =
      AtomQuery.propEvidence (State := State) (Atom := Atom) W (enc.atomOf x c) := by
  rfl

end MembershipAtomEncoder

end AtomQueryBridge

section ExtensionalFactorization

variable {State Obj Con MemberSrt PairQuery : Type}
variable {MemberQuery : MemberSrt → Type}
variable [EvidenceType State]
variable [WorldModelSigma State MemberSrt MemberQuery]
variable [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]

/-- Pairwise concept-link order induced by gated extent inclusion:
the antecedent narrows while the consequent broadens. -/
def ExtentPairSubsetRel
    (State Obj Con MemberSrt : Type)
    (MemberQuery : MemberSrt → Type)
    [EvidenceType State]
    [WorldModelSigma State MemberSrt MemberQuery]
    (G : EvidenceGate BinaryEvidence)
    (memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery)
    (W : State) (a b c d : Con) : Prop :=
  MembershipQueryBuilder.crispExtentAt G W memberEnc c ⊆
      MembershipQueryBuilder.crispExtentAt G W memberEnc a ∧
    MembershipQueryBuilder.crispExtentAt G W memberEnc b ⊆
      MembershipQueryBuilder.crispExtentAt G W memberEnc d

/-- Witness that the current pairwise extensional hook is only a summary of the
underlying gated extents. -/
structure ExtensionalHookFactorization
    (State Obj Con MemberSrt PairQuery : Type)
    (MemberQuery : MemberSrt → Type)
    [EvidenceType State]
    [WorldModelSigma State MemberSrt MemberQuery]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
    (G : EvidenceGate BinaryEvidence)
    (memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery)
    (pairEnc : InheritanceQueryBuilder Con PairQuery) where
  summarize : State → Set Obj → Set Obj → BinaryEvidence
  summarize_mono :
    ∀ {W : State} {A B C D : Set Obj},
      C ⊆ A → B ⊆ D → summarize W A B ≤ summarize W C D
  factor :
    ∀ W a b,
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b =
        summarize W
          (MembershipQueryBuilder.crispExtentAt G W memberEnc a)
          (MembershipQueryBuilder.crispExtentAt G W memberEnc b)

theorem extensionalEvidenceSubsetRel_of_extentPairSubsetRel
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    {pairEnc : InheritanceQueryBuilder Con PairQuery}
    (hFactor :
      ExtensionalHookFactorization
        State Obj Con MemberSrt PairQuery MemberQuery G memberEnc pairEnc)
    {W : State} {a b c d : Con}
    (hRel : ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc W a b c d) :
    InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc c d := by
  rcases hRel with ⟨hLeft, hRight⟩
  rw [hFactor.factor W a b, hFactor.factor W c d]
  exact hFactor.summarize_mono hLeft hRight

theorem extensionalEvidenceSubsetRel_of_crispExtensionalInherits
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    {pairEnc : InheritanceQueryBuilder Con PairQuery}
    (hFactor :
      ExtensionalHookFactorization
        State Obj Con MemberSrt PairQuery MemberQuery G memberEnc pairEnc)
    {W : State} {a b : Con}
    (hInh :
      MembershipQueryBuilder.crispExtensionalInheritsAt G W memberEnc a b) :
    InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a a ≤
      InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b := by
  apply extensionalEvidenceSubsetRel_of_extentPairSubsetRel hFactor
  exact ⟨fun _ hx => hx, hInh⟩

theorem assocEvidence_mono_of_extentPairSubsetSemantics
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    (pairEnc : InheritanceQueryBuilder Con PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Con) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Con) (Query := PairQuery)
        pairEnc model
        (ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc))
    {W : State} {a b c d : Con}
    (hRel : ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc W a b c d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc c d := by
  exact InheritanceQueryBuilder.assocEvidence_mono_of_subsetSemantics
    (State := State) (Atom := Con) (Query := PairQuery)
    pairEnc model
    (subsetRel := ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc)
    hSubset hRel

theorem patEvidence_mono_of_extentPairSubsetSemantics
    {G : EvidenceGate BinaryEvidence}
    {memberEnc : MembershipQueryBuilder Obj Con MemberSrt MemberQuery}
    (pairEnc : InheritanceQueryBuilder Con PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Con) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Con) (Query := PairQuery)
        pairEnc model
        (ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc))
    {W : State} {a b c d : Con}
    (hRel : ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc W a b c d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Con) (Query := PairQuery) W pairEnc c d := by
  exact InheritanceQueryBuilder.patEvidence_mono_of_subsetSemantics
    (State := State) (Atom := Con) (Query := PairQuery)
    pairEnc model
    (subsetRel := ExtentPairSubsetRel State Obj Con MemberSrt MemberQuery G memberEnc)
    hSubset hRel

end ExtensionalFactorization

end Mettapedia.Logic.ConceptOntology
