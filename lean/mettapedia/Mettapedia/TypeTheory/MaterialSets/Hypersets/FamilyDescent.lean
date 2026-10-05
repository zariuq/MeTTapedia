import Mettapedia.TypeTheory.DependentFamilySectionDescent
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Presentations

/-!
# Dependent families and sections over hyperset presentations

An occurrence in a pointed graph observes an actual member of its pictured
hyperset. This observation is onto, but duplicated edges can give distinct
occurrences of one member. A factorizing family therefore has two separate
descent obligations: its fibres identify with fibres on material members, and
its selected section agrees on observationally equal occurrences.

Given explicit occurrence recovery, compatible sections are exactly sections
on material members. The kernel quotient of the dependent total space is the
observed total space. The supplied recovery is data; the separately named
classical construction uses choice. Bounded graph morphisms give commuting
substitution squares.

The duplicated-child controls distinguish a descending constant Boolean
family from an edge-sensitive section of that family, and from an edge-sensitive
family with inhabited and empty fibres.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

universe u v

namespace AccessiblePointedGraph

/-- The material members of the hyperset pictured by a presentation. -/
abbrev PicturedMembers (G : AccessiblePointedGraph.{u}) :=
  {x : HSet.{u} // x ∈ picture G}

/-- Read an occurrence as its material member, retaining the membership fact. -/
def memberObservation (G : AccessiblePointedGraph.{u}) (o : Occurrence G) :
    PicturedMembers G :=
  ⟨o.picture, mem_picture_iff_occurrence.mpr ⟨o, rfl⟩⟩

/-- Every material member has an occurrence; this existential is not a
selected occurrence. -/
theorem memberObservation_surjective (G : AccessiblePointedGraph.{u}) :
    Function.Surjective (memberObservation G) := by
  intro member
  obtain ⟨occurrence, same⟩ := mem_picture_iff_occurrence.mp member.2
  exact ⟨occurrence, Subtype.ext same⟩

/-- Explicit recovery of an occurrence for each material member. -/
structure OccurrenceRecovery (G : AccessiblePointedGraph.{u}) where
  recover : PicturedMembers G → Occurrence G
  picture_recover : ∀ member, (recover member).picture = member.1

namespace OccurrenceRecovery

/-- Recovering from mere existential membership by classical choice. -/
noncomputable def classical (G : AccessiblePointedGraph.{u}) : OccurrenceRecovery G where
  recover member := Classical.choose (memberObservation_surjective G member)
  picture_recover member :=
    congrArg Subtype.val (Classical.choose_spec (memberObservation_surjective G member))

/-- The member observation equipped with the supplied recovery data. -/
def readout {G : AccessiblePointedGraph.{u}} (r : OccurrenceRecovery G) :
    SplitReadout (Occurrence G) (PicturedMembers G) where
  observe := memberObservation G
  representative := r.recover
  observe_representative member := Subtype.ext (r.picture_recover member)

end OccurrenceRecovery

section Families

variable {G : AccessiblePointedGraph.{u}} {F : Occurrence G → Type v}
variable (d : FamilyFactorization (memberObservation G) F)

/-- Actual functions on material members are exactly compatible functions on
occurrences, relative to the selected fibre interpretation. -/
def memberSectionEquiv (r : OccurrenceRecovery G) :
    (∀ member, d.targetFamily member) ≃
      {term : ∀ occurrence, F occurrence // Compatible d term} :=
  sectionEquiv r.readout d

/-- Total-space descent identifies exactly the dependent values that have the
same material-member observation. -/
def memberTotalQuotientEquiv (r : OccurrenceRecovery G) :
    Quotient (Setoid.ker d.totalObservation) ≃ Sigma d.targetFamily :=
  totalQuotientEquiv r.readout d

end Families

namespace Hom

variable {G H : AccessiblePointedGraph.{u}}

/-- A bounded presentation morphism carries material members by the identity
on their underlying hypersets. -/
def mapMember (φ : Hom G H) (member : PicturedMembers G) : PicturedMembers H :=
  ⟨member.1, by rw [φ.picture_eq]; exact member.2⟩

/-- Occurrence substitution and material-member substitution commute. -/
theorem memberObservation_mapOccurrence (φ : Hom G H) (o : Occurrence G) :
    memberObservation H (φ.mapOccurrence o) = φ.mapMember (memberObservation G o) :=
  Subtype.ext (φ.picture_mapOccurrence o)

/-- Reindex the actual family interpretation along the presentation morphism. -/
def reindexMemberFamily (φ : Hom G H) {F : Occurrence H → Type v}
    (d : FamilyFactorization (memberObservation H) F) :
    FamilyFactorization (memberObservation G) (fun o => F (φ.mapOccurrence o)) :=
  reindexFamily d φ.mapOccurrence (memberObservation G) φ.mapMember
    φ.memberObservation_mapOccurrence

/-- Material-section pullback agrees with occurrence-section pullback. -/
theorem liftMemberSection_reindex (φ : Hom G H) {F : Occurrence H → Type v}
    (d : FamilyFactorization (memberObservation H) F)
    (term : ∀ member, d.targetFamily member) :
    liftSection (φ.reindexMemberFamily d) (fun member => term (φ.mapMember member)) =
      fun occurrence => liftSection d term (φ.mapOccurrence occurrence) :=
  liftSection_reindex d φ.mapOccurrence (memberObservation G) φ.mapMember
    φ.memberObservation_mapOccurrence term

/-- Graph substitution preserves compatible sections without selecting
representatives of material members. -/
theorem compatible_reindexMemberFamily (φ : Hom G H) {F : Occurrence H → Type v}
    (d : FamilyFactorization (memberObservation H) F)
    (term : ∀ occurrence, F occurrence) (compatible : Compatible d term) :
    Compatible (φ.reindexMemberFamily d) (fun o => term (φ.mapOccurrence o)) :=
  compatible_reindex d φ.mapOccurrence (memberObservation G) φ.mapMember
    φ.memberObservation_mapOccurrence term compatible

end Hom

/-! ## Duplicated-child controls -/

/-- The two edges have the same material-member observation. -/
theorem twoChildren_same_member :
    memberObservation twoChildren.{u} (twoChildrenOccurrence true) =
      memberObservation twoChildren (twoChildrenOccurrence false) :=
  Subtype.ext ((twoChildrenOccurrence_picture true).trans
    (twoChildrenOccurrence_picture false).symm)

/-- The edge's Boolean tag is retained at the presentation layer. -/
def edgeTag (o : Occurrence twoChildren.{u}) : Bool :=
  Option.elim o.1 false (fun p => p.1.down)

@[simp] theorem edgeTag_twoChildrenOccurrence (b : Bool) :
    edgeTag (twoChildrenOccurrence.{u} b) = b := rfl

/-- A constant Boolean fibre is a legitimate material-member family. -/
def boolMemberFamily :
    FamilyFactorization (memberObservation twoChildren.{u}) (fun _ => Bool) :=
  FamilyFactorization.constant _ Bool

/-- A constant section descends even though the graph duplicates its member. -/
theorem constant_section_compatible (b : Bool) :
    Compatible boolMemberFamily.{u} (fun _ => b) :=
  liftSection_compatible boolMemberFamily (fun _ => b)

/-- The family descends, but its edge-sensitive section does not. -/
theorem edgeTag_not_compatible : ¬ Compatible boolMemberFamily.{u} edgeTag := by
  intro compatible
  have same := compatible (twoChildrenOccurrence true) (twoChildrenOccurrence false)
    twoChildren_same_member
  have values := eq_of_heq (Sigma.mk.inj_iff.mp same).2
  exact Bool.false_ne_true values.symm

/-- No function on material members reconstructs the edge-sensitive section. -/
theorem edgeTag_not_lifted :
    ¬ ∃ term : PicturedMembers twoChildren.{u} → Bool,
      liftSection boolMemberFamily term = edgeTag := by
  rintro ⟨term, same⟩
  exact edgeTag_not_compatible (same ▸ liftSection_compatible boolMemberFamily term)

/-- Even a descending family does not make its unquotiented total-space
observation injective. -/
theorem boolTotalObservation_not_injective :
    ¬ Function.Injective boolMemberFamily.{u}.totalObservation := by
  intro injective
  have same :
      boolMemberFamily.totalObservation ⟨twoChildrenOccurrence true, true⟩ =
        boolMemberFamily.totalObservation ⟨twoChildrenOccurrence false, true⟩ :=
    congrArg (fun member => (⟨member, true⟩ : Sigma boolMemberFamily.targetFamily))
      twoChildren_same_member
  exact twoChildrenOccurrence_ne (congrArg Sigma.fst (injective same))

/-- An occurrence-sensitive family can have inhabited and empty fibres at
occurrences of the same member. -/
def edgeSelectedFamily (o : Occurrence twoChildren.{u}) : Type :=
  if edgeTag o = true then PUnit else PEmpty

/-- This family itself cannot factor through material members, even up to
fibrewise equivalence. -/
theorem edgeSelectedFamily_not_factors :
    ¬ Nonempty (FamilyFactorization (memberObservation twoChildren.{u}) edgeSelectedFamily) := by
  rintro ⟨d⟩
  let equiv : edgeSelectedFamily (twoChildrenOccurrence true) ≃
      edgeSelectedFamily (twoChildrenOccurrence false) :=
    (d.identify (twoChildrenOccurrence true)).trans
      ((equalityEquiv (congrArg d.targetFamily twoChildren_same_member)).trans
        (d.identify (twoChildrenOccurrence false)).symm)
  have simpler : PUnit ≃ PEmpty := by
    simpa [edgeSelectedFamily] using equiv
  exact (simpler PUnit.unit).elim

end AccessiblePointedGraph

end Mettapedia.TypeTheory.MaterialSets.Hypersets
