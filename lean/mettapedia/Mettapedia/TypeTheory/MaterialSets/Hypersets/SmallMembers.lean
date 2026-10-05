import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyDescent
import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet
import Mettapedia.TypeTheory.FamilyEnclosingUniverse
import Mathlib.Logic.Equiv.Basic

/-!
# Small member types and dependent families of hypersets

`HSet.{u}` lives in `Type (u + 1)`, but the members of each fixed hyperset have
a `Type u` model: quotient the occurrences of a supplied graph by equality of
their material-member observations. The quotient observation is bijective
without choice. Its explicit inverse uses the separately supplied
`OccurrenceRecovery`; it does not silently choose graph occurrences.

The material dependent-sum and dependent-product comparisons then provide
small models of the actual dependent sums and functions. A reduced base and
its reduced fibres also fit the existing family-enclosing semantic capability.
This does not construct native universe syntax or assert that arbitrary
higher-universe families are representable by hypersets at this size.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

namespace AccessiblePointedGraph

/-- Observational equality of occurrences: the same pictured material member. -/
def memberSetoid (G : AccessiblePointedGraph.{u}) : Setoid (Occurrence G) :=
  Setoid.ker (memberObservation G)

/-- A small carrier for the material members of a supplied graph's picture. -/
def SmallMembers (G : AccessiblePointedGraph.{u}) : Type u :=
  Quotient (memberSetoid G)

/-- Observe an occurrence class as its material member. -/
def smallMemberObservation (G : AccessiblePointedGraph.{u}) :
    SmallMembers G → PicturedMembers G :=
  Quotient.lift (memberObservation G) fun _ _ same => same

@[simp] theorem smallMemberObservation_mk (G : AccessiblePointedGraph.{u})
    (o : Occurrence G) :
    smallMemberObservation G (Quotient.mk (memberSetoid G) o) = memberObservation G o := rfl

/-- The occurrence quotient removes exactly the distinctions its readout forgets. -/
theorem smallMemberObservation_injective (G : AccessiblePointedGraph.{u}) :
    Function.Injective (smallMemberObservation G) := by
  intro a b same
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      exact Quotient.sound same

/-- Every material member is pictured by an occurrence class. No selected
occurrence or inverse is needed for this existential statement. -/
theorem smallMemberObservation_surjective (G : AccessiblePointedGraph.{u}) :
    Function.Surjective (smallMemberObservation G) := by
  intro member
  obtain ⟨o, same⟩ := memberObservation_surjective G member
  exact ⟨Quotient.mk _ o, same⟩

theorem smallMemberObservation_bijective (G : AccessiblePointedGraph.{u}) :
    Function.Bijective (smallMemberObservation G) :=
  ⟨smallMemberObservation_injective G, smallMemberObservation_surjective G⟩

/-- A supplied recovery gives an explicit inverse without further selection. -/
def smallMemberEquiv {G : AccessiblePointedGraph.{u}} (r : OccurrenceRecovery G) :
    SmallMembers G ≃ PicturedMembers G where
  toFun := smallMemberObservation G
  invFun member := Quotient.mk _ (r.recover member)
  left_inv member := by
    apply smallMemberObservation_injective G
    exact Subtype.ext (r.picture_recover (smallMemberObservation G member))
  right_inv member := Subtype.ext (r.picture_recover member)

/-- The subtype of material members and the evidence-carrying member type
agree because material membership is a proposition. -/
def picturedMembersEquivEl (G : AccessiblePointedGraph.{u}) :
    PicturedMembers G ≃ El (· ∈ ·) (picture G) where
  toFun member := ⟨member.1, member.2⟩
  invFun member := ⟨member.1, member.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def smallElEquiv {G : AccessiblePointedGraph.{u}} (r : OccurrenceRecovery G) :
    SmallMembers G ≃ El (· ∈ ·) (picture G) :=
  (smallMemberEquiv r).trans (picturedMembersEquivEl G)

theorem small_el_picture {G : AccessiblePointedGraph.{u}} (r : OccurrenceRecovery G) :
    Small.{u} (El (· ∈ ·) (picture G)) :=
  Small.mk' (smallElEquiv r).symm

/-- Duplicated occurrences are identified in the small material carrier. -/
theorem twoChildren_quotient_occurrences_eq :
    Quotient.mk (memberSetoid twoChildren.{u}) (twoChildrenOccurrence true) =
      Quotient.mk (memberSetoid twoChildren) (twoChildrenOccurrence false) :=
  Quotient.sound twoChildren_same_member

/-- Recovery for the duplicated-empty-member example is explicit finite data,
so its small member equivalence needs no classical selector. -/
def twoChildrenRecovery : OccurrenceRecovery twoChildren.{u} where
  recover _ := twoChildrenOccurrence true
  picture_recover member := by
    have hpicture : picture twoChildren.{u} = {∅} :=
      (picture_eq_mk _).trans mk_twoChildren
    have same : member.1 = ∅ := HSet.mem_singleton.mp (hpicture ▸ member.2)
    exact (twoChildrenOccurrence_picture true).trans same.symm

/-- Positive size control: two distinct presentation occurrences have precisely
one small material member class. -/
def twoChildrenMemberEquiv : SmallMembers twoChildren.{u} ≃ PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := Quotient.mk _ (twoChildrenOccurrence true)
  left_inv value := by
    apply smallMemberObservation_injective
    apply Subtype.ext
    let memberValue : HSet.{u} := (smallMemberObservation twoChildren value).1
    have member : memberValue ∈ picture twoChildren := (smallMemberObservation twoChildren value).2
    have hpicture : picture twoChildren.{u} = {∅} :=
      (picture_eq_mk _).trans mk_twoChildren
    have singleton : memberValue ∈ {∅} := hpicture ▸ member
    exact (twoChildrenOccurrence_picture true).trans (HSet.mem_singleton.mp singleton).symm
  right_inv _ := rfl

/-- Size boundary: the type of all types at level `u` cannot be a fixed
hyperset's member type at that same size. -/
theorem no_sameLevel_type_carrier {G : AccessiblePointedGraph.{u}}
    (r : OccurrenceRecovery G) :
    ¬ Nonempty (El (· ∈ ·) (picture G) ≃ Type u) := by
  rintro ⟨e⟩
  exact not_small_type (Small.mk' (e.symm.trans (smallElEquiv r).symm))

end AccessiblePointedGraph

namespace HSet

open AccessiblePointedGraph

/- Equality elimination suffices for the following comparisons. The local
proofs avoid the classical proof wrappers of the library congruence maps. -/

private def piBaseEquiv {α β : Type*} (e : α ≃ β) (P : β → Sort*) :
    (∀ a, P (e a)) ≃ (∀ b, P b) where
  toFun f b := cast (congrArg P (e.apply_symm_apply b)) (f (e.symm b))
  invFun f a := f (e a)
  left_inv f := by
    funext a
    exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq f (e.symm_apply_apply a)))
  right_inv f := by
    funext b
    exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq f (e.apply_symm_apply b)))

private def sectionCongr {α β : Type*} {P : α → Sort*} {Q : β → Sort*}
    (e : α ≃ β) (fibres : ∀ a, P a ≃ Q (e a)) : (∀ a, P a) ≃ (∀ b, Q b) :=
  (Equiv.piCongrRight fibres).trans (piBaseEquiv e Q)

private def sigmaFibreEquiv {α : Type*} {P Q : α → Type*}
    (fibres : ∀ a, P a ≃ Q a) : Sigma P ≃ Sigma Q where
  toFun value := ⟨value.1, fibres value.1 value.2⟩
  invFun value := ⟨value.1, (fibres value.1).symm value.2⟩
  left_inv value := congrArg (Sigma.mk value.1) ((fibres value.1).symm_apply_apply value.2)
  right_inv value := congrArg (Sigma.mk value.1) ((fibres value.1).apply_symm_apply value.2)

private def sumCongr {α β : Type*} {P : α → Type*} {Q : β → Type*}
    (e : α ≃ β) (fibres : ∀ a, P a ≃ Q (e a)) : Sigma P ≃ Sigma Q :=
  (sigmaFibreEquiv fibres).trans (Equiv.sigmaCongrLeft e)

/-- A chosen presentation has a small quotient carrier of its members. -/
abbrev MemberModel (p : Presentation.{u}) (X : HSet.{u}) : Type u :=
  SmallMembers (p.graph X)

/-- An explicit member model equivalence, transported along the supplied
presentation's picture equation. -/
def memberModelEquiv (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) : MemberModel p X ≃ El (· ∈ ·) X :=
  (smallElEquiv r).trans
    (Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
      (congrArg (fun Y => El (· ∈ ·) Y)
    ((picture_eq_mk (p.graph X)).trans (p.mk_graph X))))

theorem small_el (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) : Small.{u} (El (· ∈ ·) X) :=
  Small.mk' (memberModelEquiv p X r).symm

/-- The unconditional metatheoretic smallness statement, with both classical
presentation and occurrence selection explicitly named. No global instance is
installed, so uses of this choice-bearing result remain visible. -/
theorem small_el_classical (X : HSet.{u}) : Small.{u} (El (· ∈ ·) X) :=
  small_el Presentation.choice X (OccurrenceRecovery.classical _)

/-- The material set of dependent pairs supplies a small model of the actual
dependent sum, not just of its bare support predicate. -/
def sigmaMemberModelEquiv (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u})
    (r : OccurrenceRecovery
      (p.graph (sigmaSet (dependentReplacement p) union kuratowski X B))) :
    MemberModel p (sigmaSet (dependentReplacement p) union kuratowski X B) ≃
      Σ' a : El (· ∈ ·) X, El (· ∈ ·) (B a) :=
  (memberModelEquiv p _ r).trans (sigmaSetEquiv p X B)

theorem small_sigma (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u})
    (r : OccurrenceRecovery
      (p.graph (sigmaSet (dependentReplacement p) union kuratowski X B))) :
    Small.{u} (Σ' a : El (· ∈ ·) X, El (· ∈ ·) (B a)) :=
  Small.mk' (sigmaMemberModelEquiv p X B r).symm

/-- The material function-graph set supplies a small model of all actual
dependent functions over an HSet-valued family at the chosen graph size. -/
def piMemberModelEquiv (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u})
    (r : OccurrenceRecovery (p.graph (dependentProduct p X B))) :
    MemberModel p (dependentProduct p X B) ≃ (∀ a, El (· ∈ ·) (B a)) :=
  (memberModelEquiv p _ r).trans (piSetEquiv p X B)

theorem small_pi (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u})
    (r : OccurrenceRecovery (p.graph (dependentProduct p X B))) :
    Small.{u} (∀ a, El (· ∈ ·) (B a)) :=
  Small.mk' (piMemberModelEquiv p X B r).symm

/-- The chosen base's small representation reindexes the material family. -/
def ReducedMemberFamily (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) (B : El (· ∈ ·) X → HSet.{u}) :
    MemberModel p X → Type u :=
  fun a => MemberModel p (B (memberModelEquiv p X r a))

/-- The existing ambient family-enclosing capability can enclose the reduced
base and fibres at `u`, with codes at `u + 1`. This is a semantic capability,
not a native universe calculus or a collecting hyperset of every code. -/
def memberFamilyEnvelope (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) (B : El (· ∈ ·) X → HSet.{u}) :
    FamilyEnclosingUniverse.ClosedTarskiUniverseOver.{u + 1, u}
      (MemberModel p X) (ReducedMemberFamily p X r B) :=
  FamilyEnclosingUniverse.ambientEnvelope _ _

/-- With explicit fibre recovery, dependent functions over the reduced family
are equivalent to the original material-member functions. -/
def reducedPiEquiv (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) (B : El (· ∈ ·) X → HSet.{u})
    (fibres : ∀ a : El (· ∈ ·) X, OccurrenceRecovery (p.graph (B a))) :
    (∀ a, ReducedMemberFamily p X r B a) ≃ (∀ a, El (· ∈ ·) (B a)) :=
  sectionCongr (memberModelEquiv p X r) fun a =>
    memberModelEquiv p (B (memberModelEquiv p X r a))
      (fibres (memberModelEquiv p X r a))

/-- The reduced dependent sum retains the actual material member and its fibre
value through the base and fibre equivalences. -/
def reducedSigmaEquiv (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) (B : El (· ∈ ·) X → HSet.{u})
    (fibres : ∀ a : El (· ∈ ·) X, OccurrenceRecovery (p.graph (B a))) :
    (Σ a, ReducedMemberFamily p X r B a) ≃ Σ' a : El (· ∈ ·) X, El (· ∈ ·) (B a) :=
  (sumCongr (memberModelEquiv p X r) fun a =>
    memberModelEquiv p (B (memberModelEquiv p X r a))
      (fibres (memberModelEquiv p X r a))).trans (Equiv.psigmaEquivSigma _).symm

/-- A family-enclosing universe's selected Pi code decodes to actual dependent
functions on material members after the explicit size comparisons. -/
def memberFamilyEnvelopePiEquiv (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) (B : El (· ∈ ·) X → HSet.{u})
    (fibres : ∀ a : El (· ∈ ·) X, OccurrenceRecovery (p.graph (B a))) :
    let envelope := memberFamilyEnvelope p X r B
    envelope.El (envelope.piCode envelope.baseCode
      (fun a => envelope.fibreCode (envelope.elBase a))) ≃
      (∀ a, El (· ∈ ·) (B a)) :=
  let envelope := memberFamilyEnvelope p X r B
  (envelope.elPi _ _).trans
    ((sectionCongr envelope.elBase fun a => envelope.elFibre (envelope.elBase a)).trans
      (reducedPiEquiv p X r B fibres))

/-- The selected Sigma code likewise decodes to actual evidence-carrying
dependent pairs on the material-member family. -/
def memberFamilyEnvelopeSigmaEquiv (p : Presentation.{u}) (X : HSet.{u})
    (r : OccurrenceRecovery (p.graph X)) (B : El (· ∈ ·) X → HSet.{u})
    (fibres : ∀ a : El (· ∈ ·) X, OccurrenceRecovery (p.graph (B a))) :
    let envelope := memberFamilyEnvelope p X r B
    envelope.El (envelope.sigmaCode envelope.baseCode
      (fun a => envelope.fibreCode (envelope.elBase a))) ≃
      Σ' a : El (· ∈ ·) X, El (· ∈ ·) (B a) :=
  let envelope := memberFamilyEnvelope p X r B
  (envelope.elSigma _ _).trans
    ((sumCongr envelope.elBase fun a => envelope.elFibre (envelope.elBase a)).trans
      (reducedSigmaEquiv p X r B fibres))

/-- Even when every fixed member type has a small model, the whole ambient
hyperset carrier does not: otherwise a small graph family would collect it. -/
theorem not_small_hset (p : Presentation.{u}) : ¬ Small.{u} HSet.{u} := by
  rintro ⟨⟨α, ⟨e⟩⟩⟩
  apply not_exists_universal
  refine ⟨range (fun a : α => p.graph (e.symm a)), fun x => ?_⟩
  exact mem_range.mpr ⟨e x, (p.mk_graph _).trans (e.symm_apply_apply x)⟩

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
