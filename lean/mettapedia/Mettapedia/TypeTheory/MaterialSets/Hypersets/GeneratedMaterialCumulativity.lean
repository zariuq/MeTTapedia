import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeCumulativity

/-!
# Cumulative interpretation of the whole generated material core

Every core derivation is translated to the successor grammar by recursively
lifting its decoded types. Dependent positions and families are reindexed by
explicit equivalences. The constructed material encodings commute with the
universe lift, while presentation graphs are compared by bisimilarity.

The enclosure of exactly translated derivations is the lifted original
enclosure. It is included in the enclosure of the whole successor grammar;
the latter has additional derivations, and no equality of those grammars or
internal transfinite closure principle is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialCumulativity

open Mettapedia.TypeTheory.FamilyEnclosingUniverse
open GeneratedMaterialDecoder
open PresentedTypeCumulativity

universe u

/-- Translation retains an actual successor formation derivation and an
explicit semantic comparison, including each recursively dependent branch. -/
structure Raised (A : Type u) (B : A → Type u) (T : Type u) : Type (u + 2) where
  Target : Type (u + 1)
  derivation : CoreGeneration (ULift.{u + 1, u} A) (fun a => ULift.{u + 1, u} (B a.down)) Target
  comparison : Target ≃ T

def raise {A : Type u} {B : A → Type u} :
    {T : Type u} → CoreGeneration A B T → Raised A B T
  | _, .base => ⟨ULift.{u + 1, u} A, .base, Equiv.ulift⟩
  | _, .fibre a => ⟨ULift.{u + 1, u} (B a), .fibre (⟨a⟩ : ULift.{u + 1, u} A), Equiv.ulift⟩
  | _, .empty => ⟨ULift.{u + 1, 0} Empty, .empty, Equiv.ulift.trans Equiv.ulift.symm⟩
  | _, .unit => ⟨ULift.{u + 1, 0} PUnit, .unit, Equiv.ulift.trans Equiv.ulift.symm⟩
  | _, .pi domain codomain =>
    let d := raise domain
    let c := fun a => raise (codomain (d.comparison a))
    ⟨(a : d.Target) → (c a).Target, .pi d.derivation (fun a => (c a).derivation),
      piEquiv d.comparison (fun a => (c a).comparison)⟩
  | _, .sigma domain codomain =>
    let d := raise domain
    let c := fun a => raise (codomain (d.comparison a))
    ⟨Sigma (fun a => (c a).Target), .sigma d.derivation (fun a => (c a).derivation),
      sigmaEquiv d.comparison (fun a => (c a).comparison)⟩
  | _, .identity domain left right =>
    let d := raise domain
    ⟨ULift.{u + 1, 0} (PLift (d.comparison.symm left = d.comparison.symm right)),
      .identity d.derivation (d.comparison.symm left) (d.comparison.symm right),
      identityEquiv d.comparison left right⟩
  | _, .w shape position =>
    let d := raise shape
    let c := fun a => raise (position (d.comparison a))
    ⟨WTree d.Target (fun a => (c a).Target), .w d.derivation (fun a => (c a).derivation),
      Trees.equiv d.comparison (fun a => (c a).comparison)⟩

variable {A : Type u} {B : A → Type u}

def upperModel (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T) : PresentedType (raise derivation).Target :=
  (raise derivation).derivation.interpret (liftModel baseModel) (fun a => liftModel (fibreModels a.down))

/-- Every material constructor has a proved lifting comparison. The proof
recurses through arbitrary families rather than only named seed codes. -/
theorem value_lift (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    ∀ term : (raise derivation).Target,
      (upperModel baseModel fibreModels derivation).value term =
        HSet.lift ((derivation.interpret baseModel fibreModels).value ((raise derivation).comparison term)) := by
  induction derivation with
  | base => exact liftModel_value baseModel
  | fibre a => exact liftModel_value (fibreModels a)
  | empty => intro term; exact term.down.elim
  | unit =>
    intro term
    change ∅ = HSet.lift (∅ : HSet.{u})
    exact HSet.lift_empty.symm
  | pi domain codomain earlierDomain earlierCodomain =>
    exact product_value (domain.interpret baseModel fibreModels) (fun a => (codomain a).interpret baseModel fibreModels)
      (upperModel baseModel fibreModels domain)
      (fun a => upperModel baseModel fibreModels (codomain ((raise domain).comparison a)))
      (raise domain).comparison (fun a => (raise (codomain ((raise domain).comparison a))).comparison)
      earlierDomain (fun a => earlierCodomain ((raise domain).comparison a))
  | sigma domain codomain earlierDomain earlierCodomain =>
    exact sum_value (domain.interpret baseModel fibreModels) (fun a => (codomain a).interpret baseModel fibreModels)
      (upperModel baseModel fibreModels domain)
      (fun a => upperModel baseModel fibreModels (codomain ((raise domain).comparison a)))
      (raise domain).comparison (fun a => (raise (codomain ((raise domain).comparison a))).comparison)
      earlierDomain (fun a => earlierCodomain ((raise domain).comparison a))
  | identity domain left right _ =>
    exact identity_value (domain.interpret baseModel fibreModels) (upperModel baseModel fibreModels domain)
      (raise domain).comparison left right
  | w shape position earlierShape earlierPosition =>
    exact w_value (shape.interpret baseModel fibreModels) (fun a => (position a).interpret baseModel fibreModels)
      (upperModel baseModel fibreModels shape)
      (fun a => upperModel baseModel fibreModels (position ((raise shape).comparison a)))
      (raise shape).comparison (fun a => (raise (position ((raise shape).comparison a))).comparison)
      earlierShape (fun a => earlierPosition ((raise shape).comparison a))

theorem carrier_lift (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    (upperModel baseModel fibreModels derivation).carrier =
      HSet.lift (derivation.interpret baseModel fibreModels).carrier :=
  carrier_eq_lift_of_values _ _ _ (value_lift baseModel fibreModels derivation)

def members (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    {value : HSet.{u + 1} // value ∈ (upperModel baseModel fibreModels derivation).carrier} ≃
      {value : HSet.{u} // value ∈ (derivation.interpret baseModel fibreModels).carrier} :=
  memberEquiv _ _ (raise derivation).comparison

theorem members_value (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (member : {value : HSet.{u + 1} // value ∈ (upperModel baseModel fibreModels derivation).carrier}) :
    HSet.lift (members baseModel fibreModels derivation member).1 = member.1 :=
  memberEquiv_value _ _ _ (value_lift baseModel fibreModels derivation) member

theorem members_decode (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (member : {value : HSet.{u + 1} // value ∈ (upperModel baseModel fibreModels derivation).carrier}) :
    (derivation.interpret baseModel fibreModels).decode (members baseModel fibreModels derivation member) =
      (raise derivation).comparison ((upperModel baseModel fibreModels derivation).decode member) :=
  decode_memberEquiv _ _ _ member

theorem termGraph_lift (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T) (term : (raise derivation).Target) :
    (upperModel baseModel fibreModels derivation).termGraph term ≈
      ((derivation.interpret baseModel fibreModels).termGraph ((raise derivation).comparison term)).lift :=
  termGraph_bisimilar _ _ _ (value_lift baseModel fibreModels derivation) term

section Substitution

variable {C : Type u} {D : C → Type u}

/-- The two successor routes can have different target types and codes.
Their comparison retains their common original decoding. -/
def substitutionComparison (baseDerivation : CoreGeneration C D A)
    (fibres : (a : A) → CoreGeneration C D (B a)) {T : Type u} (derivation : CoreGeneration A B T) :
    (raise (CoreGeneration.substitute baseDerivation fibres derivation)).Target ≃ (raise derivation).Target :=
  (raise (CoreGeneration.substitute baseDerivation fibres derivation)).comparison.trans (raise derivation).comparison.symm

theorem value_substitution (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (term : (raise (CoreGeneration.substitute baseDerivation fibres derivation)).Target) :
    (upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).value term =
      (upperModel (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) derivation).value
          (substitutionComparison baseDerivation fibres derivation term) := by
  rw [value_lift, value_lift]
  change HSet.lift _ = HSet.lift ((derivation.interpret _ _).value
    ((raise derivation).comparison ((raise derivation).comparison.symm _)))
  rw [Equiv.apply_symm_apply]
  exact congrArg HSet.lift
    (CoreGeneration.value_substitute baseModel fibreModels baseDerivation fibres derivation _)

theorem carrier_substitution (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    (upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).carrier =
      (upperModel (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) derivation).carrier := by
  rw [carrier_lift, carrier_lift]
  exact congrArg (fun model => HSet.lift model.carrier)
    (CoreGeneration.interpret_substitute baseModel fibreModels baseDerivation fibres derivation)

def substitutionMembers (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    {value : HSet.{u + 1} // value ∈
      (upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).carrier} ≃
    {value : HSet.{u + 1} // value ∈
      (upperModel (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) derivation).carrier} :=
  ((upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).decode.trans
    (substitutionComparison baseDerivation fibres derivation)).trans
      (upperModel (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) derivation).decode.symm

theorem substitutionMembers_value (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (member : {value : HSet.{u + 1} // value ∈
      (upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).carrier}) :
    (substitutionMembers baseModel fibreModels baseDerivation fibres derivation member).1 = member.1 :=
  (value_substitution baseModel fibreModels baseDerivation fibres derivation _).symm.trans
    ((upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).value_decode member)

theorem substitutionMembers_decode (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (member : {value : HSet.{u + 1} // value ∈
      (upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).carrier}) :
    (upperModel (baseDerivation.interpret baseModel fibreModels)
      (fun a => (fibres a).interpret baseModel fibreModels) derivation).decode
        (substitutionMembers baseModel fibreModels baseDerivation fibres derivation member) =
      substitutionComparison baseDerivation fibres derivation
        ((upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).decode member) :=
  (upperModel _ _ _).decode.apply_symm_apply _

theorem termGraph_substitution (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (term : (raise (CoreGeneration.substitute baseDerivation fibres derivation)).Target) :
    (upperModel baseModel fibreModels (CoreGeneration.substitute baseDerivation fibres derivation)).termGraph term ≈
      (upperModel (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) derivation).termGraph
          (substitutionComparison baseDerivation fibres derivation term) := by
  apply HSet.mk_eq_mk_iff.mp
  rw [PresentedType.mk_termGraph, PresentedType.mk_termGraph]
  exact value_substitution baseModel fibreModels baseDerivation fibres derivation term

end Substitution

section Enclosures

/-- Collect actual carriers of exactly the translated lower derivations. This
index is explicit and need not coincide with all successor derivations. -/
def translatedEnclosure (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a)) :
    HSet.{u + 2} :=
  HSet.imageUp fun code : ULift.{u + 2, u + 1} (CoreCode A B) =>
    (upperModel baseModel fibreModels code.down.2).carrier

theorem translatedEnclosure_eq_lift (baseModel : PresentedType A)
    (fibreModels : (a : A) → PresentedType (B a)) :
    translatedEnclosure baseModel fibreModels = HSet.lift (modelEnclosure baseModel fibreModels) := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨code, same⟩ := HSet.mem_imageUp_iff.mp member
    apply HSet.mem_lift_iff.mpr
    refine ⟨HSet.lift (code.down.2.interpret baseModel fibreModels).carrier,
      mem_modelEnclosure_iff.mpr ⟨code.down, rfl⟩, ?_⟩
    exact (congrArg HSet.lift (carrier_lift baseModel fibreModels code.down.2)).symm.trans same
  · intro member
    obtain ⟨old, oldMember, same⟩ := HSet.mem_lift_iff.mp member
    obtain ⟨code, oldValue⟩ := mem_modelEnclosure_iff.mp oldMember
    exact HSet.mem_imageUp_iff.mpr ⟨ULift.up code,
      (congrArg HSet.lift (carrier_lift baseModel fibreModels code.2)).trans
        ((congrArg HSet.lift oldValue).trans same)⟩

theorem translatedEnclosure_subset (baseModel : PresentedType A)
    (fibreModels : (a : A) → PresentedType (B a)) :
    translatedEnclosure baseModel fibreModels ⊆
      modelEnclosure (liftModel baseModel) (fun a => liftModel (fibreModels a.down)) := by
  intro value member
  obtain ⟨code, same⟩ := HSet.mem_imageUp_iff.mp member
  exact mem_modelEnclosure_iff.mpr ⟨⟨(raise code.down.2).Target, (raise code.down.2).derivation⟩, same⟩

theorem enclosure_lift_subset (baseModel : PresentedType A)
    (fibreModels : (a : A) → PresentedType (B a)) :
    HSet.lift (modelEnclosure baseModel fibreModels) ⊆
      modelEnclosure (liftModel baseModel) (fun a => liftModel (fibreModels a.down)) := by
  rw [← translatedEnclosure_eq_lift]
  exact translatedEnclosure_subset baseModel fibreModels

/-- Family substitution and successor translation agree on the actual
collected carriers. The upper whole-grammar enclosure remains an inclusion. -/
theorem enclosure_substitution_subset {C : Type u} {D : C → Type u}
    (baseModel : PresentedType C) (fibreModels : (c : C) → PresentedType (D c))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a)) :
    translatedEnclosure (baseDerivation.interpret baseModel fibreModels)
        (fun a => (fibres a).interpret baseModel fibreModels) ⊆
      modelEnclosure (liftModel baseModel) (fun c => liftModel (fibreModels c.down)) := by
  intro value member
  rw [translatedEnclosure_eq_lift] at member
  obtain ⟨old, oldMember, same⟩ := HSet.mem_lift_iff.mp member
  exact enclosure_lift_subset baseModel fibreModels
    (HSet.mem_lift_iff.mpr ⟨old,
      modelEnclosure_substitute_subset baseModel fibreModels baseDerivation fibres oldMember, same⟩)

open LiftedFamilyModel (Elements)

/-- This successor enclosure has entirely constructed generators for any
bare material family. Its graph and code bounds are displayed explicitly. -/
def successorCodeEnclosure (X : HSet.{u}) (family : Elements X → HSet.{u}) : HSet.{u + 3} :=
  modelEnclosure (liftModel (liftedModel X)) (fun a => liftModel (liftedModel (family a.down)))

theorem codeEnclosure_lift_subset (X : HSet.{u}) (family : Elements X → HSet.{u}) :
    HSet.lift (codeEnclosure X family) ⊆ successorCodeEnclosure X family :=
  enclosure_lift_subset (liftedModel X) (fun a => liftedModel (family a))

end Enclosures

section TwoSuccessors

def twiceComparison {T : Type u} (derivation : CoreGeneration A B T) :
    (raise (raise derivation).derivation).Target ≃ T :=
  (raise (raise derivation).derivation).comparison.trans (raise derivation).comparison

theorem value_two_lifts (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (term : (raise (raise derivation).derivation).Target) :
    (upperModel (liftModel baseModel) (fun a => liftModel (fibreModels a.down))
      (raise derivation).derivation).value term =
      HSet.lift (HSet.lift ((derivation.interpret baseModel fibreModels).value (twiceComparison derivation term))) := by
  rw [value_lift]
  exact congrArg HSet.lift (value_lift baseModel fibreModels derivation _)

theorem carrier_two_lifts (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    (upperModel (liftModel baseModel) (fun a => liftModel (fibreModels a.down))
      (raise derivation).derivation).carrier =
      HSet.lift (HSet.lift (derivation.interpret baseModel fibreModels).carrier) := by
  rw [carrier_lift]
  exact congrArg HSet.lift (carrier_lift baseModel fibreModels derivation)

end TwoSuccessors

section Controls

/-- An arbitrary dependent position, including an infinite one, remains a
labelled material row after lifting the whole generated W constructor. -/
theorem w_position_lift (baseModel : PresentedType A) (fibreModels : (a : A) → PresentedType (B a))
    (shape : A) (children : B shape → WTree A B) (position : B shape) :
    HSet.lift (HSet.kpair (PresentedType.W.positionTag baseModel fibreModels shape position)
      (PresentedType.W.encode baseModel fibreModels (children position))) ∈
      (upperModel baseModel fibreModels (CoreGeneration.w .base .fibre)).value
        ((raise (CoreGeneration.w .base .fibre)).comparison.symm (.sup shape children)) := by
  rw [value_lift, Equiv.apply_symm_apply]
  apply HSet.lift_mem_lift_iff.mpr
  change _ ∈ PresentedType.W.encode baseModel fibreModels (.sup shape children)
  exact (PresentedType.W.mem_encode_sup_iff baseModel fibreModels shape children _).mpr
    (Or.inr ⟨position, rfl⟩)

/-- A permutation changing an addressed child cannot become invisible under
the cumulative embedding, even if it preserves the unaddressed child bag. -/
theorem w_permutation_changes_lifted_value (baseModel : PresentedType A)
    (fibreModels : (a : A) → PresentedType (B a)) (shape : A) (children : B shape → WTree A B)
    (permutation : B shape ≃ B shape) (position : B shape)
    (different : children position ≠ children (permutation position)) :
    (upperModel baseModel fibreModels (CoreGeneration.w .base .fibre)).value
        ((raise (CoreGeneration.w .base .fibre)).comparison.symm (.sup shape children)) ≠
      (upperModel baseModel fibreModels (CoreGeneration.w .base .fibre)).value
        ((raise (CoreGeneration.w .base .fibre)).comparison.symm
          (.sup shape (fun p => children (permutation p)))) := by
  intro same
  rw [value_lift, value_lift, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at same
  have encoded := HSet.lift_injective same
  change PresentedType.W.encode baseModel fibreModels (.sup shape children) =
    PresentedType.W.encode baseModel fibreModels (.sup shape (fun p => children (permutation p))) at encoded
  have observed := (PresentedType.W.mem_encode_sup_iff baseModel fibreModels shape children _).mpr
    (Or.inr ⟨position, rfl⟩)
  rw [encoded] at observed
  exact different (PresentedType.W.encode_injective baseModel fibreModels
    ((PresentedType.W.positionObservation_sup_iff baseModel fibreModels shape _ position _).mp observed))

open LiftedFamilyModel (Elements)

/-- The nested nonconstant singleton family retains two material observations
and its actual equality term through the successor comparison. -/
theorem singleton_nested_lifted_entry (X : HSet.{u}) (a : Elements X) :
    HSet.kpair (HSet.lift (HSet.lift a.1)) (HSet.kpair (HSet.lift (HSet.lift a.1)) ∅) ∈
      (upperModel (liftedModel X) (fun a => liftedModel (singletonFamily a))
        (pairedIdentitySections X singletonFamily)).value
          ((raise (pairedIdentitySections X singletonFamily)).comparison.symm (singletonIdentitySection X)) := by
  rw [value_lift, Equiv.apply_symm_apply]
  have row := HSet.lift_mem_lift_iff.mpr (singletonIdentitySection_entry X a)
  simpa only [HSet.lift_kpair, HSet.lift_empty, interpretFamily] using row

theorem quine_nested_lifted_entry :
    HSet.kpair HSet.quineAtom.{u + 2} (HSet.kpair HSet.quineAtom ∅) ∈
      (upperModel (liftedModel ({HSet.quineAtom.{u}} : HSet.{u}))
        (fun a => liftedModel (singletonFamily a))
        (pairedIdentitySections {HSet.quineAtom} singletonFamily)).value
          ((raise (pairedIdentitySections {HSet.quineAtom} singletonFamily)).comparison.symm
            (singletonIdentitySection {HSet.quineAtom})) := by
  simpa only [HSet.lift_quineAtom] using singleton_nested_lifted_entry
    ({HSet.quineAtom.{u}} : HSet.{u}) ⟨HSet.quineAtom, HSet.mem_singleton_self _⟩

theorem nested_empty_fibre_stays_empty {X : HSet.{u}} {family : Elements X → HSet.{u}}
    (a : Elements X) (empty : family a = ∅) :
    (upperModel (liftedModel X) (fun a => liftedModel (family a))
      (pairedIdentitySections X family)).carrier = ∅ := by
  rw [carrier_lift]
  change HSet.lift (typeValue X family (pairedIdentitySections X family)) = ∅
  rw [pairedIdentitySections_empty_of_empty_fibre a empty, HSet.lift_empty]

theorem identity_positions_stay_empty (X : HSet.{u}) (family : Elements X → HSet.{u}) :
    (upperModel (liftedModel X) (fun a => liftedModel (family a)) (identityPositions X family)).carrier = ∅ := by
  rw [carrier_lift]
  change HSet.lift (typeValue X family (identityPositions X family)) = ∅
  rw [identityPositions_empty, HSet.lift_empty]

/-- Constructed successor code enclosures still have an explicit missing
Russell hyperset; no universal-set rule follows from cumulative inclusion. -/
theorem successorCodeEnclosure_russell_notMem (X : HSet.{u}) (family : Elements X → HSet.{u}) :
    HSet.russell (successorCodeEnclosure X family) ∉ successorCodeEnclosure X family := HSet.russell_notMem _

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialCumulativity
