import Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialCumulativity

/-!
# Actual material-family reindexing of cumulative core interpretations

The successor translation can use actual members of a lifted material base
and fibre, rather than only ULift carriers. Bounded union constructs the
original member readout. Reindexing every core formation derivation preserves
the whole dependent interpretation and its material values after lifting.

For any bare family of `HSet.{u}`, the constructed interpretation at `u + 1`
is compared to the interpretation of its actual lifted family at `u + 2`.
Its existing code enclosure at `u + 2` embeds in the lifted-family code
enclosure at `u + 3`. All displayed bounds are external successor bounds.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialReindexing

open Mettapedia.TypeTheory.FamilyEnclosingUniverse
open GeneratedMaterialDecoder
open PresentedTypeCumulativity
open LiftedFamilyModel (Elements)

universe u

structure Translation (A' : Type (u + 1)) (B' : A' → Type (u + 1)) (T : Type u) : Type (u + 2) where
  Target : Type (u + 1)
  derivation : CoreGeneration A' B' Target
  comparison : Target ≃ T

private def castEquiv {T S : Type u} (same : T = S) : T ≃ S where
  toFun := cast same
  invFun := cast same.symm
  left_inv term := by cases same; rfl
  right_inv term := by cases same; rfl

variable {A : Type u} {B : A → Type u} {A' : Type (u + 1)} {B' : A' → Type (u + 1)}

def translate (base : A' ≃ A) (family : ∀ a', B' a' ≃ B (base a')) :
    {T : Type u} → CoreGeneration A B T → Translation A' B' T
  | _, .base => ⟨A', .base, base⟩
  | _, .fibre a => ⟨B' (base.symm a), .fibre (base.symm a),
      (family (base.symm a)).trans (castEquiv (congrArg B (base.apply_symm_apply a)))⟩
  | _, .empty => ⟨ULift.{u + 1, 0} Empty, .empty, Equiv.ulift.trans Equiv.ulift.symm⟩
  | _, .unit => ⟨ULift.{u + 1, 0} PUnit, .unit, Equiv.ulift.trans Equiv.ulift.symm⟩
  | _, .pi domain codomain =>
    let d := translate base family domain
    let c := fun a => translate base family (codomain (d.comparison a))
    ⟨(a : d.Target) → (c a).Target, .pi d.derivation (fun a => (c a).derivation),
      piEquiv d.comparison (fun a => (c a).comparison)⟩
  | _, .sigma domain codomain =>
    let d := translate base family domain
    let c := fun a => translate base family (codomain (d.comparison a))
    ⟨Sigma (fun a => (c a).Target), .sigma d.derivation (fun a => (c a).derivation),
      sigmaEquiv d.comparison (fun a => (c a).comparison)⟩
  | _, .identity domain left right =>
    let d := translate base family domain
    ⟨ULift.{u + 1, 0} (PLift (d.comparison.symm left = d.comparison.symm right)),
      .identity d.derivation (d.comparison.symm left) (d.comparison.symm right),
      identityEquiv d.comparison left right⟩
  | _, .w shape position =>
    let d := translate base family shape
    let c := fun a => translate base family (position (d.comparison a))
    ⟨WTree d.Target (fun a => (c a).Target), .w d.derivation (fun a => (c a).derivation),
      Trees.equiv d.comparison (fun a => (c a).comparison)⟩

def translatedModel (upperBase : PresentedType A') (upperFibres : ∀ a', PresentedType (B' a'))
    (base : A' ≃ A) (family : ∀ a', B' a' ≃ B (base a'))
    {T : Type u} (derivation : CoreGeneration A B T) : PresentedType (translate base family derivation).Target :=
  (translate base family derivation).derivation.interpret upperBase upperFibres

theorem translated_value (originalBase : PresentedType A) (originalFibres : ∀ a, PresentedType (B a))
    (upperBase : PresentedType A') (upperFibres : ∀ a', PresentedType (B' a'))
    (base : A' ≃ A) (family : ∀ a', B' a' ≃ B (base a'))
    (baseValues : ∀ a', upperBase.value a' = HSet.lift (originalBase.value (base a')))
    (fibreValues : ∀ a' b', (upperFibres a').value b' =
      HSet.lift ((originalFibres (base a')).value (family a' b')))
    {T : Type u} (derivation : CoreGeneration A B T) :
    ∀ term, (translatedModel upperBase upperFibres base family derivation).value term =
      HSet.lift ((derivation.interpret originalBase originalFibres).value
        ((translate base family derivation).comparison term)) := by
  induction derivation with
  | base => exact baseValues
  | fibre a =>
    intro term
    exact (fibreValues (base.symm a) term).trans
      (congrArg HSet.lift (PresentedType.value_cast originalFibres (base.apply_symm_apply a)
        (family (base.symm a) term)))
  | empty => intro term; exact term.down.elim
  | unit => intro term; change ∅ = HSet.lift (∅ : HSet.{u}); exact HSet.lift_empty.symm
  | pi domain codomain earlierDomain earlierCodomain =>
    exact product_value (domain.interpret originalBase originalFibres)
      (fun a => (codomain a).interpret originalBase originalFibres)
      (translatedModel upperBase upperFibres base family domain)
      (fun a => translatedModel upperBase upperFibres base family
        (codomain ((translate base family domain).comparison a)))
      (translate base family domain).comparison
      (fun a => (translate base family (codomain ((translate base family domain).comparison a))).comparison)
      earlierDomain (fun a => earlierCodomain ((translate base family domain).comparison a))
  | sigma domain codomain earlierDomain earlierCodomain =>
    exact sum_value (domain.interpret originalBase originalFibres)
      (fun a => (codomain a).interpret originalBase originalFibres)
      (translatedModel upperBase upperFibres base family domain)
      (fun a => translatedModel upperBase upperFibres base family
        (codomain ((translate base family domain).comparison a)))
      (translate base family domain).comparison
      (fun a => (translate base family (codomain ((translate base family domain).comparison a))).comparison)
      earlierDomain (fun a => earlierCodomain ((translate base family domain).comparison a))
  | identity domain left right _ =>
    exact identity_value (domain.interpret originalBase originalFibres)
      (translatedModel upperBase upperFibres base family domain)
      (translate base family domain).comparison left right
  | w shape position earlierShape earlierPosition =>
    exact w_value (shape.interpret originalBase originalFibres)
      (fun a => (position a).interpret originalBase originalFibres)
      (translatedModel upperBase upperFibres base family shape)
      (fun a => translatedModel upperBase upperFibres base family
        (position ((translate base family shape).comparison a)))
      (translate base family shape).comparison
      (fun a => (translate base family (position ((translate base family shape).comparison a))).comparison)
      earlierShape (fun a => earlierPosition ((translate base family shape).comparison a))

section CodeSubstitution

variable {C : Type u} {D : C → Type u} {C' : Type (u + 1)} {D' : C' → Type (u + 1)}

/-- Translate generator derivations and substitute their actual successor
codes into the translated body. Every target branch is constructed data. -/
def substituteTranslation (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) : Translation C' D' T :=
  let d := translate base family baseDerivation
  let c := fun a => translate base family (fibres (d.comparison a))
  let body := translate d.comparison (fun a => (c a).comparison) derivation
  ⟨body.Target, CoreGeneration.substitute d.derivation (fun a => (c a).derivation) body.derivation,
    body.comparison⟩

theorem substituteTranslation_value (originalBase : PresentedType C) (originalFibres : ∀ c, PresentedType (D c))
    (upperBase : PresentedType C') (upperFibres : ∀ c', PresentedType (D' c'))
    (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseValues : ∀ c', upperBase.value c' = HSet.lift (originalBase.value (base c')))
    (fibreValues : ∀ c' d', (upperFibres c').value d' =
      HSet.lift ((originalFibres (base c')).value (family c' d')))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (term : (substituteTranslation base family baseDerivation fibres derivation).Target) :
    ((substituteTranslation base family baseDerivation fibres derivation).derivation.interpret upperBase upperFibres).value term =
      HSet.lift ((CoreGeneration.substitute baseDerivation fibres derivation).interpret originalBase originalFibres |>.value
        ((substituteTranslation base family baseDerivation fibres derivation).comparison term)) := by
  let d := translate base family baseDerivation
  let c := fun a => translate base family (fibres (d.comparison a))
  let body := translate d.comparison (fun a => (c a).comparison) derivation
  change ((CoreGeneration.substitute d.derivation (fun a => (c a).derivation) body.derivation).interpret
      upperBase upperFibres).value term =
    HSet.lift (((CoreGeneration.substitute baseDerivation fibres derivation).interpret originalBase originalFibres).value
      (body.comparison term))
  rw [CoreGeneration.interpret_substitute, CoreGeneration.interpret_substitute]
  exact translated_value (baseDerivation.interpret originalBase originalFibres)
    (fun a => (fibres a).interpret originalBase originalFibres)
    (translatedModel upperBase upperFibres base family baseDerivation)
    (fun a => translatedModel upperBase upperFibres base family (fibres (d.comparison a)))
    d.comparison (fun a => (c a).comparison)
    (translated_value originalBase originalFibres upperBase upperFibres base family baseValues fibreValues baseDerivation)
    (fun a => translated_value originalBase originalFibres upperBase upperFibres base family baseValues fibreValues
      (fibres (d.comparison a))) derivation term

def substitutionComparison (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    (translate base family (CoreGeneration.substitute baseDerivation fibres derivation)).Target ≃
      (substituteTranslation base family baseDerivation fibres derivation).Target :=
  (translate base family (CoreGeneration.substitute baseDerivation fibres derivation)).comparison.trans
    (substituteTranslation base family baseDerivation fibres derivation).comparison.symm

/-- Direct translation and translated-code substitution have the same actual
material values under their explicit semantic comparison. No code equality
or literal node-carrier equality is required. -/
theorem value_substitution (originalBase : PresentedType C) (originalFibres : ∀ c, PresentedType (D c))
    (upperBase : PresentedType C') (upperFibres : ∀ c', PresentedType (D' c'))
    (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseValues : ∀ c', upperBase.value c' = HSet.lift (originalBase.value (base c')))
    (fibreValues : ∀ c' d', (upperFibres c').value d' =
      HSet.lift ((originalFibres (base c')).value (family c' d')))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (term : (translate base family (CoreGeneration.substitute baseDerivation fibres derivation)).Target) :
    (translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).value term =
      ((substituteTranslation base family baseDerivation fibres derivation).derivation.interpret upperBase upperFibres).value
        (substitutionComparison base family baseDerivation fibres derivation term) := by
  rw [translated_value originalBase originalFibres upperBase upperFibres base family baseValues fibreValues,
    substituteTranslation_value originalBase originalFibres upperBase upperFibres base family baseValues fibreValues]
  exact congrArg (fun t => HSet.lift
    (((CoreGeneration.substitute baseDerivation fibres derivation).interpret originalBase originalFibres).value t))
      ((substituteTranslation base family baseDerivation fibres derivation).comparison.apply_symm_apply _).symm

theorem carrier_substitution (originalBase : PresentedType C) (originalFibres : ∀ c, PresentedType (D c))
    (upperBase : PresentedType C') (upperFibres : ∀ c', PresentedType (D' c'))
    (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseValues : ∀ c', upperBase.value c' = HSet.lift (originalBase.value (base c')))
    (fibreValues : ∀ c' d', (upperFibres c').value d' =
      HSet.lift ((originalFibres (base c')).value (family c' d')))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    (translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).carrier =
      ((substituteTranslation base family baseDerivation fibres derivation).derivation.interpret upperBase upperFibres).carrier :=
  (carrier_eq_lift_of_values _ _ _
    (translated_value originalBase originalFibres upperBase upperFibres base family baseValues fibreValues
      (CoreGeneration.substitute baseDerivation fibres derivation))).trans
    (carrier_eq_lift_of_values _ _ _
      (substituteTranslation_value originalBase originalFibres upperBase upperFibres base family baseValues fibreValues
        baseDerivation fibres derivation)).symm

def substitutionMembers (upperBase : PresentedType C') (upperFibres : ∀ c', PresentedType (D' c'))
    (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T) :
    {value : HSet.{u + 1} // value ∈
      (translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).carrier} ≃
    {value : HSet.{u + 1} // value ∈
      ((substituteTranslation base family baseDerivation fibres derivation).derivation.interpret upperBase upperFibres).carrier} :=
  ((translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).decode.trans
    (substitutionComparison base family baseDerivation fibres derivation)).trans
      ((substituteTranslation base family baseDerivation fibres derivation).derivation.interpret upperBase upperFibres).decode.symm

theorem substitutionMembers_value (originalBase : PresentedType C) (originalFibres : ∀ c, PresentedType (D c))
    (upperBase : PresentedType C') (upperFibres : ∀ c', PresentedType (D' c'))
    (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseValues : ∀ c', upperBase.value c' = HSet.lift (originalBase.value (base c')))
    (fibreValues : ∀ c' d', (upperFibres c').value d' =
      HSet.lift ((originalFibres (base c')).value (family c' d')))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (member : {value : HSet.{u + 1} // value ∈
      (translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).carrier}) :
    (substitutionMembers upperBase upperFibres base family baseDerivation fibres derivation member).1 = member.1 :=
  (value_substitution originalBase originalFibres upperBase upperFibres base family baseValues fibreValues
    baseDerivation fibres derivation _).symm.trans
      ((translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).value_decode member)

theorem substitutionMembers_decode (upperBase : PresentedType C') (upperFibres : ∀ c', PresentedType (D' c'))
    (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (member : {value : HSet.{u + 1} // value ∈
      (translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).carrier}) :
    ((substituteTranslation base family baseDerivation fibres derivation).derivation.interpret upperBase upperFibres).decode
      (substitutionMembers upperBase upperFibres base family baseDerivation fibres derivation member) =
      substitutionComparison base family baseDerivation fibres derivation
        ((translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).decode member) :=
  (_ : PresentedType _).decode.apply_symm_apply _

theorem termGraph_substitution (originalBase : PresentedType C) (originalFibres : ∀ c, PresentedType (D c))
    (upperBase : PresentedType C') (upperFibres : ∀ c', PresentedType (D' c'))
    (base : C' ≃ C) (family : ∀ c', D' c' ≃ D (base c'))
    (baseValues : ∀ c', upperBase.value c' = HSet.lift (originalBase.value (base c')))
    (fibreValues : ∀ c' d', (upperFibres c').value d' =
      HSet.lift ((originalFibres (base c')).value (family c' d')))
    (baseDerivation : CoreGeneration C D A) (fibres : (a : A) → CoreGeneration C D (B a))
    {T : Type u} (derivation : CoreGeneration A B T)
    (term : (translate base family (CoreGeneration.substitute baseDerivation fibres derivation)).Target) :
    (translatedModel upperBase upperFibres base family (CoreGeneration.substitute baseDerivation fibres derivation)).termGraph term ≈
      ((substituteTranslation base family baseDerivation fibres derivation).derivation.interpret upperBase upperFibres).termGraph
        (substitutionComparison base family baseDerivation fibres derivation term) := by
  apply HSet.mk_eq_mk_iff.mp
  rw [PresentedType.mk_termGraph, PresentedType.mk_termGraph]
  exact value_substitution originalBase originalFibres upperBase upperFibres base family baseValues fibreValues
    baseDerivation fibres derivation term

end CodeSubstitution

/-- Recovering a member is bounded by its original set. No representative
of its graph quotient, or unique witness from an arbitrary Type, is selected. -/
def memberComparison (X : HSet.{u}) : Elements (HSet.lift X) ≃ Elements X where
  toFun member := ⟨HSet.lowerMemberValue X member.1, HSet.lowerMemberValue_mem member.2⟩
  invFun member := ⟨HSet.lift member.1, HSet.lift_mem_lift_iff.mpr member.2⟩
  left_inv member := El.ext HSet.propositional (HSet.lift_lowerMemberValue member.2)
  right_inv member := El.ext HSet.propositional (HSet.lowerMemberValue_lift member.2)

def liftedFamily (X : HSet.{u}) (family : Elements X → HSet.{u}) : Elements (HSet.lift X) → HSet.{u + 1} :=
  fun member => HSet.lift (family (memberComparison X member))

theorem memberComparison_value (X : HSet.{u}) (member : Elements (HSet.lift X)) :
    (liftedModel (HSet.lift X)).value member = HSet.lift ((liftedModel X).value (memberComparison X member)) :=
  congrArg HSet.lift (HSet.lift_lowerMemberValue member.2).symm

def familyTranslation (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T) :
    Translation (Elements (HSet.lift X)) (fun a => Elements (liftedFamily X family a)) T :=
  translate (memberComparison X) (fun a => memberComparison (family (memberComparison X a))) derivation

def familyModel (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T) :
    PresentedType (familyTranslation X family derivation).Target :=
  interpretFamily (HSet.lift X) (liftedFamily X family) (familyTranslation X family derivation).derivation

theorem family_value_lift (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T)
    (term : (familyTranslation X family derivation).Target) :
    (familyModel X family derivation).value term =
      HSet.lift ((interpretFamily X family derivation).value ((familyTranslation X family derivation).comparison term)) := by
  apply translated_value (liftedModel X) (fun a => liftedModel (family a))
    (liftedModel (HSet.lift X)) (fun a => liftedModel (liftedFamily X family a))
    (memberComparison X) (fun a => memberComparison (family (memberComparison X a)))
  · intro a
    exact congrArg HSet.lift (HSet.lift_lowerMemberValue a.2).symm
  · intro a b
    exact congrArg HSet.lift (HSet.lift_lowerMemberValue b.2).symm

theorem family_carrier_lift (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T) :
    (familyModel X family derivation).carrier = HSet.lift (typeValue X family derivation) :=
  carrier_eq_lift_of_values _ _ _ (family_value_lift X family derivation)

def familyMembers (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T) :
    {value : HSet.{u + 2} // value ∈ (familyModel X family derivation).carrier} ≃
      {value : HSet.{u + 1} // value ∈ typeValue X family derivation} :=
  memberEquiv _ _ (familyTranslation X family derivation).comparison

theorem familyMembers_value (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T)
    (member : {value : HSet.{u + 2} // value ∈ (familyModel X family derivation).carrier}) :
    HSet.lift (familyMembers X family derivation member).1 = member.1 :=
  memberEquiv_value _ _ _ (family_value_lift X family derivation) member

theorem familyMembers_decode (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T)
    (member : {value : HSet.{u + 2} // value ∈ (familyModel X family derivation).carrier}) :
    (interpretFamily X family derivation).decode (familyMembers X family derivation member) =
      (familyTranslation X family derivation).comparison ((familyModel X family derivation).decode member) :=
  decode_memberEquiv _ _ _ member

theorem family_termGraph_lift (X : HSet.{u}) (family : Elements X → HSet.{u})
    {T : Type (u + 1)} (derivation : CoreGeneration (Elements X) (fun a => Elements (family a)) T)
    (term : (familyTranslation X family derivation).Target) :
    (familyModel X family derivation).termGraph term ≈
      ((interpretFamily X family derivation).termGraph ((familyTranslation X family derivation).comparison term)).lift :=
  termGraph_bisimilar _ _ _ (family_value_lift X family derivation) term

/-- The destination is the existing code enclosure of the actual lifted
material family, not an additional supplied universe or a ULift-only family. -/
theorem codeEnclosure_lift_subset (X : HSet.{u}) (family : Elements X → HSet.{u}) :
    HSet.lift (codeEnclosure X family) ⊆ codeEnclosure (HSet.lift X) (liftedFamily X family) := by
  intro value member
  obtain ⟨old, oldMember, same⟩ := HSet.mem_lift_iff.mp member
  obtain ⟨code, oldValue⟩ := mem_codeEnclosure_iff.mp oldMember
  apply mem_codeEnclosure_iff.mpr
  refine ⟨⟨(familyTranslation X family code.2).Target, (familyTranslation X family code.2).derivation⟩, ?_⟩
  exact (congrArg HSet.lift (family_carrier_lift X family code.2)).trans
    ((congrArg HSet.lift oldValue).trans same)

theorem family_value_substitution (X : HSet.{u}) (family : Elements X → HSet.{u})
    {A : Type (u + 1)} {B : A → Type (u + 1)}
    (baseDerivation : CoreGeneration (Elements X) (fun a => Elements (family a)) A)
    (fibres : (a : A) → CoreGeneration (Elements X) (fun a => Elements (family a)) (B a))
    {T : Type (u + 1)} (derivation : CoreGeneration A B T)
    (term : (familyTranslation X family (CoreGeneration.substitute baseDerivation fibres derivation)).Target) :
    (familyModel X family (CoreGeneration.substitute baseDerivation fibres derivation)).value term =
      ((substituteTranslation (memberComparison X) (fun a => memberComparison (family (memberComparison X a)))
        baseDerivation fibres derivation).derivation.interpret (liftedModel (HSet.lift X))
          (fun a => liftedModel (liftedFamily X family a))).value
            (substitutionComparison (memberComparison X) (fun a => memberComparison (family (memberComparison X a)))
              baseDerivation fibres derivation term) :=
  value_substitution (liftedModel X) (fun a => liftedModel (family a))
    (liftedModel (HSet.lift X)) (fun a => liftedModel (liftedFamily X family a))
    (memberComparison X) (fun a => memberComparison (family (memberComparison X a)))
    (memberComparison_value X) (fun a => memberComparison_value (family (memberComparison X a)))
    baseDerivation fibres derivation term

namespace Controls

/-- Two material shapes, one well-founded and one cyclic. The family below
has no positions at the first and one actual position at the second. -/
def branchingBase : HSet.{u} := {∅, HSet.quineAtom}

def emptyShape : Elements branchingBase.{u} := ⟨∅, HSet.mem_pair.mpr (Or.inl rfl)⟩

def cyclicShape : Elements branchingBase.{u} := ⟨HSet.quineAtom, HSet.mem_pair.mpr (Or.inr rfl)⟩

def branchingFamily (shape : Elements branchingBase.{u}) : HSet.{u} :=
  HSet.sep (fun _ => shape.1 = HSet.quineAtom) {∅}

theorem branchingFamily_empty : branchingFamily emptyShape.{u} = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  exact HSet.empty_ne_quineAtom (HSet.mem_sep.mp member).2

def cyclicPosition : Elements (branchingFamily cyclicShape.{u}) :=
  ⟨∅, HSet.mem_sep.mpr ⟨HSet.mem_singleton_self _, rfl⟩⟩

theorem branchingFamily_nonconstant :
    branchingFamily emptyShape.{u} ≠ branchingFamily cyclicShape := by
  intro same
  have member : (∅ : HSet.{u}) ∈ branchingFamily cyclicShape := cyclicPosition.2
  rw [← same, branchingFamily_empty] at member
  exact HSet.notMem_empty _ member

abbrev BranchingTree := WTree (Elements branchingBase.{u}) (fun a => Elements (branchingFamily a))

def leaf : BranchingTree.{u} := .sup emptyShape fun position =>
  (HSet.notMem_empty position.1 (branchingFamily_empty ▸ position.2)).elim

def node : BranchingTree.{u} := .sup cyclicShape fun _ => leaf

def branchingDerivation : CoreGeneration (Elements branchingBase.{u}) (fun a => Elements (branchingFamily a)) BranchingTree :=
  .w .base .fibre

theorem branching_values_distinct :
    (interpretFamily branchingBase.{u} branchingFamily branchingDerivation).value leaf ≠
      (interpretFamily branchingBase branchingFamily branchingDerivation).value node := by
  intro same
  have treeSame := (interpretFamily branchingBase branchingFamily branchingDerivation).value_injective same
  exact HSet.empty_ne_quineAtom
    (congrArg (fun tree : BranchingTree => match tree with | .sup shape _ => shape.1) treeSame)

/-- This is an inhabited W with genuinely nonconstant material positions.
The addressed row survives translation to the actual lifted family. -/
theorem actual_lifted_w_position :
    HSet.lift (HSet.kpair
      (PresentedType.W.positionTag (liftedModel branchingBase.{u}) (fun a => liftedModel (branchingFamily a))
        cyclicShape cyclicPosition)
      (PresentedType.W.encode (liftedModel branchingBase) (fun a => liftedModel (branchingFamily a)) leaf)) ∈
      (familyModel branchingBase branchingFamily branchingDerivation).value
        ((familyTranslation branchingBase branchingFamily branchingDerivation).comparison.symm node) := by
  rw [family_value_lift, Equiv.apply_symm_apply]
  apply HSet.lift_mem_lift_iff.mpr
  change _ ∈ PresentedType.W.encode (liftedModel branchingBase) (fun a => liftedModel (branchingFamily a))
    (.sup cyclicShape (fun _ => leaf))
  exact (PresentedType.W.mem_encode_sup_iff _ _ _ _ _).mpr (Or.inr ⟨cyclicPosition, rfl⟩)

theorem actual_lifted_w_values_distinct :
    (familyModel branchingBase.{u} branchingFamily branchingDerivation).value
        ((familyTranslation branchingBase branchingFamily branchingDerivation).comparison.symm leaf) ≠
      (familyModel branchingBase branchingFamily branchingDerivation).value
        ((familyTranslation branchingBase branchingFamily branchingDerivation).comparison.symm node) := by
  intro same
  rw [family_value_lift, family_value_lift, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at same
  exact branching_values_distinct (HSet.lift_injective same)

theorem actual_lifted_nested_entry (X : HSet.{u}) (a : Elements X) :
    HSet.kpair (HSet.lift (HSet.lift a.1)) (HSet.kpair (HSet.lift (HSet.lift a.1)) ∅) ∈
      (familyModel X singletonFamily (pairedIdentitySections X singletonFamily)).value
        ((familyTranslation X singletonFamily (pairedIdentitySections X singletonFamily)).comparison.symm
          (singletonIdentitySection X)) := by
  rw [family_value_lift, Equiv.apply_symm_apply]
  have row := HSet.lift_mem_lift_iff.mpr (singletonIdentitySection_entry X a)
  simpa only [HSet.lift_kpair, HSet.lift_empty] using row

theorem actual_lifted_empty_fibre {X : HSet.{u}} {family : Elements X → HSet.{u}}
    (a : Elements X) (empty : family a = ∅) :
    (familyModel X family (pairedIdentitySections X family)).carrier = ∅ := by
  rw [family_carrier_lift, pairedIdentitySections_empty_of_empty_fibre a empty, HSet.lift_empty]

theorem actual_lifted_enclosure_russell_notMem (X : HSet.{u}) (family : Elements X → HSet.{u}) :
    HSet.russell (codeEnclosure (HSet.lift X) (liftedFamily X family)) ∉
      codeEnclosure (HSet.lift X) (liftedFamily X family) := HSet.russell_notMem _

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialReindexing
