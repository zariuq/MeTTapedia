import Mettapedia.Logic.HOL.HenkinInstitution
import Mettapedia.Logic.HOL.Syntax.TypeSubstitutionComposition
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation
import Mettapedia.Logic.HOL.CanonicalTheory

/-!+# Type-derived HOL signature morphisms

A signature consists of a base-type alphabet and a typed constant family.
A type-derived morphism may interpret a base symbol by a compound simple type;
its constant map must have the resulting type. This extends constant-only
signature translation without changing the fixed-base Henkin institution or
asserting model reducts for arbitrary Henkin domains.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

open CategoryTheory

universe u

/-- HOL signatures with a variable alphabet of base types. -/
def TypeDerivedSignature := Σ Base : Type u, HenkinInstitution.Signature Base

namespace TypeDerivedSignature

/-- Interpret base symbols by types and constants by symbols at those types. -/
structure Hom (source target : TypeDerivedSignature.{u}) where
  base : source.1 → Ty target.1
  constants : ∀ {a}, source.2.Const a → target.2.Const (Ty.substitute base a)

namespace Hom

variable {first middle last final : TypeDerivedSignature.{u}}

@[ext] theorem ext_data {f g : Hom first middle} (types : f.base = g.base)
    (symbols : ∀ {a} (c : first.2.Const a), HEq (f.constants c) (g.constants c)) : f = g := by
  cases f with
  | mk fb fc =>
      cases g with
      | mk gb gc =>
          cases types
          congr
          funext a c
          exact eq_of_heq (symbols c)

def identity (source : TypeDerivedSignature.{u}) : Hom source source where
  base := Ty.base
  constants := fun {a} c => (Ty.substitute_id a).symm ▸ c

def comp (f : Hom first middle) (g : Hom middle last) : Hom first last where
  base := fun b => Ty.substitute g.base (f.base b)
  constants := composeTypeConstants f.base g.base f.constants g.constants

theorem identity_comp (f : Hom first middle) : comp (identity first) f = f := by
  apply ext_data
  · rfl
  · intro a c
    simp only [comp, identity, composeTypeConstants]
    refine (eqRec_heq _ _).trans ?_
    congr 1 <;> simp

theorem comp_identity (f : Hom first middle) : comp f (identity middle) = f := by
  apply ext_data
  · funext b
    exact Ty.substitute_id _
  · intro a c
    simp only [comp, identity, composeTypeConstants]
    exact (eqRec_heq _ _).trans (eqRec_heq _ _)

theorem comp_assoc (f : Hom first middle) (g : Hom middle last) (h : Hom last final) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext_data
  · funext b
    exact Ty.substitute_comp _ _ _
  · intro a c
    simp only [comp, composeTypeConstants]
    refine (eqRec_heq _ _).trans ?_
    refine HEq.trans ?_ (eqRec_heq _ _).symm
    refine HEq.trans ?_ (eqRec_heq _ _).symm
    congr 1 <;> simp [Ty.substitute_comp]

end Hom

instance category : Category TypeDerivedSignature.{u} where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp := Hom.identity_comp
  comp_id := Hom.comp_identity
  assoc := Hom.comp_assoc

/-- Type-derived signature interpretations act functorially on sentences. -/
def sentence : TypeDerivedSignature.{u} ⥤ Type u where
  obj S := ClosedFormula S.2.Const
  map f := TypeCat.ofHom (mapTypes f.base f.constants)
  map_id S := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext φ
    exact mapTypes_id_closed φ
  map_comp f g := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext φ
    exact (mapTypes_comp_closed f.base g.base f.constants g.constants φ).symm

/-- Actual extensional derivations transport along every signature arrow.
This states preservation, not reflection or completeness. -/
theorem theorem_map {S T : TypeDerivedSignature.{u}} (f : S ⟶ T)
    {φ : ClosedFormula S.2.Const} (proof : ExtDerivation.Theorem S.2.Const φ) :
    ExtDerivation.Theorem T.2.Const (sentence.map f φ) :=
  ExtDerivation.theorem_mapTypes f.base f.constants proof

/-- Finite derivability from an arbitrary theory transports to its translated
axioms. No semantic completeness hypothesis is used. -/
theorem provable_map {S T : TypeDerivedSignature.{u}} (f : S ⟶ T)
    {axioms : ClosedTheorySet S.2.Const} {φ : ClosedFormula S.2.Const}
    (proof : ClosedTheorySet.Provable axioms φ) :
    ClosedTheorySet.Provable (Set.image (sentence.map f) axioms) (sentence.map f φ) := by
  obtain ⟨premises, admitted, derivation⟩ := proof
  refine ⟨premises.map (sentence.map f), ?_, ExtDerivation.mapTypes f.base f.constants derivation⟩
  intro ψ membership
  obtain ⟨θ, member, rfl⟩ := List.mem_map.mp membership
  exact Set.mem_image_of_mem _ (admitted θ member)

/-- Include the existing constant-only signature category without changing
its objects' constants or inventing an arbitrary-Henkin model translation. -/
def fixedBase (Base : Type u) : HenkinInstitution.Signature Base ⥤ TypeDerivedSignature.{u} where
  obj S := ⟨Base, S⟩
  map f := ⟨Ty.base, fun {a} c => (Ty.substitute_id a).symm ▸ f.map c⟩
  map_id _ := rfl
  map_comp f g := by
    apply Hom.ext_data
    · rfl
    · intro a c
      simp only [CategoryStruct.comp, Hom.comp, composeTypeConstants]
      refine HEq.trans ?_ (eqRec_heq _ _).symm
      refine HEq.trans ?_ (eqRec_heq _ _).symm
      refine (eqRec_heq _ _).trans ?_
      change HEq (g.map (f.map c)) (g.map _)
      congr 1 <;> simp

theorem sentence_fixedBase {Base : Type u} {S T : HenkinInstitution.Signature Base}
    (f : S ⟶ T) (φ : ClosedFormula S.Const) :
    sentence.map ((fixedBase Base).map f) φ = HenkinInstitution.sentence.map f φ :=
  mapTypes_base_closed f.map φ

/-- Extending the signature category does not identify distinct constant maps. -/
instance fixedBase_faithful (Base : Type u) : (fixedBase Base).Faithful where
  map_injective := by
    intro S T f g equal
    apply HenkinInstitution.Signature.Hom.ext
    intro a c
    have pairEqual := congrArg
      (fun h : Hom ⟨Base, S⟩ ⟨Base, T⟩ =>
        (⟨Ty.substitute h.base a, h.constants c⟩ : Σ b, T.Const b)) equal
    have values := (Sigma.mk.inj_iff.mp pairEqual).2
    exact eq_of_heq ((eqRec_heq _ _).symm.trans (values.trans (eqRec_heq _ _)))

#print axioms Hom.comp_assoc
#print axioms sentence
#print axioms theorem_map
#print axioms provable_map
#print axioms fixedBase_faithful

end TypeDerivedSignature

end Mettapedia.Logic.HOL
