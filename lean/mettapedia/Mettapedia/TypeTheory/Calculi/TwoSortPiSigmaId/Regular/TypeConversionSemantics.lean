import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.PresheafNormalization

/-!
# Formed type conversion in the regular source representation

Conversion of formed source types induces an isomorphism of their display
contexts and hence of their represented families. The comparison retains
the actual term and is compatible with substitution. This realizes the
existing regular conversion rule; it does not reflect conversion into raw
type equality or add propositional identity elimination.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf

open Syntax Substitution Regular
open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory

local instance (Γ : Context) : Category.{0} (TypeOver cwf Γ) :=
  TypeOver.instCategory (C := cwf) (Γ := Γ)

/-- Convert a term between two independently formed convertible types. -/
def convertTerm {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) (term : Tm Γ A) : Tm Γ B :=
  ⟨term.val, .conv_type term.property B.property conversion⟩

def conversionTermEquiv {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) : Tm Γ A ≃ Tm Γ B where
  toFun := convertTerm conversion
  invFun := convertTerm conversion.symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- Conversion changes the typing derivation, not the retained source term. -/
theorem convertTerm_substitution {Γ Δ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) (term : Tm Γ A) (σ : Hom Δ Γ) :
    termSub (convertTerm conversion term) σ =
      convertTerm (conversion.subst σ.val σ.property.constantFree) (termSub term σ) :=
  rfl

/-- Retyping by conversion does not change the normalizer's input or
computed output. Only the retained result typing changes. -/
theorem normalizeTerm_conversion {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) (term : Tm Γ A) :
    normalizeTerm (convertTerm conversion term) =
      convertTerm conversion (normalizeTerm term) := rfl

/-- The existing context-head conversion is the identity substitution on
syntax with the regular typing proof appropriate to its two telescopes. -/
def conversionDisplayMap {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) :
    (⟨A⟩ : TypeOver cwf Γ) ⟶ ⟨B⟩ :=
  ⟨⟨ids, RegularCtxMor.convertHead B.property conversion.symm⟩, Subtype.ext rfl⟩

def conversionDisplayIso {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) :
    (⟨A⟩ : TypeOver cwf Γ) ≅ ⟨B⟩ where
  hom := conversionDisplayMap conversion
  inv := conversionDisplayMap conversion.symm
  hom_inv_id := TypeOver.Hom.ext (Subtype.ext rfl)
  inv_hom_id := TypeOver.Hom.ext (Subtype.ext rfl)

/-- Reindexing a conversion display map is precisely conversion between the
substituted formed types. This uses uniqueness of the existing cartesian
lift rather than a second reindexing operation. -/
theorem conversionDisplayMap_substitution {Γ Δ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) (σ : Hom Δ Γ) :
    TypeOver.reindexArrow σ (conversionDisplayMap conversion) =
      conversionDisplayMap (conversion.subst σ.val σ.property.constantFree) := by
  apply TypeOver.extensionSubstitution_cancel (C := cwf) σ
    (source := ⟨typeSub A σ⟩) (B := ⟨B⟩)
  refine (TypeOver.extensionSubstitution_naturality (C := cwf) σ
    (conversionDisplayMap conversion)).trans ?_
  change compose (conversionDisplayMap conversion).substitution
      (TypeOver.extensionSubstitution (C := cwf) σ A) =
    compose (TypeOver.extensionSubstitution (C := cwf) σ B)
      (conversionDisplayMap (conversion.subst σ.val σ.property.constantFree)).substitution
  rw [comprehension_lift_eq, comprehension_lift_eq]
  apply Subtype.ext
  funext i
  change subst (liftSub σ.val) (ids i) = subst ids (liftSub σ.val i)
  exact (subst_ids (liftSub σ.val i)).symm

/-- The source conversion rule interpreted by the existing display-map
functor, with an inverse rather than a one-sided family implication. -/
def representedConversionIso {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) :
    representedFamily A ≅ representedFamily B :=
  (CwfYoneda.familyFunctor cwf Γ).mapIso (conversionDisplayIso conversion)

/-- At every environment, interpreted conversion retains the entire raw
constructor-tree substitution, not just its denotation. -/
theorem representedConversion_preserves_substitution {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val)
    (point : (CwfYoneda.contextFace cwf Γ).Elements)
    (receipt : (representedFamily A).obj point) :
    ((representedConversionIso conversion).hom.app point receipt).val.val =
      receipt.val.val := rfl

/-- Interpreting source type conversion agrees with converting the whole
natural term section. The source term itself is unchanged. -/
theorem representedConversion_term {Γ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) (term : Tm Γ A) :
    (Functor.sectionsFunctor _).map (representedConversionIso conversion).hom
        (representedTermEquiv A term) =
      representedTermEquiv B (convertTerm conversion term) := by
  apply (Functor.sections_ext_iff).2
  intro point
  apply Subtype.ext
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  rfl

theorem representedConversion_refl {Γ : Context} (A : Ty Γ) :
    (representedConversionIso
      (ConstantFreeConv.refl A.val
        (A.property.constantFree_both Γ.regular.constantFreeCtx).1)).hom =
      𝟙 (representedFamily A) := by
  change (CwfYoneda.familyFunctor cwf Γ).map _ = _
  have sourceIdentity : conversionDisplayMap
      (ConstantFreeConv.refl A.val
        (A.property.constantFree_both Γ.regular.constantFreeCtx).1) =
      𝟙 (⟨A⟩ : TypeOver cwf Γ) := TypeOver.Hom.ext (Subtype.ext rfl)
  exact (congrArg (CwfYoneda.familyFunctor cwf Γ).map sourceIdentity).trans
    ((CwfYoneda.familyFunctor cwf Γ).map_id (⟨A⟩ : TypeOver cwf Γ))

/-- Successive source conversions give the same displayed family map as
their composite conversion. -/
theorem representedConversion_trans {Γ : Context} {A B D : Ty Γ}
    (first : ConstantFreeConv A.val B.val) (second : ConstantFreeConv B.val D.val) :
    (representedConversionIso first).hom ≫ (representedConversionIso second).hom =
      (representedConversionIso (first.trans second)).hom := by
  change (CwfYoneda.familyFunctor cwf Γ).map (conversionDisplayMap first) ≫
      (CwfYoneda.familyFunctor cwf Γ).map (conversionDisplayMap second) = _
  rw [← Functor.map_comp]
  apply congrArg (CwfYoneda.familyFunctor cwf Γ).map
  exact TypeOver.Hom.ext (Subtype.ext rfl)

/-- The represented conversion square commutes with arbitrary regular
context substitutions, including the interpretation's nontrivial type
substitution comparisons. -/
theorem representedConversion_substitution {Γ Δ : Context} {A B : Ty Γ}
    (conversion : ConstantFreeConv A.val B.val) (σ : Hom Δ Γ) :
    (representedConversionIso
        (conversion.subst σ.val σ.property.constantFree)).hom ≫
        (CwfYoneda.substitutionIso cwf B σ).hom =
      (CwfYoneda.substitutionIso cwf A σ).hom ≫
        Functor.whiskerLeft (yoneda.map
          (show CwfYoneda.context cwf Δ ⟶ CwfYoneda.context cwf Γ from σ)).mapElements
          (representedConversionIso conversion).hom := by
  have natural := CwfYoneda.substitutionIso_naturality cwf σ
    (conversionDisplayMap conversion)
  rw [conversionDisplayMap_substitution] at natural
  exact natural

/-! ## A formed, genuinely dependent conversion -/

def betaIndexedType : Ty sampleContext :=
  identityType (smallSort sampleContext) sampleBeta sampleTerm

theorem betaIndexedType_converts :
    ConstantFreeConv betaIndexedType.val dependentIdentityFamily.val :=
  .rel ⟨.congIdLeft (.betaPi (.var (0 : Fin 2)) (.var (0 : Fin 1))),
    (betaIndexedType.property.constantFree_both sampleContext.regular.constantFreeCtx).1,
    (dependentIdentityFamily.property.constantFree_both
      sampleContext.regular.constantFreeCtx).1⟩

/-- Distinct formed type syntax has isomorphic represented families, and a
dependent witness transports without replacing its code. -/
theorem dependent_conversion_retains_witness :
    betaIndexedType ≠ dependentIdentityFamily ∧
      (convertTerm betaIndexedType_converts.symm dependentIdentityWitness).val =
        dependentIdentityWitness.val := by
  constructor
  · intro same
    have raw := congrArg Subtype.val same
    cases raw
  · rfl

#print axioms conversionDisplayIso
#print axioms convertTerm_substitution
#print axioms normalizeTerm_conversion
#print axioms conversionDisplayMap_substitution
#print axioms representedConversion_term
#print axioms representedConversion_refl
#print axioms representedConversion_trans
#print axioms representedConversion_substitution
#print axioms dependent_conversion_retains_witness

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf
