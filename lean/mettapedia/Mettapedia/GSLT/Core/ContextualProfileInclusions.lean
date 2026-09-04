import Mettapedia.GSLT.Core.ContextualPseudoCwfBasePseudofunctor

/-!
# Canonical inclusions between the families profiles

The common contextual waist becomes useful only when the actions on type and
term fibres are also explicit.  This module starts that comparison for the
canonical set-family models.

The simply typed model embeds in the dependent model by sending a simple type
`A` to the constant family `fun _ => A`.  At every context this gives a fully
faithful functor between the corresponding categories of types.  It is not
essentially surjective: the dependent model contains genuinely varying
families.

The comprehension contexts of the two models are a product and a dependent
sum.  They are canonically isomorphic, but not definitionally the same
construction.  This is the concrete reason the eventual profile inclusion is
a pseudo CwF morphism rather than a strict one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe w

/-- The dependent-interface presentation of the canonical simply typed
families model. -/
abbrev SimpleFamiliesCwf : Cwf.{w + 1, w, w + 1, w} :=
  simpleFamilies.toCwf

/-- The simply typed families model with its selected terminal context,
presented through the dependent CwF interface. -/
abbrev SimpleFamiliesCwfWithTerminal :
    CwfWithTerminal.{w + 1, w, w + 1, w} :=
  simpleFamiliesWithTerminal.toCwfWithTerminal

/-- The unityped families model over `V`, transported through the structural
ladder to the dependent CwF interface. -/
abbrev UnitypedFamiliesCwfWithTerminal (V : Type w) :
    CwfWithTerminal.{w + 1, w, w + 1, w} :=
  (unitypedFamiliesWithTerminal V).toScwfWithTerminal.toCwfWithTerminal

/-- Constant-family inclusion leaves contexts and substitutions unchanged. -/
def simpleToDependentBaseFunctor :
    SimpleFamiliesCwf.base.Context ⥤ familiesCwf.base.Context where
  obj context := ⟨context.val⟩
  map substitution := substitution

/-! ## Unityped values as one selected simple type -/

/-- The family-presheaf map selecting `V` as the unique simple type carried
by the unityped profile. -/
def unitypedToSimpleFamilyMorphism (V : Type w) :
    CwfFamilyMorphism
      (UnitypedFamiliesCwfWithTerminal V).toCwf
      SimpleFamiliesCwfWithTerminal.toCwf where
  base :=
    { obj := fun context => ⟨context.val⟩
      map := fun substitution => substitution }
  family :=
    { app := fun _ =>
        { onIndex := fun _ => V
          onFibre := fun _ term => term }
      naturality := by
        intro source target substitution
        apply IndexedFamily.Hom.ext
        · funext A
          cases A
          rfl
        · intro A term
          cases A
          rfl }

/-- Unityped inclusion is strict: after selecting `V`, both sides use the
same product comprehension `Γ × V`. -/
def unitypedToSimpleStrictMorphism (V : Type w) :
    StrictCwfMorphism
      (UnitypedFamiliesCwfWithTerminal V)
      SimpleFamiliesCwfWithTerminal where
  toFamilyMorphism := unitypedToSimpleFamilyMorphism V
  empty_preserved := rfl
  extension_preserved := by
    intro Γ A
    cases A
    rfl
  projection_preserved := by
    intro Γ A
    cases A
    change (fun point : Γ × V => point.1) =
      (fun point : Γ × V => point.1)
    rfl
  variable_preserved := by
    intro Γ A
    cases A
    rfl

/-- The strict lower inclusion, viewed in the common pseudo-CwF
bicategory. -/
def unitypedToSimplePseudoMorphism (V : Type w) :
    PseudoCwfMorphism
      (UnitypedFamiliesCwfWithTerminal V)
      SimpleFamiliesCwfWithTerminal :=
  (unitypedToSimpleStrictMorphism V).toPseudo

/-- The unique unityped type is sent to the selected simple type `V`. -/
@[simp]
theorem unitypedToSimplePseudoMorphism_mapType
    (V : Type w) {Γ : Type w} (A : PUnit) :
    (unitypedToSimplePseudoMorphism V).mapType (Γ := Γ) A = V := by
  cases A
  rfl

/-- Negative control: at `V = Bool`, the empty simple type is not in the
object image of the unityped inclusion. -/
theorem pempty_not_in_unitypedBool_type_image :
    ¬ ∃ A : TypeOver
        (UnitypedFamiliesCwfWithTerminal Bool).toCwf PUnit,
      (unitypedToSimplePseudoMorphism Bool).mapTypeObject A =
        (⟨PEmpty⟩ : TypeOver SimpleFamiliesCwf PUnit) := by
  rintro ⟨A, imageEquality⟩
  rcases A with ⟨A⟩
  cases A
  have valueEquality := congrArg TypeOver.val imageEquality
  change Bool = PEmpty at valueEquality
  have boolEmpty : Bool = PEmpty := valueEquality
  exact nomatch cast boolEmpty true

/-- A simple type over `Γ`, regarded as a constant dependent family. -/
def simpleToDependentObject {Γ : Type w}
    (A : TypeOver (SimpleFamiliesCwf.{w}) Γ) :
    TypeOver (familiesCwf.{w}) Γ :=
  ⟨constantFamily A.val⟩

/-! ## Comprehension comparison -/

/-- Product comprehension in the simple model and dependent-sum
comprehension in the dependent model are canonically isomorphic. -/
def productSigmaComprehensionIso (Γ A : Type w) :
    (⟨Γ × A⟩ : SimpleFamiliesCwf.base.Context) ≅
      (⟨Σ _ : Γ, A⟩ : familiesCwf.base.Context) where
  hom point := ⟨point.1, point.2⟩
  inv point := (point.1, point.2)
  hom_inv_id := by
    funext point
    rcases point with ⟨context, value⟩
    rfl
  inv_hom_id := by
    funext point
    rcases point with ⟨context, value⟩
    rfl

/-- Translate a display map between simple types into the corresponding
display map between constant dependent families. -/
def simpleToDependentArrow {Γ : Type w}
    {A B : TypeOver (SimpleFamiliesCwf.{w}) Γ} (arrow : A ⟶ B) :
    simpleToDependentObject A ⟶ simpleToDependentObject B :=
  { substitution := fun point =>
      let output := arrow.substitution (point.1, point.2)
      ⟨output.1, output.2⟩
    over := by
      funext point
      exact congrFun arrow.over (point.1, point.2) }

/-- At a fixed context, constant-family inclusion is functorial. -/
def simpleToDependentTypeFunctor (Γ : Type w) :
    TypeOver (SimpleFamiliesCwf.{w}) Γ ⥤
      TypeOver (familiesCwf.{w}) Γ where
  obj := simpleToDependentObject
  map := simpleToDependentArrow
  map_id A := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨context, value⟩
    rfl
  map_comp first second := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨context, value⟩
    rfl

/-- Read a display map between constant dependent families back as the
corresponding simply typed display map. -/
def dependentToSimpleArrow {Γ : Type w}
    {A B : TypeOver (SimpleFamiliesCwf.{w}) Γ}
    (arrow : simpleToDependentObject A ⟶ simpleToDependentObject B) :
    A ⟶ B :=
  { substitution := fun point =>
      let output := arrow.substitution ⟨point.1, point.2⟩
      (output.1, output.2)
    over := by
      funext point
      exact congrFun arrow.over ⟨point.1, point.2⟩ }

/-- Constant-family inclusion is fully faithful at every context.  It loses
no display maps between types already in the simple image. -/
def simpleToDependentTypeFunctorFullyFaithful (Γ : Type w) :
    (simpleToDependentTypeFunctor Γ).FullyFaithful where
  preimage := dependentToSimpleArrow
  map_preimage arrow := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨context, value⟩
    generalize outputEquality :
      arrow.substitution ⟨context, value⟩ = output
    rcases output with ⟨target, result⟩
    simpa [simpleToDependentTypeFunctor, simpleToDependentArrow,
      dependentToSimpleArrow] using outputEquality
  preimage_map arrow := by
    apply TypeOver.Hom.ext
    funext point
    rcases point with ⟨context, value⟩
    generalize outputEquality :
      arrow.substitution (context, value) = output
    rcases output with ⟨target, result⟩
    simpa [simpleToDependentTypeFunctor, simpleToDependentArrow,
      dependentToSimpleArrow] using outputEquality

/-- Positive image control: every selected simple type maps to its constant
dependent family. -/
@[simp]
theorem simpleToDependentTypeFunctor_obj_val (Γ A : Type w) :
    ((simpleToDependentTypeFunctor Γ).obj
      (⟨A⟩ : TypeOver (SimpleFamiliesCwf.{w}) Γ)).val =
        constantFamily A :=
  rfl

/-- The canonical varying Boolean family is not in the object image of the
simple-to-dependent fibre functor. -/
theorem varyingBoolFamily_not_in_simpleType_image :
    ¬ ∃ A : TypeOver (SimpleFamiliesCwf.{0}) Bool,
      (simpleToDependentTypeFunctor Bool).obj A =
        (⟨varyingBoolFamily⟩ : TypeOver (familiesCwf.{0}) Bool) := by
  rintro ⟨A, imageEquality⟩
  have valueEquality := congrArg TypeOver.val imageEquality
  exact varyingBoolFamily_not_constant
    ⟨A.val, valueEquality.symm⟩

/-! ## Compatibility with substitution -/

/-- Reindexing a simple display map and then including it agrees with first
including the display map and then reindexing the resulting constant
families. -/
theorem simpleToDependentArrow_reindex
    {Γ Δ : Type w} (substitution : Γ → Δ)
    {A B : TypeOver (SimpleFamiliesCwf.{w}) Δ} (arrow : A ⟶ B) :
    simpleToDependentArrow
        (TypeOver.reindexArrow (C := SimpleFamiliesCwf)
          substitution arrow) =
      TypeOver.reindexArrow (C := familiesCwf) substitution
        (simpleToDependentArrow arrow) := by
  apply TypeOver.Hom.ext
  funext point
  rcases point with ⟨context, value⟩
  rfl

/-- The pointwise inclusions commute with context substitution. -/
def simpleToDependentSubstitutionIso
    {Γ Δ : Type w} (substitution : Γ → Δ) :
    TypeOver.reindexFunctor (C := SimpleFamiliesCwf) substitution ⋙
        simpleToDependentTypeFunctor Γ ≅
      simpleToDependentTypeFunctor Δ ⋙
        TypeOver.reindexFunctor (C := familiesCwf) substitution :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun arrow => simpleToDependentArrow_reindex substitution arrow)

/-- The fibrewise fully faithful inclusions and their substitution
comparisons assemble into a strong transformation of indexed type
categories. -/
def simpleToDependentFamilyTransformation :
    Pseudofunctor.StrongTrans
      (TypeOver.reindexingPseudofunctor SimpleFamiliesCwf)
      (SimpleFamiliesCwf.pullbackTypePseudofunctor
        simpleToDependentBaseFunctor) where
  app context :=
    (simpleToDependentTypeFunctor context.as.unop.val).toCatHom
  naturality arrow :=
    Cat.Hom.isoMk (simpleToDependentSubstitutionIso arrow.as.unop)
  naturality_naturality {a b f g} eta := by
    have underlyingEqual : f.as = g.as := Discrete.eq_of_hom
      (X := f) (Y := g) eta
    have arrowEqual : f = g := Discrete.ext underlyingEqual
    subst g
    have etaEqual : eta = 𝟙 f := Subsingleton.elim _ _
    subst eta
    simp only [PrelaxFunctor.map₂_id, Bicategory.id_whiskerRight,
      Bicategory.whiskerLeft_id, Category.id_comp, Category.comp_id]

/-! ## The pseudo-CwF profile inclusion -/

/-- The canonical simply typed families profile embeds into the dependent
families profile as a pseudo CwF morphism.  Its base action is the identity,
its fibre action is constant-family inclusion, and its comprehension
comparison is the product-to-dependent-sum isomorphism. -/
def simpleToDependentPseudoMorphism :
    PseudoCwfMorphism
      (SimpleFamiliesCwfWithTerminal.{w})
      (familiesCwfWithTerminal.{w}) where
  base := simpleToDependentBaseFunctor
  family := simpleToDependentFamilyTransformation
  emptyIso := Iso.refl _
  comprehensionIso Γ A := productSigmaComprehensionIso Γ A
  projection_preserved := by
    intro Γ A
    rfl
  display_preserved := by
    intro Γ A B arrow
    rfl
  extension_preserved := by
    intro Γ Δ substitution A
    funext point
    rcases point with ⟨context, value⟩
    rfl

/-- The profile inclusion sends every simple type to the corresponding
constant family. -/
@[simp]
theorem simpleToDependentPseudoMorphism_mapType
    {Γ : Type w} (A : Type w) :
    simpleToDependentPseudoMorphism.mapType
        (Γ := Γ) A = constantFamily A :=
  rfl

/-- Its action on every type fibre is fully faithful. -/
def simpleToDependentPseudoMorphism_fibreFullyFaithful (Γ : Type w) :
    (simpleToDependentPseudoMorphism.mapTypeFunctor Γ).FullyFaithful :=
  simpleToDependentTypeFunctorFullyFaithful Γ

/-- Negative control: the pseudo-CwF inclusion remains a proper fragment;
the varying Boolean family is not in its object image. -/
theorem varyingBoolFamily_not_in_pseudoMorphism_image :
    ¬ ∃ A : TypeOver (SimpleFamiliesCwf.{0}) Bool,
      simpleToDependentPseudoMorphism.mapTypeObject A =
        (⟨varyingBoolFamily⟩ : TypeOver (familiesCwf.{0}) Bool) :=
  varyingBoolFamily_not_in_simpleType_image

/-- The operational unityped profile reaches dependent families by first
selecting its value carrier as one simple type and then taking the constant
dependent family. -/
def unitypedToDependentPseudoMorphism (V : Type w) :
    PseudoCwfMorphism
      (UnitypedFamiliesCwfWithTerminal V)
      (familiesCwfWithTerminal.{w}) :=
  (unitypedToSimplePseudoMorphism V).comp
    simpleToDependentPseudoMorphism

/-- Along the composite comparison, the implicit unityped sort becomes the
constant dependent family with fibre `V`. -/
@[simp]
theorem unitypedToDependentPseudoMorphism_mapType
    (V : Type w) {Γ : Type w} (A : PUnit) :
    (unitypedToDependentPseudoMorphism V).mapType (Γ := Γ) A =
      constantFamily V := by
  cases A
  rfl

/-- The comparison is over the unchanged base context. -/
theorem productSigmaComprehensionIso_projection (Γ A : Type w) :
    (productSigmaComprehensionIso Γ A).hom ≫
        (show (⟨Σ _ : Γ, A⟩ : familiesCwf.base.Context) ⟶ ⟨Γ⟩ from
          familiesCwf.wk (constantFamily A)) =
      (show (⟨Γ × A⟩ : SimpleFamiliesCwf.base.Context) ⟶ ⟨Γ⟩ from
        SimpleFamiliesCwf.wk A) :=
  rfl

#print axioms simpleToDependentTypeFunctor
#print axioms unitypedToSimpleStrictMorphism
#print axioms unitypedToSimplePseudoMorphism
#print axioms pempty_not_in_unitypedBool_type_image
#print axioms simpleToDependentTypeFunctorFullyFaithful
#print axioms varyingBoolFamily_not_in_simpleType_image
#print axioms simpleToDependentArrow_reindex
#print axioms simpleToDependentSubstitutionIso
#print axioms simpleToDependentFamilyTransformation
#print axioms simpleToDependentPseudoMorphism
#print axioms simpleToDependentPseudoMorphism_fibreFullyFaithful
#print axioms varyingBoolFamily_not_in_pseudoMorphism_image
#print axioms unitypedToDependentPseudoMorphism
#print axioms unitypedToDependentPseudoMorphism_mapType
#print axioms productSigmaComprehensionIso
#print axioms productSigmaComprehensionIso_projection

end Mettapedia.GSLT.Core.ContextualLadder
