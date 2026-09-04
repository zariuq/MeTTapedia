import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mettapedia.CategoryTheory.PseudofunctorOneCellOpposite
import Mettapedia.TypeTheory.CategoryIndexedFamilyTwoCellAction
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalSemanticThinness

/-!
# A mode-indexed doctrine of covariant dependent families

A semantic mode pseudofunctor `S : B ⥤ᵖ Cat` determines a contravariant
pseudofunctor of covariant dependent families.  At a mode `m` its objects are
functors from `S(m)` to `Type`.  A modality `p : m ⟶ n` acts by
precomposition with `S(p)`, and a comparison between modalities acts by right
whiskering on every family.

The construction is the composite

`Bᵒᵖ ⥤ᵖ Catᵒᵖ ⥤ᵖ Cat`,

where the first map is the one-cell opposite of `S` and the second is the
bicategorical Yoneda pseudofunctor represented by `Type`.  Thus identity,
composition, and 2-cell coherence are inherited from standard bicategorical
structure rather than imposed separately.

The operational/intensional/extensional semantics is instantiated below.
Its factor comparison yields a natural isomorphism between the two induced
reindexing functors, while the two modality paths remain distinct.  This is
the required non-collapse boundary: coherent comparison is not equality of
routes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ModeIndexedFamilyDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open _root_.Opposite
open Mettapedia.CategoryTheory.Pseudofunctor
open CategoryIndexedFamilyTwoCellAction
open OperationalIntensionalExtensionalModes
open OperationalIntensionalExtensionalTwoComputad
open OperationalIntensionalExtensionalLocallyThinModeTheory
open OperationalIntensionalExtensionalSemanticThinness

universe w v uBase u

variable {B : Type uBase} [Bicategory.{w, v} B]

/-! ## The generic indexed doctrine -/

/-- Covariant dependent families over the semantic category at one mode.
`Cat.Hom` is Mathlib's non-definitional wrapper around an ordinary functor. -/
abbrev FamilyAt (semantics : B ⥤ᵖ Cat.{u, u + 1}) (mode : B) :=
  semantics.obj mode ⟶ Cat.of (Type u)

/-- A semantic mode pseudofunctor induces a contravariant pseudofunctor of
covariant dependent families. -/
def covariantFamilyDoctrine (semantics : B ⥤ᵖ Cat.{u, u + 1}) :
    Bᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1} :=
  Pseudofunctor.comp
    (oneCellOpposite semantics)
    (Bicategory.yoneda₀ (Cat.of (Type u)))

/-- A modality reindexes families by precomposition. -/
def reindexing (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} (path : source ⟶ target) :
    FamilyAt semantics target ⥤ FamilyAt semantics source :=
  ((covariantFamilyDoctrine semantics).map path.op).toFunctor

/-- Reindexing along an identity path is naturally isomorphic to identity. -/
def reindexingIdentityIso (semantics : B ⥤ᵖ Cat.{u, u + 1}) (mode : B) :
    reindexing semantics (𝟙 mode) ≅ 𝟭 (FamilyAt semantics mode) :=
  Cat.Hom.toNatIso
    ((covariantFamilyDoctrine semantics).mapId (Opposite.op mode))

/-- Reindexing reverses composition, coherently rather than definitionally. -/
def reindexingCompositionIso (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {first middle last : B} (earlier : first ⟶ middle)
    (later : middle ⟶ last) :
    reindexing semantics (earlier ≫ later) ≅
      reindexing semantics later ⋙ reindexing semantics earlier :=
  Cat.Hom.toNatIso
    ((covariantFamilyDoctrine semantics).mapComp later.op earlier.op)

@[simp] theorem covariantFamilyDoctrine_obj
    (semantics : B ⥤ᵖ Cat.{u, u + 1}) (mode : Bᵒᵖ) :
    (covariantFamilyDoctrine semantics).obj mode =
      Cat.of (FamilyAt semantics mode.unop) :=
  rfl

@[simp] theorem reindexing_obj
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} (path : source ⟶ target)
    (family : FamilyAt semantics target) :
    ((reindexing semantics path).obj family).toFunctor =
      (semantics.map path).toFunctor ⋙ family.toFunctor :=
  rfl

/-- The doctrine's action on a mode 2-cell is exactly right whiskering of the
semantic natural transformation by the selected family. -/
@[simp] theorem covariantFamilyDoctrine_map₂_app
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target) :
    (((covariantFamilyDoctrine semantics).map₂
      (Bicategory.Opposite.op2 cell)).toNatTrans.app family).toNatTrans =
        whiskeredFamilyAction
          (semantics.map₂ cell).toNatTrans family.toFunctor :=
  rfl

/-- Acting on every covariant family detects exactly equality of the semantic
2-cells.  It detects base 2-cell equality as well precisely when the semantic
pseudofunctor is locally faithful. -/
theorem mappedCell_eq_iff_all_family_actions_eq
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (left right : first ⟶ second) :
    semantics.map₂ left = semantics.map₂ right ↔
      ∀ family : FamilyAt semantics target,
        (((covariantFamilyDoctrine semantics).map₂
            (Bicategory.Opposite.op2 left)).toNatTrans.app family).toNatTrans =
          (((covariantFamilyDoctrine semantics).map₂
            (Bicategory.Opposite.op2 right)).toNatTrans.app family).toNatTrans := by
  constructor
  · intro equality family
    exact congrArg
      (fun cell => Functor.whiskerRight cell.toNatTrans family.toFunctor)
      equality
  · intro equalActions
    apply Cat.Hom₂.ext
    apply whiskeredDependentAction_injective
    funext family
    have actionEquality := equalActions family.toCatHom
    change Functor.whiskerRight (semantics.map₂ left).toNatTrans family =
      Functor.whiskerRight (semantics.map₂ right).toNatTrans family
        at actionEquality
    exact actionEquality

/-! ## The selected operational/intensional/extensional instance -/

/-- Families over one selected operational, intensional, or extensional
semantic category. -/
abbrev SelectedFamily (mode : ThinMode) :=
  FamilyAt thinSemanticPseudofunctor.{u} mode

/-- The checked O/I/E semantics lifted from modes to their categories of
covariant dependent families. -/
def operationalIntensionalExtensionalFamilyDoctrine :
    ThinModeᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1} :=
  covariantFamilyDoctrine thinSemanticPseudofunctor.{u}

/-- Reindex families along a selected O/I/E modality path. -/
abbrev selectedReindexing {source target : ThinMode}
    (path : source ⟶ target) :
    SelectedFamily.{u} target ⥤ SelectedFamily.{u} source :=
  reindexing thinSemanticPseudofunctor.{u} path

@[simp] theorem selectedReindexing_obj
    {source target : ThinMode} (path : source ⟶ target)
    (family : SelectedFamily.{u} target) :
    ((selectedReindexing path).obj family).toFunctor =
      (thinSemanticPseudofunctor.{u}.map path).toFunctor ⋙
        family.toFunctor :=
  rfl

/-- The factor cell induces an invertible comparison between reindexing by
evidence-then-readout and reindexing by direct observation. -/
def factorReindexingIso :
    selectedReindexing.{u} evidenceReadout ≅
      selectedReindexing.{u} observe :=
  Cat.Hom.toNatIso
    (operationalIntensionalExtensionalFamilyDoctrine.{u}.map₂Iso
      factorIso.op2)

/-- The factor comparison acts on a family by the same right-whiskering
operation as the underlying semantic natural transformation. -/
@[simp] theorem factorReindexingIso_hom_app
    (family : SelectedFamily.{u} extensional) :
    (factorReindexingIso.{u}.hom.app family).toNatTrans =
      whiskeredFamilyAction
        (thinSemanticPseudofunctor.{u}.map₂ factorForward).toNatTrans
        family.toFunctor :=
  rfl

/-- The factor comparison does not identify the two authored modality paths.
They remain distinct one-cells connected by an isomorphism. -/
theorem factor_paths_distinct : evidenceReadout ≠ observe := by
  intro equality
  have countEquality := congrArg
    (fun path : operational ⟶ extensional => generatorCount path.as) equality
  change 1 + 1 = 1 at countEquality
  omega

/-- Positive and negative canaries for the selected family doctrine: the two
factor routes have coherently isomorphic family actions, but are not equal as
mode paths. -/
theorem factor_family_doctrine_noncollapse :
    Nonempty
        (selectedReindexing.{u} evidenceReadout ≅
          selectedReindexing.{u} observe) ∧
      evidenceReadout ≠ observe :=
  ⟨⟨factorReindexingIso.{u}⟩, factor_paths_distinct⟩

/-! ## Axiom audit -/

#print axioms covariantFamilyDoctrine
#print axioms mappedCell_eq_iff_all_family_actions_eq
#print axioms operationalIntensionalExtensionalFamilyDoctrine
#print axioms factorReindexingIso
#print axioms factor_paths_distinct
#print axioms factor_family_doctrine_noncollapse

end Mettapedia.TypeTheory.ModeIndexedFamilyDoctrine
