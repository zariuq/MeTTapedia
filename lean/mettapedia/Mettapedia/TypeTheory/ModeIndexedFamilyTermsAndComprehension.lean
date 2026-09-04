import Mathlib.CategoryTheory.Limits.Final.Type
import Mettapedia.TypeTheory.ModeIndexedFamilyDoctrine

/-!
# Terms and comprehension for mode-indexed dependent families

The mode-indexed family doctrine sends a mode to its category of covariant
`Type`-valued families and sends a modality to reindexing by precomposition.
This module lifts that action to natural sections and to Grothendieck
comprehension.

For an ordinary functor `F : C ⥤ D`, a section of `A : D ⥤ Type` restricts
to a section of `F ⋙ A`.  A natural transformation `α : F ⟶ G` transports
the restricted section along the induced family map, and section naturality
proves that this transported term is exactly restriction along `G`.

The same family map induces a functor between categories of elements.  It
commutes strictly with the comprehension projection and transports the last
variable coherently.  These constructions are universe-polymorphic, so they
apply directly to semantic mode pseudofunctors whose categories have distinct
object and morphism universes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.TypeTheory.CategoryIndexedFamilyTwoCellAction
open Mettapedia.TypeTheory.ModeIndexedFamilyDoctrine
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocallyThinModeTheory
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalSemanticThinness

universe w v uBase u
universe uSource vSource uTarget vTarget uFamily

/-! ## Universe-polymorphic action on natural sections -/

/-- Map a natural section along a morphism of covariant families. -/
def mapSection
    {Context : Type uTarget} [Category.{vTarget} Context]
    {left right : Context ⥤ Type uFamily}
    (cell : left ⟶ right) (term : left.sections) : right.sections :=
  ((Functor.sectionsFunctor Context).map cell) term

@[simp] theorem mapSection_value
    {Context : Type uTarget} [Category.{vTarget} Context]
    {left right : Context ⥤ Type uFamily}
    (cell : left ⟶ right) (term : left.sections) (point : Context) :
    (mapSection cell term).1 point = cell.app point (term.1 point) :=
  rfl

@[simp] theorem mapSection_identity
    {Context : Type uTarget} [Category.{vTarget} Context]
    {family : Context ⥤ Type uFamily} (term : family.sections) :
    mapSection (𝟙 family) term = term := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

@[simp] theorem mapSection_vertical
    {Context : Type uTarget} [Category.{vTarget} Context]
    {first middle last : Context ⥤ Type uFamily}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (term : first.sections) :
    mapSection (earlier ≫ later) term =
      mapSection later (mapSection earlier term) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- Restrict a natural section along an ordinary functor. -/
def restrictSection
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    (substitution : Source ⥤ Target) {family : Target ⥤ Type uFamily}
    (term : family.sections) : (substitution ⋙ family).sections :=
  substitution.sectionsPrecomp term

@[simp] theorem restrictSection_value
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    (substitution : Source ⥤ Target) {family : Target ⥤ Type uFamily}
    (term : family.sections) (point : Source) :
    (restrictSection substitution term).1 point =
      term.1 (substitution.obj point) :=
  rfl

@[simp] theorem restrictSection_identity
    {Context : Type uTarget} [Category.{vTarget} Context]
    {family : Context ⥤ Type uFamily} (term : family.sections) :
    restrictSection (𝟭 Context) term = term := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

@[simp] theorem restrictSection_composition
    {First : Type uSource} [Category.{vSource} First]
    {Middle : Type uTarget} [Category.{vTarget} Middle]
    {Last : Type uBase} [Category.{v} Last]
    (earlier : First ⥤ Middle) (later : Middle ⥤ Last)
    {family : Last ⥤ Type uFamily} (term : family.sections) :
    restrictSection (earlier ⋙ later) term =
      restrictSection earlier (restrictSection later term) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- A context 2-cell acts coherently on every restricted term. -/
theorem restrictSection_action
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Source ⥤ Target} (cell : left ⟶ right)
    {family : Target ⥤ Type uFamily} (term : family.sections) :
    mapSection (whiskeredFamilyAction cell family)
        (restrictSection left term) =
      restrictSection right term := by
  apply (Functor.sections_ext_iff).2
  intro point
  change family.map (cell.app point) (term.1 (left.obj point)) =
    term.1 (right.obj point)
  exact term.2 (cell.app point)

/-! ## Universe-polymorphic Grothendieck comprehension -/

/-- A morphism of covariant families induces a functor between their
categories of elements. -/
def elementsAction
    {Context : Type uTarget} [Category.{vTarget} Context]
    {left right : Context ⥤ Type uFamily} (cell : left ⟶ right) :
    left.Elements ⥤ right.Elements :=
  ((Functor.elementsFunctor).map cell).toFunctor

@[simp] theorem elementsAction_projection
    {Context : Type uTarget} [Category.{vTarget} Context]
    {left right : Context ⥤ Type uFamily} (cell : left ⟶ right) :
    elementsAction cell ⋙ CategoryOfElements.π right =
      CategoryOfElements.π left :=
  rfl

@[simp] theorem elementsAction_identity
    {Context : Type uTarget} [Category.{vTarget} Context]
    (family : Context ⥤ Type uFamily) :
    elementsAction (𝟙 family) = 𝟭 family.Elements := by
  have mappedIdentity := (Functor.elementsFunctor).map_id family
  exact congrArg Cat.Hom.toFunctor mappedIdentity

@[simp] theorem elementsAction_vertical
    {Context : Type uTarget} [Category.{vTarget} Context]
    {first middle last : Context ⥤ Type uFamily}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    elementsAction (earlier ≫ later) =
      elementsAction earlier ⋙ elementsAction later := by
  have mappedComposition :=
    (Functor.elementsFunctor).map_comp earlier later
  exact congrArg Cat.Hom.toFunctor mappedComposition

/-- A context 2-cell induces the corresponding functor between the
comprehensions of a reindexed family. -/
def comprehensionAction
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Source ⥤ Target} (cell : left ⟶ right)
    (family : Target ⥤ Type uFamily) :
    (left ⋙ family).Elements ⥤ (right ⋙ family).Elements :=
  elementsAction (whiskeredFamilyAction cell family)

@[simp] theorem comprehensionAction_projection
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Source ⥤ Target} (cell : left ⟶ right)
    (family : Target ⥤ Type uFamily) :
    comprehensionAction cell family ⋙
        CategoryOfElements.π (right ⋙ family) =
      CategoryOfElements.π (left ⋙ family) :=
  rfl

@[simp] theorem comprehensionAction_identity
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    (substitution : Source ⥤ Target)
    (family : Target ⥤ Type uFamily) :
    comprehensionAction (𝟙 substitution) family =
      𝟭 (substitution ⋙ family).Elements := by
  rw [comprehensionAction, whiskeredFamilyAction_identity]
  exact elementsAction_identity (substitution ⋙ family)

@[simp] theorem comprehensionAction_vertical
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {first middle last : Source ⥤ Target}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (family : Target ⥤ Type uFamily) :
    comprehensionAction (earlier ≫ later) family =
      comprehensionAction earlier family ⋙
        comprehensionAction later family := by
  rw [comprehensionAction, whiskeredFamilyAction_vertical]
  exact elementsAction_vertical
    (whiskeredFamilyAction earlier family)
    (whiskeredFamilyAction later family)

/-- The last variable is the canonical section over a category of elements. -/
def lastVariable
    {Context : Type uTarget} [Category.{vTarget} Context]
    (family : Context ⥤ Type uFamily) :
    (CategoryOfElements.π family ⋙ family).sections :=
  ⟨fun point => point.2, fun route => route.property⟩

/-- Pull the family action back to the source comprehension. -/
def variableFamilyAction
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Source ⥤ Target} (cell : left ⟶ right)
    (family : Target ⥤ Type uFamily) :
    CategoryOfElements.π (left ⋙ family) ⋙ (left ⋙ family) ⟶
      CategoryOfElements.π (left ⋙ family) ⋙ (right ⋙ family) :=
  Functor.whiskerLeft (CategoryOfElements.π (left ⋙ family))
    (whiskeredFamilyAction cell family)

/-- The induced comprehension functor transports the last variable exactly
by the family action. -/
theorem comprehensionAction_lastVariable
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Source ⥤ Target} (cell : left ⟶ right)
    (family : Target ⥤ Type uFamily) :
    mapSection (variableFamilyAction cell family)
        (lastVariable (left ⋙ family)) =
      restrictSection (comprehensionAction cell family)
        (lastVariable (right ⋙ family)) := by
  apply (Functor.sections_ext_iff).2
  rintro ⟨point, value⟩
  change family.map (cell.app point) value =
    family.map (cell.app point) value
  rfl

/-! ## Action of a semantic mode 2-cell -/

variable {B : Type uBase} [Bicategory.{w, v} B]

/-- Natural sections of one family at one semantic mode. -/
abbrev TermAt (semantics : B ⥤ᵖ Cat.{u, u + 1}) {mode : B}
    (family : FamilyAt semantics mode) :=
  family.toFunctor.sections

/-- Reindex a term along a semantic modality. -/
def reindexTerm (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} (path : source ⟶ target)
    {family : FamilyAt semantics target} (term : TermAt semantics family) :
    TermAt semantics ((reindexing semantics path).obj family) :=
  restrictSection (semantics.map path).toFunctor term

/-- The semantic identity comparison transports restriction along an
identity modality back to the original term. -/
theorem reindexTerm_identity_coherence
    (semantics : B ⥤ᵖ Cat.{u, u + 1}) (mode : B)
    (family : FamilyAt semantics mode) (term : TermAt semantics family) :
    mapSection
        (whiskeredFamilyAction
          (semantics.mapId mode).hom.toNatTrans family.toFunctor)
        (reindexTerm semantics (𝟙 mode) term) =
      term := by
  have action := restrictSection_action
    (semantics.mapId mode).hom.toNatTrans term
  simpa [reindexTerm] using action

/-- The semantic composition comparison identifies one-step restriction
along a composite modality with successive restriction along its factors. -/
theorem reindexTerm_composition_coherence
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {first middle last : B} (earlier : first ⟶ middle)
    (later : middle ⟶ last) (family : FamilyAt semantics last)
    (term : TermAt semantics family) :
    mapSection
        (whiskeredFamilyAction
          (semantics.mapComp earlier later).hom.toNatTrans family.toFunctor)
        (reindexTerm semantics (earlier ≫ later) term) =
      reindexTerm semantics earlier
        (reindexTerm semantics later term) := by
  apply (Functor.sections_ext_iff).2
  intro point
  change
    TypeCat.Hom.hom
        (family.toFunctor.map
          ((semantics.mapComp earlier later).hom.toNatTrans.app point))
        (term.1 ((semantics.map (earlier ≫ later)).toFunctor.obj point)) =
      term.1
        ((semantics.map later).toFunctor.obj
          ((semantics.map earlier).toFunctor.obj point))
  exact term.2 ((semantics.mapComp earlier later).hom.toNatTrans.app point)

/-- The family morphism induced by one semantic mode 2-cell. -/
def modeCellFamilyAction (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target) :
    ((reindexing semantics first).obj family).toFunctor ⟶
      ((reindexing semantics second).obj family).toFunctor :=
  (((covariantFamilyDoctrine semantics).map₂
    (Bicategory.Opposite.op2 cell)).toNatTrans.app family).toNatTrans

@[simp] theorem modeCellFamilyAction_eq_whiskered
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target) :
    modeCellFamilyAction semantics cell family =
      whiskeredFamilyAction
        (semantics.map₂ cell).toNatTrans family.toFunctor :=
  rfl

/-- Transport a reindexed term along a semantic mode 2-cell. -/
def modeCellTermAction (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target) :
    TermAt semantics ((reindexing semantics first).obj family) →
      TermAt semantics ((reindexing semantics second).obj family) :=
  mapSection (modeCellFamilyAction semantics cell family)

/-- Reindexing a term along either side of a mode 2-cell agrees after the
induced term transport. -/
theorem modeCellTermAction_reindex
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target)
    (term : TermAt semantics family) :
    modeCellTermAction semantics cell family
        (reindexTerm semantics first term) =
      reindexTerm semantics second term := by
  exact restrictSection_action
    (semantics.map₂ cell).toNatTrans term

/-- A semantic mode 2-cell induces a functor between the corresponding
reindexed comprehensions. -/
def modeCellComprehensionAction
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target) :
    ((reindexing semantics first).obj family).toFunctor.Elements ⥤
      ((reindexing semantics second).obj family).toFunctor.Elements :=
  elementsAction (modeCellFamilyAction semantics cell family)

@[simp] theorem modeCellComprehensionAction_projection
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target) :
    modeCellComprehensionAction semantics cell family ⋙
        CategoryOfElements.π
          ((reindexing semantics second).obj family).toFunctor =
      CategoryOfElements.π
        ((reindexing semantics first).obj family).toFunctor :=
  rfl

/-- The last variable is coherent under the comprehension action of a
semantic mode 2-cell. -/
theorem modeCellComprehensionAction_lastVariable
    (semantics : B ⥤ᵖ Cat.{u, u + 1})
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) (family : FamilyAt semantics target) :
    mapSection
        (variableFamilyAction (semantics.map₂ cell).toNatTrans
          family.toFunctor)
        (lastVariable
          ((reindexing semantics first).obj family).toFunctor) =
      restrictSection
        (modeCellComprehensionAction semantics cell family)
        (lastVariable
          ((reindexing semantics second).obj family).toFunctor) := by
  exact comprehensionAction_lastVariable
    (semantics.map₂ cell).toNatTrans family.toFunctor

/-! ## The selected factor comparison -/

/-- Terms over one selected O/I/E family. -/
abbrev SelectedTerm {mode : ThinMode} (family : SelectedFamily.{u} mode) :=
  TermAt thinSemanticPseudofunctor.{u} family

/-- Transport a term along the factor comparison between the two-step and
direct operational-to-extensional routes. -/
def factorTermAction (family : SelectedFamily.{u} extensional) :
    SelectedTerm ((selectedReindexing.{u} evidenceReadout).obj family) →
      SelectedTerm ((selectedReindexing.{u} observe).obj family) :=
  modeCellTermAction thinSemanticPseudofunctor.{u} factorForward family

/-- The selected term action is exactly the action of the factor
reindexing isomorphism constructed by the family doctrine. -/
theorem factorTermAction_eq_iso_action
    (family : SelectedFamily.{u} extensional) :
    factorTermAction family =
      mapSection (factorReindexingIso.{u}.hom.app family).toNatTrans :=
  rfl

/-- The factor comparison transports every restricted extensional term to
the same term restricted along direct observation. -/
theorem factorTermAction_reindex
    (family : SelectedFamily.{u} extensional)
    (term : SelectedTerm family) :
    factorTermAction family
        (reindexTerm thinSemanticPseudofunctor.{u} evidenceReadout term) =
      reindexTerm thinSemanticPseudofunctor.{u} observe term :=
  modeCellTermAction_reindex
    thinSemanticPseudofunctor.{u} factorForward family term

/-- The factor comparison also induces the coherent functor between the two
operational comprehensions. -/
def factorComprehensionAction
    (family : SelectedFamily.{u} extensional) :
    ((selectedReindexing.{u} evidenceReadout).obj family).toFunctor.Elements
      ⥤
    ((selectedReindexing.{u} observe).obj family).toFunctor.Elements :=
  modeCellComprehensionAction
    thinSemanticPseudofunctor.{u} factorForward family

/-- The selected comprehension action is exactly the category-of-elements
action of the factor reindexing isomorphism. -/
theorem factorComprehensionAction_eq_iso_action
    (family : SelectedFamily.{u} extensional) :
    factorComprehensionAction family =
      elementsAction
        (factorReindexingIso.{u}.hom.app family).toNatTrans :=
  rfl

@[simp] theorem factorComprehensionAction_projection
    (family : SelectedFamily.{u} extensional) :
    factorComprehensionAction family ⋙
        CategoryOfElements.π
          ((selectedReindexing.{u} observe).obj family).toFunctor =
      CategoryOfElements.π
        ((selectedReindexing.{u} evidenceReadout).obj family).toFunctor :=
  rfl

/-- The factor comparison transports the last variable coherently between
the two operational comprehensions. -/
theorem factorComprehensionAction_lastVariable
    (family : SelectedFamily.{u} extensional) :
    mapSection
        (variableFamilyAction
          (thinSemanticPseudofunctor.{u}.map₂ factorForward).toNatTrans
          family.toFunctor)
        (lastVariable
          ((selectedReindexing.{u} evidenceReadout).obj family).toFunctor) =
      restrictSection
        (factorComprehensionAction family)
        (lastVariable
          ((selectedReindexing.{u} observe).obj family).toFunctor) :=
  modeCellComprehensionAction_lastVariable
    thinSemanticPseudofunctor.{u} factorForward family

/-- Term and comprehension coherence coexist with non-equality of the two
authored modality paths. -/
theorem factor_term_comprehension_noncollapse :
    (∀ (family : SelectedFamily.{u} extensional)
        (term : SelectedTerm family),
      factorTermAction family
          (reindexTerm thinSemanticPseudofunctor.{u} evidenceReadout term) =
        reindexTerm thinSemanticPseudofunctor.{u} observe term) ∧
      (∀ family : SelectedFamily.{u} extensional,
        factorComprehensionAction family ⋙
            CategoryOfElements.π
              ((selectedReindexing.{u} observe).obj family).toFunctor =
          CategoryOfElements.π
            ((selectedReindexing.{u} evidenceReadout).obj family).toFunctor) ∧
      evidenceReadout ≠ observe :=
  ⟨factorTermAction_reindex,
    factorComprehensionAction_projection,
    factor_paths_distinct⟩

/-! ## Axiom audit -/

#print axioms restrictSection_action
#print axioms comprehensionAction_lastVariable
#print axioms reindexTerm_identity_coherence
#print axioms reindexTerm_composition_coherence
#print axioms modeCellTermAction_reindex
#print axioms modeCellComprehensionAction_lastVariable
#print axioms factorComprehensionAction_lastVariable
#print axioms factor_term_comprehension_noncollapse

end Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension
