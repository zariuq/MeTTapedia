import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Structural category of interactive language presentations

An interactive presentation selects, from one exact validated `LanguageDef`,
an interacting carrier sort, a contact constructor on that sort, and an
authored rewrite whose source is headed by that constructor.  Nothing is
copied into a second presentation record: every selected item carries its
membership proof in the original declaration lists.

This is the structural substrate of iGSLT.  Behavioral simulations and
bisimilarity preservation are deliberately added at the semantic layer; a
structural declaration map alone need not preserve behavior when its target
authors additional rewrites.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism

/-- The two declaration shapes that represent binary contact.  A language
may use an ordinary binary constructor or an authored homogeneous collection
constructor whose concrete term representation is the bare collection node. -/
inductive ContactRepresentation where
  | binary
  | collection (collectionType : CollType)
deriving DecidableEq, Repr

/-- Read the representation of binary contact from a selected constructor.
The result sort and both argument sorts must be the selected interacting sort.
The collection case records the existing bare-collection representation; it
does not grant contextual reduction authority to collections. -/
def contactRepresentation? (sort : TypeDecl) (constructor : GrammarRule) :
    Option ContactRepresentation :=
  if constructor.category = sort.name then
    match constructor.params with
    | [.simple _ (.base left), .simple _ (.base right)] =>
        if left = sort.name ∧ right = sort.name then
          some .binary
        else
          none
    | [.simple _ (.collection collectionType (.base element))] =>
        if element = sort.name then
          some (.collection collectionType)
        else
          none
    | _ => none
  else
    none

/-- The left side of an interaction rewrite is headed by the selected contact
representation.  In the bare-collection case, two explicit components are
required; an open rest may retain the surrounding parallel context. -/
def InteractionHeaded
    (representation : ContactRepresentation)
    (constructor : GrammarRule) (pattern : Pattern) : Prop :=
  match representation, pattern with
  | .binary, .apply label [_, _] => label = constructor.label
  | .collection expected, .collection actual elements _ =>
      actual = expected ∧ 2 ≤ elements.length
  | _, _ => False

/-- An exact validated operational theory with authored interaction data.
The selected sort, constructor, and rewrite are subobjects of the sole
`LanguageDef`; the representation witness only exposes their existing shape. -/
structure InteractivePresentation where
  presentation : ValidatedLanguageDef
  interactingSort : AuthoredSort presentation
  contactConstructor : AuthoredConstructor presentation
  interactionRewrite : AuthoredRewrite presentation
  contactRepresentation : ContactRepresentation
  representsContact :
    contactRepresentation?
      interactingSort.1 contactConstructor.1 = some contactRepresentation
  interactionHeaded :
    InteractionHeaded contactRepresentation contactConstructor.1
      interactionRewrite.1.left

/-- A structural theory map preserving the selected interaction interface.
Because the base map preserves every declaration of the source, this is not a
renamed policy switch or a second operational semantics. -/
structure InteractiveMorphism
    (source target : InteractivePresentation) where
  structural : StructuralMorphism source.presentation target.presentation
  mapsInteractingSort :
    structural.mapSort source.interactingSort = target.interactingSort
  mapsContactConstructor :
    structural.mapConstructor source.contactConstructor =
      target.contactConstructor
  mapsInteractionRewrite :
    structural.mapRewrite source.interactionRewrite = target.interactionRewrite

namespace InteractiveMorphism

/-- Interaction-preserving structural maps are proof-irrelevant beyond their
underlying structural map. -/
@[ext]
theorem ext {source target : InteractivePresentation}
    {first second : InteractiveMorphism source target}
    (structural : first.structural = second.structural) : first = second := by
  cases first
  cases second
  cases structural
  rfl

/-- Identity interaction-preserving map. -/
def id (presentation : InteractivePresentation) :
    InteractiveMorphism presentation presentation where
  structural := StructuralMorphism.id presentation.presentation
  mapsInteractingSort := by simp
  mapsContactConstructor := by simp
  mapsInteractionRewrite := by simp

/-- Composition of interaction-preserving structural maps. -/
def comp {first second third : InteractivePresentation}
    (left : InteractiveMorphism first second)
    (right : InteractiveMorphism second third) :
    InteractiveMorphism first third where
  structural := StructuralMorphism.comp left.structural right.structural
  mapsInteractingSort := by
    rw [StructuralMorphism.mapSort_comp, left.mapsInteractingSort]
    exact right.mapsInteractingSort
  mapsContactConstructor := by
    rw [StructuralMorphism.mapConstructor_comp,
      left.mapsContactConstructor]
    exact right.mapsContactConstructor
  mapsInteractionRewrite := by
    rw [StructuralMorphism.mapRewrite_comp, left.mapsInteractionRewrite]
    exact right.mapsInteractionRewrite

end InteractiveMorphism

/-- Interactive presentations and exact interaction-preserving theory maps
form a Mathlib category. -/
instance : Category InteractivePresentation where
  Hom := InteractiveMorphism
  id := InteractiveMorphism.id
  comp := InteractiveMorphism.comp
  id_comp morphism := by
    apply InteractiveMorphism.ext
    rfl
  comp_id morphism := by
    apply InteractiveMorphism.ext
    rfl
  assoc first second third := by
    apply InteractiveMorphism.ext
    rfl

/-! ## Strict-core rho instance and controls -/

/-- The strict-core rho declaration, retained verbatim with its established
validation theorem. -/
def rhoValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨rhoCalc, rhoCalc_validate_eq_nil⟩

/-- Pure rho is interactive because its authored process sort, parallel
constructor, and COMM rewrite inhabit the exact validated `rhoCalc` lists.
The parallel constructor's bare bag is representation data only; `ParCong`
remains the sole authority for contextual parallel reduction. -/
def rhoInteractivePresentation : InteractivePresentation where
  presentation := rhoValidatedLanguageDef
  interactingSort :=
    ⟨rhoCalc.types[0], by
      change List.Mem rhoCalc.types[0] rhoCalc.types
      exact List.getElem_mem (by simp [rhoCalc])⟩
  contactConstructor :=
    ⟨rhoCalc.terms[3], by
      change List.Mem rhoCalc.terms[3] rhoCalc.terms
      exact List.getElem_mem (by simp [rhoCalc])⟩
  interactionRewrite :=
    ⟨rhoCalc.rewrites[0], by
      change List.Mem rhoCalc.rewrites[0] rhoCalc.rewrites
      exact List.getElem_mem (by simp [rhoCalc])⟩
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, rhoCalc, rhoCommRewrite]

/-- Positive control: the authored COMM source has at least the two explicit
parallel participants required by contact. -/
theorem rho_comm_interaction_headed :
    InteractionHeaded rhoInteractivePresentation.contactRepresentation
      rhoInteractivePresentation.contactConstructor.1
      rhoInteractivePresentation.interactionRewrite.1.left :=
  rhoInteractivePresentation.interactionHeaded

/-- Negative control: free Drop is not an interaction source. -/
theorem rho_free_drop_not_interaction_headed (name : Pattern) :
    ¬ InteractionHeaded rhoInteractivePresentation.contactRepresentation
      rhoInteractivePresentation.contactConstructor.1
      (.apply "PDrop" [name]) := by
  simp [rhoInteractivePresentation, InteractionHeaded]

end Mettapedia.GSLT.LanguageDef
