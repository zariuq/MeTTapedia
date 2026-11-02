import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModels

/-!
# Explicit common extensions for unused contextual declarations

Restricting an extended model forgets only the new source names. Adding
unused names to a matching witness keeps its original target declaration
family and gives the new names a separate summand. The assignment squares
are proved from the existing reindexing and capture transport operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels

variable {S : Signature} {Extra V : Type} (unused : Extra → MetaArity S) {declaration : V → MetaArity S}

def restrictUnused (extension : Extension (extended unused declaration)) : Extension declaration where
  Names := extension.Names
  declarations := extension.declarations
  name identity := extension.name (.inr identity)
  injective := fun _ _ same => Sum.inr.inj (extension.injective same)
  preserves identity := extension.preserves (.inr identity)

theorem restrictUnused_assignment (extension : Extension (extended unused declaration)) :
    (restrictUnused unused extension).assignment =
      Assignment.compose extension.assignment (inclusion unused declaration) := by
  funext name
  exact (instantiate_generator extension.assignment (Sum.inr name)).symm

def addUnused (extension : Extension declaration) : Extension (extended unused declaration) where
  Names := Extra ⊕ extension.Names
  declarations := extended unused extension.declarations
  name := Sum.map id extension.name
  injective := by
    intro first second same
    cases first with
    | inl first =>
        cases second with
        | inl second => exact congrArg Sum.inl (Sum.inl.inj same)
        | inr second => cases same
    | inr first =>
        cases second with
        | inl second => cases same
        | inr second => exact congrArg Sum.inr (extension.injective (Sum.inr.inj same))
  preserves identity := by
    cases identity with
    | inl name => rfl
    | inr name => exact extension.preserves name

theorem addUnused_assignment (extension : Extension declaration) :
    (addUnused unused extension).assignment = ContextualStoredRows.liftCaptures unused extension.assignment := by
  funext identity
  cases identity with
  | inl name => rfl
  | inr name =>
      change castMetaBody (V := signature S (extended unused extension.declarations))
          (extension.preserves name) (generator (extended unused extension.declarations) (.inr (extension.name name))) =
        instantiate (inclusion unused extension.declarations)
          (castMetaBody (V := signature S extension.declarations) (extension.preserves name)
            (generator extension.declarations (extension.name name)))
      rw [instantiate_castMetaBody, instantiate_generator]
      rfl

theorem addUnused_square (extension : Extension declaration) :
    Assignment.compose (addUnused unused extension).assignment (inclusion unused declaration) =
      Assignment.compose (inclusion unused extension.declarations) extension.assignment := by
  rw [addUnused_assignment]
  exact lifted_capture_assignment unused extension.assignment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension
