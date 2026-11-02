import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnusedExtensions
import Mathlib.Logic.Equiv.Set

/-!
# An injective declaration extension splits into old and unused names

The complement keeps each off-image declaration with its original arity.
Splitting is an arity-preserving equivalence, not a total retraction into
the old declarations. No term inhabiting an old sort is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels

variable {S : Signature} {V : Type} {source : V → MetaArity S}

def trans (first : Extension source) (second : Extension first.declarations) : Extension source where
  Names := second.Names
  declarations := second.declarations
  name := second.name ∘ first.name
  injective := second.injective.comp first.injective
  preserves name := (second.preserves (first.name name)).trans (first.preserves name)

theorem trans_assignment (first : Extension source) (second : Extension first.declarations) :
    (first.trans second).assignment = Assignment.compose second.assignment first.assignment :=
  (reindex_compose _ _ first.preserves second.preserves).symm

abbrev Complement (extension : Extension source) := ↥((Set.range extension.name)ᶜ)

def complementDeclarations (extension : Extension source) : Complement extension → MetaArity S :=
  fun name => extension.declarations name.val

noncomputable def splitNames (extension : Extension source) : Complement extension ⊕ V ≃ extension.Names := by
  classical
  exact (Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (Equiv.ofInjective extension.name extension.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range extension.name)))

theorem splitNames_complement (extension : Extension source) (name : Complement extension) :
    splitNames extension (.inl name) = name.val := by
  classical
  simp only [splitNames, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.refl_apply, Equiv.Set.sumCompl_apply_inr]

theorem splitNames_source (extension : Extension source) (name : V) :
    splitNames extension (.inr name) = extension.name name := by
  classical
  simp only [splitNames, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]

theorem splitPreserves (extension : Extension source) (name : Complement extension ⊕ V) :
    extension.declarations (splitNames extension name) =
      extended (complementDeclarations extension) source name := by
  cases name with
  | inl name => rw [splitNames_complement]; rfl
  | inr name => rw [splitNames_source]; exact extension.preserves name

theorem unsplitPreserves (extension : Extension source) (name : extension.Names) :
    extended (complementDeclarations extension) source ((splitNames extension).symm name) =
      extension.declarations name := by
  have same := splitPreserves extension ((splitNames extension).symm name)
  rw [(splitNames extension).apply_symm_apply] at same
  exact same.symm

noncomputable def splitAssignment (extension : Extension source) :
    Assignment (extended (complementDeclarations extension) source) extension.declarations :=
  reindex (splitNames extension) (splitPreserves extension)

noncomputable def unsplitAssignment (extension : Extension source) :
    Assignment extension.declarations (extended (complementDeclarations extension) source) :=
  reindex (splitNames extension).symm (unsplitPreserves extension)

private theorem generator_cast_agrees {Names : Type} (declaration : Names → MetaArity S)
    {first second : Names} (same : first = second) (expected : MetaArity S)
    (firstPreserves : declaration first = expected) (secondPreserves : declaration second = expected) :
    castMetaBody (V := signature S declaration) firstPreserves (generator declaration first) =
      castMetaBody (V := signature S declaration) secondPreserves (generator declaration second) := by
  cases same
  rfl

theorem split_inclusion (extension : Extension source) :
    Assignment.compose (splitAssignment extension) (inclusion (complementDeclarations extension) source) =
      extension.assignment := by
  funext name
  change instantiate (splitAssignment extension)
      (generator (extended (complementDeclarations extension) source) (Sum.inr name)) = extension.assignment name
  rw [instantiate_generator]
  change reindex (splitNames extension) (splitPreserves extension) (Sum.inr name) =
    reindex extension.name extension.preserves name
  unfold reindex
  change castMetaBody (V := signature S extension.declarations)
      (a := extension.declarations (splitNames extension (.inr name))) (b := source name)
      (splitPreserves extension (.inr name))
      (generator extension.declarations (splitNames extension (.inr name))) =
    castMetaBody (V := signature S extension.declarations) (extension.preserves name)
      (generator extension.declarations (extension.name name))
  exact generator_cast_agrees extension.declarations (splitNames_source extension name) (source name) _ _

theorem split_inverse (extension : Extension source) :
    Assignment.compose (unsplitAssignment extension) (splitAssignment extension) =
      generator (extended (complementDeclarations extension) source) :=
  reindex_left_inverse _ _ _ _ (splitNames extension).left_inv

theorem unsplit_inverse (extension : Extension source) :
    Assignment.compose (splitAssignment extension) (unsplitAssignment extension) =
      generator extension.declarations :=
  reindex_left_inverse _ _ _ _ (splitNames extension).right_inv

/-- Splitting an extension back into old names and its unused complement
recovers the ordinary capture inclusion on every original declaration. -/
theorem unsplit_assignment (extension : Extension source) :
    Assignment.compose extension.unsplitAssignment extension.assignment =
      inclusion extension.complementDeclarations source := by
  rw [← extension.split_inclusion, Assignment.compose_associative,
    extension.split_inverse, Assignment.compose_identity_left]

/-- Adding fresh declarations cannot identify two original terms. No term
is invented to interpret names outside the original image. -/
theorem instantiate_injective (extension : Extension source) {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (instantiate (Γ := Γ) (sort := sort) extension.assignment) := by
  intro first second same
  apply ContextualPrefixModels.inclusion_injective extension.complementDeclarations source
  have restored := congrArg (instantiate extension.unsplitAssignment) same
  simpa only [← Assignment.instantiate_compose, extension.unsplit_assignment] using restored

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension
