import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory

/-!
# Read-only steps as context extension in the classifying category

Uses `ClassifyingContext`, `pair`, `fstProjection`, `sndProjection` and
`comp_pair`. A read-only step keeps every premise occurrence of `Γ` and adds one judgment
derived by a rule from the occurrences its match picks: `⟨𝟙 Γ, picked ≫ rule⟩`.

* the old occurrences are kept exactly (weakening is the first projection);
* a match that picks one occurrence for two ports factors through the diagonal (contraction);
* two steps paste by composition, and the second conclusion is the second rule with the
  first derivation substituted into its premise holes (cut).

This is the classifying-category half of the correspondence only. No functor from occurrence
stores and selections of the constraint rewriting step into this category is defined here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadOnlyContextExtension

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.ClassifyingContext
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker

variable {definition : ValidatedCalculusLanguageDef}

/-- A read-only step: keep `Γ`, add the conclusion derived from the picked occurrences. -/
def readStep {Γ premises conclusion : ClassifyingContext definition}
    (picked : Γ ⟶ premises) (rule : premises ⟶ conclusion) : Γ ⟶ concat Γ conclusion :=
  pair (𝟙 Γ) (picked ≫ rule)

/-- Weakening: every old occurrence is kept as itself. -/
theorem readStep_keeps {Γ premises conclusion : ClassifyingContext definition}
    (picked : Γ ⟶ premises) (rule : premises ⟶ conclusion) :
    readStep picked rule ≫ fstProjection Γ conclusion = 𝟙 Γ :=
  pair_fst _ _

/-- The added judgment is the rule applied to the picked occurrences. -/
theorem readStep_adds {Γ premises conclusion : ClassifyingContext definition}
    (picked : Γ ⟶ premises) (rule : premises ⟶ conclusion) :
    readStep picked rule ≫ sndProjection Γ conclusion = picked ≫ rule :=
  pair_snd _ _

/-- The diagonal of the cartesian structure. -/
def diagonal (A : ClassifyingContext definition) : A ⟶ concat A A := pair (𝟙 A) (𝟙 A)

/-- Contraction: a match citing one occurrence at two read ports factors through the diagonal. -/
theorem aliased_match_is_the_diagonal {Γ A : ClassifyingContext definition} (picked : Γ ⟶ A) :
    pair picked picked = picked ≫ diagonal A := by
  rw [diagonal, comp_pair, Category.comp_id]

/-- Pasting two read-only steps keeps the original context. -/
theorem pasted_steps_keep {Γ first conclusion₁ second conclusion₂ : ClassifyingContext definition}
    (picked₁ : Γ ⟶ first) (rule₁ : first ⟶ conclusion₁)
    (picked₂ : concat Γ conclusion₁ ⟶ second) (rule₂ : second ⟶ conclusion₂) :
    readStep picked₁ rule₁ ≫ readStep picked₂ rule₂ ≫
        fstProjection (concat Γ conclusion₁) conclusion₂ ≫ fstProjection Γ conclusion₁ = 𝟙 Γ := by
  rw [← Category.assoc (readStep picked₂ rule₂), readStep_keeps, Category.id_comp, readStep_keeps]

/-- Cut: the second conclusion is the second rule with the first step substituted into the
holes its match picked. -/
theorem pasted_steps_substitute {Γ first conclusion₁ second conclusion₂ : ClassifyingContext definition}
    (picked₁ : Γ ⟶ first) (rule₁ : first ⟶ conclusion₁)
    (picked₂ : concat Γ conclusion₁ ⟶ second) (rule₂ : second ⟶ conclusion₂) :
    readStep picked₁ rule₁ ≫ readStep picked₂ rule₂ ≫ sndProjection (concat Γ conclusion₁) conclusion₂ =
      (readStep picked₁ rule₁ ≫ picked₂) ≫ rule₂ := by
  rw [readStep_adds, Category.assoc]


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadOnlyContextExtension
