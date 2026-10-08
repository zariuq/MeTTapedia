import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSubstitution

/-!
# Independent material dependent sums at the successor bound

The upper sum is formed from the raised domain and the raised dependent
body. Its native receipts retain both components, and its actual ordered
pair readings match the lifted lower readings. The comparison also covers
arbitrary upper members and entire literal sections.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftSums

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphMaterialFamilies ContextualGraphMaterialProducts
open ContextualGraphMaterialLift

universe u
variable {D : Type u} [Category.{u} D] {original : D ⥤ Type u}
variable (domain : Family original) (body : Family (total domain.native))

abbrev upper := sigma (raise domain) (raisedBody domain body)
abbrev retained := raise (sigma domain body)

def forward : NaturalHom (upper domain body).native (retained domain body).native where
  app _ term := ULift.up ⟨term.1.down, term.2.down⟩
  naturality _ _ := rfl

def backward : NaturalHom (retained domain body).native (upper domain body).native where
  app _ term := ⟨ULift.up term.down.1, ULift.up term.down.2⟩
  naturality _ _ := rfl

def nativeEquiv (point : (base original).Elements) :
    (upper domain body).native.obj point ≃ (retained domain body).native.obj point where
  toFun := (forward domain body).app point
  invFun := (backward domain body).app point
  left_inv _ := rfl
  right_inv _ := rfl

theorem forward_backward : (forward domain body).comp (backward domain body) =
    ContextualSmallMapConstructions.identity (upper domain body).native := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem backward_forward : (backward domain body).comp (forward domain body) =
    ContextualSmallMapConstructions.identity (retained domain body).native := by
  apply NaturalHom.ext
  intro _ _
  rfl

def readingComparison (point : (base original).Elements)
    (term : (upper domain body).native.obj point) :
    Equal (termValue (upper domain body) point term)
      (termValue (retained domain body) point ((forward domain body).app point term)) :=
  (ContextualGraphUniverseLiftPairs.orderedPairComparison
    (termValue domain ((elementsDown original).obj point) term.1.down)
    (termValue body ⟨point.1.down, ⟨point.2.down, term.1.down⟩⟩ term.2.down)).symm

def carrierComparison (point : (base original).Elements) :
    Equal (ContextualGraphUniverseLift.value
      ((carrier (sigma domain body)).app point.1.down point.2.down))
      ((carrier (upper domain body)).app point.1 point.2) :=
  (ContextualGraphMaterialLift.carrierComparison (sigma domain body) point.1 point.2.down).trans
    (ContextualGraphMaterialSubstitution.carrierCongr
      (upper domain body) (retained domain body)
      (forward domain body) (backward domain body)
      (readingComparison domain body)
      (fun point term => (readingComparison domain body point
        ((backward domain body).app point term)).symm) point).symm

def sectionComparison : (upper domain body).native.sections ≃ (retained domain body).native.sections where
  toFun := (forward domain body).mapSection
  invFun := (backward domain body).mapSection
  left_inv _ := rfl
  right_inv _ := rfl

def literalSectionComparison : (literal (upper domain body)).sections ≃
    (literal (retained domain body)).sections :=
  (sectionDecoder (upper domain body)).trans
    ((sectionComparison domain body).trans (sectionDecoder (retained domain body)).symm)

theorem literal_first (term : (literal (upper domain body)).sections)
    (point : (base original).Elements) :
    ((sectionDecoder (retained domain body)
      (literalSectionComparison domain body term)).val point).down.1 =
      ((sectionDecoder (upper domain body) term).val point).1.down := rfl

theorem literal_second (term : (literal (upper domain body)).sections)
    (point : (base original).Elements) :
    ((sectionDecoder (retained domain body)
      (literalSectionComparison domain body term)).val point).down.2 =
      ((sectionDecoder (upper domain body) term).val point).2.down := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftSums
