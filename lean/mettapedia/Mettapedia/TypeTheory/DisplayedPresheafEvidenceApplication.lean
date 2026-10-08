import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution

/-!
# Applying universally transported dependent evidence

Native function evidence can be evaluated at a natural dependent argument.
Evaluation is a map of families, so it commutes with universal receipt
descent. The dependent codomain and the complete evidence value are kept.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceApplication

open CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafSlicePi
open DisplayedPresheafPi DisplayedPresheafEvidenceTransport
open DisplayedPresheafEvidenceUniversal

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

/-- Native abstraction for a complete family of certificates, rather than
only a single global body section. -/
noncomputable def abstractFamily (A : DisplayedFamily Q)
    (B : DisplayedFamily (totalSpace A)) {Head : DisplayedFamily Q}
    (body : reindexDisplayed (totalProjection A) Head ⟶ B) : Head ⟶ piDisplayed A B :=
  (displayedProductAdjunction A).homEquiv Head B body

theorem abstractFamily_evaluation (A : DisplayedFamily Q)
    (B : DisplayedFamily (totalSpace A)) {Head : DisplayedFamily Q}
    (body : reindexDisplayed (totalProjection A) Head ⟶ B) :
    (reindexFunctor (totalProjection A)).map (abstractFamily A B body) ≫
      (displayedProductAdjunction A).counit.app B = body :=
  ((displayedProductAdjunction A).homEquiv Head B).symm_apply_apply body

theorem abstractFamily_value (A : DisplayedFamily Q)
    (B : DisplayedFamily (totalSpace A)) {Head : DisplayedFamily Q}
    (body : reindexDisplayed (totalProjection A) Head ⟶ B)
    (point : (totalSpace A).Elements)
    (certificate : Head.obj ((totalProjection A).mapElements.obj point)) :
    ((displayedProductAdjunction A).counit.app B).app point
        ((abstractFamily A B body).app ((totalProjection A).mapElements.obj point) certificate) =
      body.app point certificate :=
  congrArg (fun result : reindexDisplayed (totalProjection A) Head ⟶ B =>
    result.app point certificate) (abstractFamily_evaluation A B body)

/-- Actual evaluation from the native product adjunction, specialized to
an argument section in the same program context. -/
noncomputable def applyAt (A : DisplayedFamily Q)
    (B : DisplayedFamily (totalSpace A)) (argument : A.sections) :
    piDisplayed A B ⟶ reindexDisplayed (sectionLift A argument) B :=
  Functor.whiskerLeft (sectionLift A argument).mapElements
    ((displayedProductAdjunction A).counit.app B)

theorem applyAt_value (A : DisplayedFamily Q) (B : DisplayedFamily (totalSpace A))
    (argument : A.sections) (function : (piDisplayed A B).sections) (point : Q.Elements) :
    (applyAt A B argument).app point (function.val point) =
      (appDisplayed function argument).val point := by
  symm
  exact piSectionEquiv_inverse_value A B function
    ((sectionLift A argument).mapElements.obj point)

theorem applyAt_abstraction (A : DisplayedFamily Q)
    (B : DisplayedFamily (totalSpace A)) (argument : A.sections) (body : B.sections) :
    (Functor.sectionsFunctor Q.Elements).map (applyAt A B argument) (lamDisplayed body) =
      reindexDisplayedSection (sectionLift A argument) B body := by
  apply (Functor.sections_ext_iff).2
  intro point
  change (applyAt A B argument).app point ((lamDisplayed body).val point) = _
  rw [applyAt_value, pi_beta]

/-- Evaluating the compiled dependent function agrees with compiling
the source evidence map followed by its pulled-back evaluator. -/
theorem descend_application (f : P ⟶ Q) {Evidence : DisplayedFamily P}
    (A : DisplayedFamily Q) (B : DisplayedFamily (totalSpace A))
    (argument : A.sections)
    (body : Evidence ⟶ reindexDisplayed f (piDisplayed A B)) :
    descend f body ≫ applyAt A B argument =
      descend f (body ≫ (reindexFunctor f).map (applyAt A B argument)) :=
  (descend_naturality f body (applyAt A B argument)).symm

theorem application_retains_supplied_value (f : P ⟶ Q) {Evidence : DisplayedFamily P}
    (A : DisplayedFamily Q) (B : DisplayedFamily (totalSpace A))
    (argument : A.sections)
    (body : Evidence ⟶ reindexDisplayed f (piDisplayed A B))
    (point : P.Elements) (certificate : Evidence.obj point) :
    (applyAt A B argument).app (f.mapElements.obj point)
        ((descend f body).app (f.mapElements.obj point) ((unit f Evidence).app point certificate)) =
      (applyAt A B argument).app (f.mapElements.obj point) (body.app point certificate) := by
  rw [descend_unit]

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceApplication
