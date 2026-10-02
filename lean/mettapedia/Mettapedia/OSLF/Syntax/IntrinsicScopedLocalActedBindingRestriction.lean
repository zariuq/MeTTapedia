import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedEquivalence

/-!
# Restriction of operational classification to binding and equations

Forgetting event objects and their actions leaves the existing program
interpretation. Restriction along the event-free program section gives the
existing equation-context interpretation. These operations commute, up to
natural isomorphism, with both directions of the two classification
equivalences, including all noninvertible interpretation maps.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

/-- Forget the event objects, substitution and rule actions, retaining the
actual program interpretation and program component of every model map. -/
def forgetPrograms : CategoricalModel R equations (D := D) ⥤
    SatisfyingInterpretation (D := D) (authoredEquationPresentation S equations) where
  obj model := model.program
  map f := f.program
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction of a structured operational interpretation to its event-free
program objects, with the existing equation-context structure. -/
def restrictionToPrograms : StructuredFunctor R equations (D := D) ⥤
    QuotientStructuredFunctor (D := D) (authoredEquationPresentation S equations) where
  obj F :=
    { carrier := programSection R equations ⋙ F.carrier
      preserving := F.program }
  map α := Functor.whiskerLeft (programSection R equations) α
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original binding/equation equivalence recovers its equation-respecting
classifier upon restricting along the equation quotient. -/
noncomputable def bindingEquation_restrictIso :
    (bindingEquationEquivalence (D := D) (authoredEquationPresentation S equations)).functor ⋙
        restrictStructured (authoredEquationPresentation S equations) ≅
      equationClassifier (authoredEquationPresentation S equations) := by
  let E := equationEquivalence (D := D) (authoredEquationPresentation S equations)
  let Q := quotientStructuredEquivalence (D := D) (authoredEquationPresentation S equations)
  change (E.functor ⋙ Q.inverse) ⋙ Q.functor ≅ E.functor
  exact Functor.associator E.functor Q.inverse Q.functor ≪≫
    Functor.isoWhiskerLeft E.functor Q.counitIso ≪≫ Functor.rightUnitor E.functor

variable [HasPullbacks D]

/-- On raw program contexts the two actual classifying functors coincide
through the checked restriction equality. -/
noncomputable def rawProgramRestrictionIso (model : CategoricalModel R equations (D := D)) :
    (equationClassifier (authoredEquationPresentation S equations)).obj model.program ≅
      (restrictStructured (authoredEquationPresentation S equations)).obj
        (restrictionToPrograms.obj ((classifyFunctor (D := D)).obj model)) where
  hom := (eqToIso model.quotient_programSection_classifyingFunctor.symm).hom
  inv := (eqToIso model.quotient_programSection_classifyingFunctor.symm).inv
  hom_inv_id := (eqToIso model.quotient_programSection_classifyingFunctor.symm).hom_inv_id
  inv_hom_id := (eqToIso model.quotient_programSection_classifyingFunctor.symm).inv_hom_id

/-- The raw-program restriction equality is natural on all model maps. -/
noncomputable def rawProgramRestrictionNatIso :
    forgetPrograms (R := R) (equations := equations) ⋙
        equationClassifier (authoredEquationPresentation S equations) ≅
      (classifyFunctor (D := D) (R := R) (equations := equations) ⋙ restrictionToPrograms) ⋙
        restrictStructured (authoredEquationPresentation S equations) :=
  NatIso.ofComponents (fun model => rawProgramRestrictionIso (D := D) model) (fun {M N} f => by
    apply NatTrans.ext
    funext X
    change Model.familyMap f.program.underlying.power X.arities ≫
        (eqToHom N.quotient_programSection_classifyingFunctor.symm).app X =
      (eqToHom M.quotient_programSection_classifyingFunctor.symm).app X ≫
        (CategoricalModel.classifyingMap f).app ((programSection R equations).obj ⟨X⟩)
    have pointM : (eqToHom M.quotient_programSection_classifyingFunctor.symm).app X =
        𝟙 (M.programModel.family X.arities) :=
      (eqToHom_app _ _).trans (eqToHom_refl _ _)
    have pointN : (eqToHom N.quotient_programSection_classifyingFunctor.symm).app X =
        𝟙 (N.programModel.family X.arities) :=
      (eqToHom_app _ _).trans (eqToHom_refl _ _)
    have left : Model.familyMap f.program.underlying.power X.arities ≫
        (eqToHom N.quotient_programSection_classifyingFunctor.symm).app X =
      Model.familyMap f.program.underlying.power X.arities :=
      (congrArg (Model.familyMap f.program.underlying.power X.arities ≫ ·) pointN).trans
        (Category.comp_id _)
    have right : (eqToHom M.quotient_programSection_classifyingFunctor.symm).app X ≫
        (CategoricalModel.classifyingMap f).app ((programSection R equations).obj ⟨X⟩) =
      (CategoricalModel.classifyingMap f).app ((programSection R equations).obj ⟨X⟩) :=
      (congrArg (· ≫ (CategoricalModel.classifyingMap f).app
        ((programSection R equations).obj ⟨X⟩)) pointM).trans (Category.id_comp _)
    exact left.trans ((CategoricalModel.classifyingMap_programSection f ⟨X⟩).symm.trans right.symm))

/-- Classification of the forgotten program interpretation agrees naturally
with restricting the combined classifier to program contexts. -/
noncomputable def bindingRestrictionIso :
    forgetPrograms (R := R) (equations := equations) ⋙
        (bindingEquationEquivalence (D := D) (authoredEquationPresentation S equations)).functor ≅
      classificationEquivalence.functor ⋙ restrictionToPrograms := by
  apply Functor.fullyFaithfulCancelRight
    (restrictStructured (authoredEquationPresentation S equations))
  exact Functor.associator forgetPrograms
      (bindingEquationEquivalence (D := D) (authoredEquationPresentation S equations)).functor
      (restrictStructured (authoredEquationPresentation S equations)) ≪≫
    Functor.isoWhiskerLeft forgetPrograms bindingEquation_restrictIso ≪≫ rawProgramRestrictionNatIso

/-- Recovery of program interpretations commutes naturally with the inverse
classifying equivalences. -/
noncomputable def bindingRecoveryIso :
    classificationEquivalence.inverse ⋙ forgetPrograms (R := R) (equations := equations) ≅
      restrictionToPrograms ⋙
        (bindingEquationEquivalence (D := D) (authoredEquationPresentation S equations)).inverse := by
  let E := classificationEquivalence (R := R) (equations := equations) (D := D)
  let B := bindingEquationEquivalence (D := D) (authoredEquationPresentation S equations)
  let comparison : forgetPrograms (R := R) (equations := equations) ≅
      (E.functor ⋙ restrictionToPrograms) ⋙ B.inverse :=
    Iso.isoCompInverse (H := B) bindingRestrictionIso
  exact Functor.isoWhiskerLeft E.inverse comparison ≪≫
    (Functor.associator E.inverse (E.functor ⋙ restrictionToPrograms) B.inverse).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator E.inverse E.functor restrictionToPrograms).symm B.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight E.counitIso restrictionToPrograms) B.inverse ≪≫
    Functor.isoWhiskerRight (Functor.leftUnitor restrictionToPrograms) B.inverse

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
