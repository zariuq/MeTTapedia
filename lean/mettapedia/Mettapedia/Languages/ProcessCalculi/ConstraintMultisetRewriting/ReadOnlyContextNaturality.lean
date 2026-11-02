import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadOnlyContextExtension

/-! # Context extension commutes with reindexing its retained premises -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadOnlyContextExtension

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.ClassifyingContext
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

def carry {first second : ClassifyingContext definition} (mapping : first ⟶ second)
    (conclusion : ClassifyingContext definition) : concat first conclusion ⟶ concat second conclusion :=
  pair (fstProjection first conclusion ≫ mapping) (sndProjection first conclusion)

theorem readStep_naturality {first second premises conclusion : ClassifyingContext definition}
    (mapping : first ⟶ second) (pickedFirst : first ⟶ premises) (pickedSecond : second ⟶ premises)
    (rule : premises ⟶ conclusion) (selected : mapping ≫ pickedSecond = pickedFirst) :
    mapping ≫ readStep pickedSecond rule = readStep pickedFirst rule ≫ carry mapping conclusion := by
  unfold readStep carry
  rw [comp_pair, comp_pair]
  apply congrArg₂ pair
  · rw [← Category.assoc, pair_fst, Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, selected, pair_snd]

theorem transported_square
    {first second physicalFirst physicalSecond shownFirst shownSecond : ClassifyingContext definition}
    (displayFirst : physicalFirst = shownFirst) (displaySecond : physicalSecond = shownSecond)
    (mapping : first ⟶ second) (left : first ⟶ shownFirst) (right : second ⟶ shownSecond)
    (terminal : shownFirst ⟶ shownSecond) (square : mapping ≫ right = left ≫ terminal) :
    mapping ≫ (right ≫ eqToHom displaySecond.symm) =
      (left ≫ eqToHom displayFirst.symm) ≫
        (eqToHom displayFirst ≫ terminal ≫ eqToHom displaySecond.symm) := by
  cases displayFirst
  cases displaySecond
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using square

theorem paste_squares
    {first₁ first₂ middle₁ middle₂ last₁ last₂ : ClassifyingContext definition}
    (initial : first₁ ⟶ first₂) (middle : middle₁ ⟶ middle₂) (terminal : last₁ ⟶ last₂)
    (firstLeft : first₁ ⟶ middle₁) (firstRight : first₂ ⟶ middle₂)
    (lastLeft : middle₁ ⟶ last₁) (lastRight : middle₂ ⟶ last₂)
    (firstSquare : initial ≫ firstRight = firstLeft ≫ middle)
    (lastSquare : middle ≫ lastRight = lastLeft ≫ terminal) :
    initial ≫ (firstRight ≫ lastRight) = (firstLeft ≫ lastLeft) ≫ terminal := by
  calc
    _ = (initial ≫ firstRight) ≫ lastRight := (Category.assoc _ _ _).symm
    _ = (firstLeft ≫ middle) ≫ lastRight := congrArg (fun part => part ≫ lastRight) firstSquare
    _ = firstLeft ≫ (middle ≫ lastRight) := Category.assoc _ _ _
    _ = firstLeft ≫ (lastLeft ≫ terminal) := congrArg (fun part => firstLeft ≫ part) lastSquare
    _ = _ := (Category.assoc _ _ _).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadOnlyContextExtension
