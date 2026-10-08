import Mettapedia.TypeTheory.ContextualProductSections
import Mettapedia.TypeTheory.CwfYonedaSumComparison
import Mettapedia.TypeTheory.DisplayedPresheafPi

/-!
# Source functions and complete native dependent function sections

Actual source abstraction and generic-variable application are compared
with the chosen native right-Kan product. Both directions retain the entire
body section over the original represented comprehension. This section
comparison does not identify the two chosen type objects by equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi ContextualProductSections
open ContextualPiEta

universe u w w'
variable (C : Cwf.{u, u, w, w'})

noncomputable section

def representedBodySection {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (sectionValue : (family C B).sections) : (dependentBodyFamily C A B).sections :=
  reindexDisplayedSection (comprehensionIso C A).hom (family C B) sectionValue

def originalBodySection {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (sectionValue : (dependentBodyFamily C A B).sections) : (family C B).sections where
  val point := sectionValue.val ((comprehensionIso C A).inv.mapElements.obj point)
  property := by
    intro first second before
    exact sectionValue.property ((comprehensionIso C A).inv.mapElements.map before)

theorem original_represented_body {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (sectionValue : (family C B).sections) :
    originalBodySection C (representedBodySection C (A := A) sectionValue) = sectionValue := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

theorem represented_original_body {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (sectionValue : (dependentBodyFamily C A B).sections) :
    representedBodySection C (originalBodySection C sectionValue) = sectionValue := by
  apply (Functor.sections_ext_iff).2
  rintro ⟨world, environment, receipt, indexed⟩
  change C.Sub world.unop.val Γ at environment
  change C.Sub world.unop.val (C.ext Γ A) at receipt
  change C.compS (C.wk A) receipt = environment at indexed
  subst environment
  rfl

/-- Complete original body sections and represented comprehension sections
are in bijection through the actual comprehension isomorphism. -/
def representedBodySectionEquiv {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    (family C B).sections ≃ (dependentBodyFamily C A B).sections where
  toFun := representedBodySection C
  invFun := originalBodySection C
  left_inv := original_represented_body C
  right_inv := represented_original_body C

def bodyTermSectionEquiv {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm (C.ext Γ A) B ≃ (dependentBodyFamily C A B).sections :=
  (termSectionEquiv C B).trans (representedBodySectionEquiv C A B)

def representedProductFamily {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    DisplayedFamily (contextFace C Γ) :=
  piDisplayed (family C A) (dependentBodyFamily C A B)

/-- Every natural function section of the chosen native product has one
original source function, with its complete generic dependent body. -/
def productTermSectionEquiv (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm Γ (products.operations.pi A B) ≃ (representedProductFamily C A B).sections :=
  (bodyEquiv products A B).trans
    ((bodyTermSectionEquiv C A B).trans
      (piSectionEquiv (family C A) (dependentBodyFamily C A B)))

def interpretFunction (products : StableProducts C) {Γ : C.Ctx}
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.operations.pi A B)) :
    (representedProductFamily C A B).sections :=
  productTermSectionEquiv C products A B function

/-- Native abstraction of the original whole body agrees with source
abstraction, by the source beta law at the actual newest variable. -/
theorem interpretFunction_lam (products : StableProducts C) {Γ : C.Ctx}
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)} (body : C.Tm (C.ext Γ A) B) :
    interpretFunction C products (products.operations.lam body) =
      lamDisplayed (representedBodySection C (A := A) (interpretTerm C body)) := by
  change lamDisplayed (bodyTermSectionEquiv C A B
    (genericSection products.operations products.substitution.1 (products.operations.lam body))) = _
  rw [genericSection_lam]
  rfl

/-- The native inverse reads the entire source generic-variable body. -/
theorem interpretFunction_body (products : StableProducts C) {Γ : C.Ctx}
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.operations.pi A B)) :
    (piSectionEquiv (family C A) (dependentBodyFamily C A B)).symm
        (interpretFunction C products function) =
      representedBodySection C (A := A)
        (interpretTerm C (genericSection products.operations products.substitution.1 function)) := by
  exact (piSectionEquiv _ _).symm_apply_apply _

/-- Application keeps the supplied first witness and returns the exact
original generic-body display map at that witness, at every future world. -/
theorem interpretFunction_application (products : StableProducts C) {Γ : C.Ctx}
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.operations.pi A B)) (argument : C.Tm Γ A)
    (world : C.base.Contextᵒᵖ) (environment : C.Sub world.unop.val Γ) :
    ((appDisplayed (interpretFunction C products function) (interpretTerm C argument)).val
        ⟨world, environment⟩).val =
      C.pair (C.pair environment A (C.tmSub argument environment)) B
        (C.tmSub (genericSection products.operations products.substitution.1 function)
          (C.pair environment A (C.tmSub argument environment))) := by
  unfold appDisplayed
  rw [interpretFunction_body]
  rfl

end

end Mettapedia.TypeTheory.CwfYoneda
