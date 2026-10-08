import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilySubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialCwf

/-!
# Actual contextual sums, products and application through graph receipts

The represented types are the constructed native sum and complete future
product families. Their graphs are built from those families alone, with
no supplied term graphs. Abstraction compares entire compatible sections;
application uses the actual comprehension substitution. Both dependent
sum coordinates remain available through the same literal decoder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyProducts

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphFamilyRepresentation ContextualGraphFamilySubstitution

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : (total domain).Elements ⥤ Type u)

def nativeLambda : body.sections ≃ (piDisplayed domain body).sections :=
  (bodySectionEquiv domain body).trans
    ((ContextualAuthoredMaterialCwf.sectionHomEquiv (indexedBody domain body)).trans
      ((ContextualSmallFamilyNativeAdjunction.smallHomEquiv domain
        (indexedBody domain body) (ContextualAuthoredMaterialCwf.unitNative base.Elements)).trans
        (ContextualAuthoredMaterialCwf.sectionHomEquiv (piDisplayed domain body)).symm))

def lambdaEquiv : (literal body).sections ≃ (literal (piDisplayed domain body)).sections :=
  (sectionDecoder body).trans ((nativeLambda domain body).trans (sectionDecoder (piDisplayed domain body)).symm)

theorem lambda_future_value (term : (literal body).sections) (point : base.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain point).Elements) :
    (decode (piDisplayed domain body) point ((lambdaEquiv domain body term).val point)).val argument =
      decode body ((flatten domain).obj ((ContextualSmallFamilyTypeFormers.futureArguments domain point).obj argument))
        (term.val ((flatten domain).obj ((ContextualSmallFamilyTypeFormers.futureArguments domain point).obj argument))) := rfl

theorem lambda_eta (function : (literal (piDisplayed domain body)).sections) :
    lambdaEquiv domain body ((lambdaEquiv domain body).symm function) = function :=
  (lambdaEquiv domain body).apply_symm_apply function

def argumentSubstitution (term : domain.sections) : NaturalHom base (total domain) where
  app point parameter := ⟨parameter, term.val ⟨point, parameter⟩⟩
  naturality {first second} step parameter :=
    Sigma.ext rfl (heq_of_eq (term.property (CategoryOfElements.homMk (F := base)
      ⟨first, parameter⟩ ⟨second, base.map step parameter⟩ step rfl)))

def application (function : (literal (piDisplayed domain body)).sections) (argument : (literal domain).sections) :
    (literal (nativeUnder body (argumentSubstitution domain (sectionDecoder domain argument)))).sections :=
  substituteSection body (argumentSubstitution domain (sectionDecoder domain argument))
    ((lambdaEquiv domain body).symm function)

theorem application_beta (term : (literal body).sections) (argument : (literal domain).sections) :
    application domain body (lambdaEquiv domain body term) argument =
      substituteSection body (argumentSubstitution domain (sectionDecoder domain argument)) term := by
  unfold application
  rw [Equiv.symm_apply_apply]

theorem application_native (function : (literal (piDisplayed domain body)).sections)
    (argument : (literal domain).sections) :
    sectionDecoder _ (application domain body function argument) =
      ContextualSmallFamilyIdentity.reindexSection
        (argumentSubstitution domain (sectionDecoder domain argument)) body
        ((nativeLambda domain body).symm (sectionDecoder (piDisplayed domain body) function)) := by
  rw [application, decoder_substitution]
  apply congrArg
  apply Subtype.ext
  funext point
  rfl

def nativeSigmaFirst (term : (sigmaDisplayed domain body).sections) : domain.sections :=
  ⟨fun point => (term.val point).1, fun {_ _} step => congrArg Sigma.fst (term.property step)⟩

def nativeSigmaSecond (term : (sigmaDisplayed domain body).sections) :
    (nativeUnder body (argumentSubstitution domain (nativeSigmaFirst domain body term))).sections :=
  ⟨fun point => (term.val point).2, by
    intro first second step
    have coordinates := term.property step
    have firstSame : domain.map step (term.val first).1 = (term.val second).1 := congrArg Sigma.fst coordinates
    have target : (flatten domain).obj ⟨second, domain.map step (term.val first).1⟩ =
        (elementMap (argumentSubstitution domain (nativeSigmaFirst domain body term))).obj second :=
      congrArg (fun argument => (⟨second.1, ⟨second.2, argument⟩⟩ : (total domain).Elements)) firstSame
    have arrows := elementsArrow_heq rfl target
      ((flatten domain).map (ContextualSmallFamilyTypeFormers.argumentStep domain step (term.val first).1))
      ((elementMap (argumentSubstitution domain (nativeSigmaFirst domain body term))).map step) HEq.rfl
    exact eq_of_heq ((familyMap_heq body rfl target _ _ arrows
      (term.val first).2 (term.val first).2 HEq.rfl).symm.trans (Sigma.mk.inj_iff.mp coordinates).2)⟩

def nativeSigmaPair (firstTerm : domain.sections)
    (secondTerm : (nativeUnder body (argumentSubstitution domain firstTerm)).sections) :
    (sigmaDisplayed domain body).sections :=
  ⟨fun point => ⟨firstTerm.val point, secondTerm.val point⟩, by
    intro first second step
    apply Sigma.ext (firstTerm.property step)
    have target : (flatten domain).obj ⟨second, domain.map step (firstTerm.val first)⟩ =
        (elementMap (argumentSubstitution domain firstTerm)).obj second :=
      congrArg (fun argument => (⟨second.1, ⟨second.2, argument⟩⟩ : (total domain).Elements)) (firstTerm.property step)
    have arrows := elementsArrow_heq rfl target
      ((flatten domain).map (ContextualSmallFamilyTypeFormers.argumentStep domain step (firstTerm.val first)))
      ((elementMap (argumentSubstitution domain firstTerm)).map step) HEq.rfl
    exact (familyMap_heq body rfl target _ _ arrows
      (secondTerm.val first) (secondTerm.val first) HEq.rfl).trans (heq_of_eq (secondTerm.property step))⟩

def sigmaFirst (term : (literal (sigmaDisplayed domain body)).sections) : (literal domain).sections :=
  (sectionDecoder domain).symm (nativeSigmaFirst domain body (sectionDecoder _ term))

def sigmaSecond (term : (literal (sigmaDisplayed domain body)).sections) :
    (literal (nativeUnder body (argumentSubstitution domain
      (nativeSigmaFirst domain body (sectionDecoder _ term))))).sections :=
  (sectionDecoder _).symm (nativeSigmaSecond domain body (sectionDecoder _ term))

def sigmaPair (firstTerm : (literal domain).sections)
    (secondTerm : (literal (nativeUnder body
      (argumentSubstitution domain (sectionDecoder domain firstTerm)))).sections) :
    (literal (sigmaDisplayed domain body)).sections :=
  (sectionDecoder _).symm (nativeSigmaPair domain body
    (sectionDecoder domain firstTerm) (sectionDecoder _ secondTerm))

theorem sigmaFirst_pair (firstTerm : (literal domain).sections)
    (secondTerm : (literal (nativeUnder body
      (argumentSubstitution domain (sectionDecoder domain firstTerm)))).sections) :
    sigmaFirst domain body (sigmaPair domain body firstTerm secondTerm) = firstTerm := by
  apply Subtype.ext
  funext point
  exact encode_decode domain point (firstTerm.val point)

theorem sigma_eta (term : (literal (sigmaDisplayed domain body)).sections) :
    (sectionDecoder _).symm
      (nativeSigmaPair domain body (nativeSigmaFirst domain body (sectionDecoder _ term))
        (nativeSigmaSecond domain body (sectionDecoder _ term))) = term := by
  apply Subtype.ext
  funext point
  exact encode_decode (sigmaDisplayed domain body) point (term.val point)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyProducts
