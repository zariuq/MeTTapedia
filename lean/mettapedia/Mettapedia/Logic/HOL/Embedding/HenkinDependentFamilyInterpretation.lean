import Mettapedia.GSLT.Core.ContextualProfileInclusions
import Mettapedia.Logic.HOL.Embedding.ContextualHenkinSemantics
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Admissible contextual Henkin semantics and its dependent-family image

A Henkin model distinguishes an ambient carrier from the elements admitted
to quantification.  The semantic context of a HOL context is therefore the
type of admissible valuations, and the semantic type of a HOL type is the
type of admissible values.  Simultaneous substitutions and terms preserve
these predicates by Henkin closure.

The resulting simple semantics has a canonical image in dependent set-family
semantics: every interpreted HOL type becomes a constant family over its
interpreted context.  Substitution commutes with this route.  The inclusion
is nevertheless proper because dependent semantics also contains genuinely
varying families.

Full domains are stated separately.  Under that additional property the
admissible semantics is equivalent to the ambient set semantics, and the
recursive extensional equality of the HOL model coincides with equality of
admissible values.  None of these results chooses a concrete HOL revision,
a dependent calculus, or a language integration.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Logic.HOL.ContextualStructure

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Admissible values and contexts -/

/-- The elements of a simple HOL type admitted by a Henkin model. -/
abbrev AdmissibleValue (M : HenkinModel.{u, v, w} Base Const)
    (A : Ty Base) :=
  { value : Ty.denote M.Carrier A // M.adm A value }

/-- Valuations whose value at every variable belongs to the corresponding
Henkin domain. -/
abbrev AdmissibleContext (M : HenkinModel.{u, v, w} Base Const)
    (context : Ctx Base) :=
  { valuation : HenkinModel.Valuation M context //
      M.ValuationAdmissible valuation }

/-- Extensionality for admissible contexts reduces to pointwise equality of
the underlying typed valuations. -/
theorem admissibleContext_ext (M : HenkinModel.{u, v, w} Base Const)
    {context : Ctx Base} {left right : AdmissibleContext M context}
    (equal : ∀ {A : Ty Base} (boundVar : Var context A),
      left.1 boundVar = right.1 boundVar) :
    left = right := by
  apply Subtype.ext
  funext A boundVar
  exact equal boundVar

/-! ## Interpretation of substitutions and terms -/

/-- A syntactic simultaneous substitution transports an admissible source
valuation to an admissible target valuation. -/
def interpretSubstitution (M : HenkinModel.{u, v, w} Base Const)
    {source target : Ctx Base}
    (substitution : (holScwf Base Const).Sub source target) :
    AdmissibleContext M source → AdmissibleContext M target :=
  fun valuation =>
    ⟨Soundness.substVal M substitution valuation.1, by
      intro A boundVar
      exact M.denote_admissible valuation.2 (substitution boundVar)⟩

/-- A typed HOL term denotes an admissible value at every admissible
valuation. -/
def interpretTerm (M : HenkinModel.{u, v, w} Base Const)
    {context : Ctx Base} {A : Ty Base}
    (term : Term Const context A) :
    AdmissibleContext M context → AdmissibleValue M A :=
  fun valuation =>
    ⟨M.denote term valuation.1, M.denote_admissible valuation.2 term⟩

/-- Interpretation preserves the identity substitution. -/
theorem interpretSubstitution_id
    (M : HenkinModel.{u, v, w} Base Const)
    {context : Ctx Base} (valuation : AdmissibleContext M context) :
    interpretSubstitution M
        (Subst.id (Base := Base) (Const := Const) (Γ := context)) valuation =
      valuation := by
  apply admissibleContext_ext M
  intro A boundVar
  rfl

/-- Interpretation preserves contextual substitution composition. -/
theorem interpretSubstitution_comp
    (M : HenkinModel.{u, v, w} Base Const)
    {source middle target : Ctx Base}
    (first : (holScwf Base Const).Sub source middle)
    (second : (holScwf Base Const).Sub middle target)
    (valuation : AdmissibleContext M source) :
    interpretSubstitution M
        ((holScwf Base Const).compS second first) valuation =
      interpretSubstitution M second
        (interpretSubstitution M first valuation) := by
  apply admissibleContext_ext M
  intro A boundVar
  exact Soundness.denote_subst M first (second boundVar) valuation.1

/-- Term denotation is natural with respect to simultaneous substitution. -/
theorem interpretTerm_substitution
    (M : HenkinModel.{u, v, w} Base Const)
    {source target : Ctx Base} {A : Ty Base}
    (term : (holScwf Base Const).Tm target A)
    (substitution : (holScwf Base Const).Sub source target)
    (valuation : AdmissibleContext M source) :
    interpretTerm M
        ((holScwf Base Const).tmSub term substitution) valuation =
      interpretTerm M term
        (interpretSubstitution M substitution valuation) := by
  apply Subtype.ext
  exact Soundness.denote_subst M substitution term valuation.1

/-! ## Context comprehension -/

/-- Interpreting context extension gives the product of an admissible
valuation and an admissible value. -/
def contextExtensionEquiv
    (M : HenkinModel.{u, v, w} Base Const)
    (context : Ctx Base) (A : Ty Base) :
    AdmissibleContext M (A :: context) ≃
      (AdmissibleContext M context × AdmissibleValue M A) where
  toFun valuation :=
    (⟨fun {B} boundVar => valuation.1 (.vs boundVar),
      by
        intro B boundVar
        exact valuation.2 (.vs boundVar)⟩,
      ⟨valuation.1 .vz, valuation.2 .vz⟩)
  invFun pair :=
    ⟨M.extend pair.1.1 pair.2.1,
      M.extend_admissible pair.1.2 pair.2.2⟩
  left_inv valuation := by
    apply admissibleContext_ext M
    intro B boundVar
    cases boundVar <;> rfl
  right_inv pair := by
    apply Prod.ext
    · apply admissibleContext_ext M
      intro B boundVar
      rfl
    · apply Subtype.ext
      rfl

/-- The same comprehension comparison, now written as the dependent sum of
the constant family selected by the HOL type. -/
def productConstantSigmaEquiv (Context Value : Type*) :
    (Context × Value) ≃ (Σ _ : Context, Value) where
  toFun pair := ⟨pair.1, pair.2⟩
  invFun pair := (pair.1, pair.2)
  left_inv pair := by
    cases pair
    rfl
  right_inv pair := by
    cases pair
    rfl

/-- The same comprehension comparison, now written as the dependent sum of
the constant family selected by the HOL type. -/
def dependentContextExtensionEquiv
    (M : HenkinModel.{u, v, w} Base Const)
    (context : Ctx Base) (A : Ty Base) :
    AdmissibleContext M (A :: context) ≃
      (Σ _ : AdmissibleContext M context, AdmissibleValue M A) :=
  (contextExtensionEquiv M context A).trans
    (productConstantSigmaEquiv
      (AdmissibleContext M context) (AdmissibleValue M A))

/-! ## Application and the selected extensional equality -/

/-- Admissible functions take admissible arguments to admissible results. -/
def applyAdmissible (M : HenkinModel.{u, v, w} Base Const)
    {domain codomain : Ty Base} :
    AdmissibleValue M (domain ⇒ codomain) →
      AdmissibleValue M domain → AdmissibleValue M codomain :=
  fun function argument =>
    ⟨function.1 argument.1, M.app_mem function.2 argument.2⟩

/-- Term application is interpreted by admissible semantic application. -/
theorem interpretTerm_application
    (M : HenkinModel.{u, v, w} Base Const)
    {context : Ctx Base} {domain codomain : Ty Base}
    (function : Term Const context (domain ⇒ codomain))
    (argument : Term Const context domain)
    (valuation : AdmissibleContext M context) :
    interpretTerm M (.app function argument) valuation =
      applyAdmissible M (interpretTerm M function valuation)
        (interpretTerm M argument valuation) :=
  rfl

/-- Recursive Henkin equality restricted to admissible semantic values. -/
def ExtensionallyEqual (M : HenkinModel.{u, v, w} Base Const)
    {A : Ty Base} (left right : AdmissibleValue M A) : Prop :=
  M.Eqv A left.1 right.1

/-- The separately named function-congruence property makes application
respect extensional equality in both arguments. -/
theorem applyAdmissible_respects_extensionalEquality
    (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {domain codomain : Ty Base}
    {leftFunction rightFunction : AdmissibleValue M (domain ⇒ codomain)}
    {leftArgument rightArgument : AdmissibleValue M domain}
    (functionEqual : ExtensionallyEqual M leftFunction rightFunction)
    (argumentEqual : ExtensionallyEqual M leftArgument rightArgument) :
    ExtensionallyEqual M
      (applyAdmissible M leftFunction leftArgument)
      (applyAdmissible M rightFunction rightArgument) := by
  exact M.eqv_trans
    (M.eqv_arr_apply functionEqual leftArgument.2)
    (respects rightFunction.2 leftArgument.2 rightArgument.2 argumentEqual)

/-! ## The canonical dependent-family image -/

/-- The simple semantic type of a HOL type at a semantic context. -/
def simpleSemanticType
    (M : HenkinModel.{u, v, w} Base Const)
    (_context : Ctx Base) (A : Ty Base) : Type (max (u + 1) w) :=
  AdmissibleValue M A

/-- The dependent interpretation is the constant family selected by the
simple semantic type. -/
def dependentSemanticType
    (M : HenkinModel.{u, v, w} Base Const)
    (context : Ctx Base) (A : Ty Base) :
    AdmissibleContext M context → Type (max (u + 1) w) :=
  constantFamily (AdmissibleValue M A)

/-- HOL term denotation is a section of its constant dependent family. -/
def dependentSemanticTerm
    (M : HenkinModel.{u, v, w} Base Const)
    {context : Ctx Base} {A : Ty Base}
    (term : Term Const context A) :
    ∀ valuation : AdmissibleContext M context,
      dependentSemanticType M context A valuation :=
  interpretTerm M term

/-- The dependent type is exactly the object obtained from the canonical
simple-to-dependent fibre functor. -/
theorem dependentSemanticType_is_simpleToDependent
    (M : HenkinModel.{u, v, w} Base Const)
    (context : Ctx Base) (A : Ty Base) :
    ((simpleToDependentTypeFunctor (AdmissibleContext M context)).obj
      (⟨simpleSemanticType M context A⟩ :
        TypeOver SimpleFamiliesCwf (AdmissibleContext M context))).val =
      dependentSemanticType M context A :=
  rfl

/-- Substitution also commutes after passage to the dependent-family image. -/
theorem dependentSemanticTerm_substitution
    (M : HenkinModel.{u, v, w} Base Const)
    {source target : Ctx Base} {A : Ty Base}
    (term : Term Const target A)
    (substitution : (holScwf Base Const).Sub source target) :
    familiesCwf.tmSub (dependentSemanticTerm M term)
        (interpretSubstitution M substitution) =
      dependentSemanticTerm M
        ((holScwf Base Const).tmSub term substitution) := by
  funext valuation
  exact (interpretTerm_substitution M term substitution valuation).symm

/-! ## Full-domain comparison and strict dependent boundary -/

/-- With full Henkin domains, admissible values are equivalent to the ambient
semantic carrier. -/
def fullDomainsValueEquiv
    (M : HenkinModel.{u, v, w} Base Const) (full : M.FullDomains)
    (A : Ty Base) :
    AdmissibleValue M A ≃ Ty.denote M.Carrier A where
  toFun := Subtype.val
  invFun value := ⟨value, full A value⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- With full domains, admissible contexts are equivalent to all ambient
valuations. -/
def fullDomainsContextEquiv
    (M : HenkinModel.{u, v, w} Base Const) (full : M.FullDomains)
    (context : Ctx Base) :
    AdmissibleContext M context ≃ HenkinModel.Valuation M context where
  toFun := Subtype.val
  invFun valuation :=
    ⟨valuation, by
      intro A boundVar
      exact full A (valuation boundVar)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Under full domains, recursive Henkin equality is precisely equality of
admissible semantic values. -/
theorem extensionallyEqual_iff_eq_of_fullDomains
    (M : HenkinModel.{u, v, w} Base Const) (full : M.FullDomains)
    {A : Ty Base} (left right : AdmissibleValue M A) :
    ExtensionallyEqual M left right ↔ left = right := by
  constructor
  · intro equal
    apply Subtype.ext
    exact M.eq_of_eqv_of_fullDomains full equal
  · intro equal
    subst right
    exact M.eqv_refl left.2

/-- Negative control: the dependent families model remains strictly larger
than every constant-family HOL image. -/
theorem varyingDependentFamily_not_in_simple_image :
    ¬ ∃ A : TypeOver (SimpleFamiliesCwf.{0}) Bool,
      simpleToDependentPseudoMorphism.mapTypeObject A =
        (⟨varyingBoolFamily⟩ : TypeOver (familiesCwf.{0}) Bool) :=
  varyingBoolFamily_not_in_pseudoMorphism_image

/-- The main commuting comparison and its non-collapse boundary. -/
theorem henkin_simple_dependent_comparison
    (M : HenkinModel.{u, v, w} Base Const) :
    (∀ {source target : Ctx Base} {A : Ty Base}
        (term : Term Const target A)
        (substitution : (holScwf Base Const).Sub source target),
      familiesCwf.tmSub (dependentSemanticTerm M term)
          (interpretSubstitution M substitution) =
        dependentSemanticTerm M
          ((holScwf Base Const).tmSub term substitution)) ∧
      (¬ ∃ A : TypeOver (SimpleFamiliesCwf.{0}) Bool,
        simpleToDependentPseudoMorphism.mapTypeObject A =
          (⟨varyingBoolFamily⟩ : TypeOver (familiesCwf.{0}) Bool)) :=
  ⟨fun term substitution =>
      dependentSemanticTerm_substitution M term substitution,
    varyingDependentFamily_not_in_simple_image⟩

#print axioms interpretSubstitution
#print axioms interpretTerm
#print axioms interpretSubstitution_comp
#print axioms interpretTerm_substitution
#print axioms contextExtensionEquiv
#print axioms dependentContextExtensionEquiv
#print axioms applyAdmissible_respects_extensionalEquality
#print axioms dependentSemanticType_is_simpleToDependent
#print axioms dependentSemanticTerm_substitution
#print axioms fullDomainsValueEquiv
#print axioms extensionallyEqual_iff_eq_of_fullDomains
#print axioms varyingDependentFamily_not_in_simple_image
#print axioms henkin_simple_dependent_comparison

end Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation
