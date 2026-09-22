import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory

/-!
# A criterion obstructing exponentials in certificate context categories

The existing category has finite products by concatenating premise contexts.
That does not imply it has function objects. If a calculus has a judgment
which cannot be proved from the empty premise context, the proposed
exponential of that judgment by itself cannot be represented: an empty
context gives a closed identity map and forces the representing context to
be empty, while a singleton context has two different projections.

The obstruction rules out even objectwise equivalences of hom-types, a
weaker demand than a natural exponential adjunction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private def singletonContext (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) : ClassifyingContext definition := ⟨[goal]⟩

private theorem empty_source_hom_target_empty
    (definition : ValidatedCalculusLanguageDef)
    (noClosed : ∀ goal : Pattern,
      ¬ Nonempty (OpenDerivation definition [] goal))
    (target : ClassifyingContext definition)
    (morphism : ClassifyingContext.emptyContext definition ⟶ target) :
    target.judgments = [] := by
  cases target with
  | mk goals =>
      cases goals with
      | nil => rfl
      | cons goal goals =>
          cases morphism with
          | cons head _ => exact (noClosed goal ⟨head⟩).elim

private theorem hom_to_empty_unique
    (definition : ValidatedCalculusLanguageDef)
    (source target : ClassifyingContext definition)
    (empty : target.judgments = [])
    (first second : source ⟶ target) : first = second := by
  cases target with
  | mk judgments =>
      change judgments = [] at empty
      subst judgments
      cases first
      cases second
      rfl

private def firstProjection
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    ClassifyingContext.concat (singletonContext definition goal)
      (singletonContext definition goal) ⟶
        singletonContext definition goal :=
  .cons (OpenDerivation.assumption (definition := definition)
    (context := [goal, goal]) (0 : Fin 2)) .nil

private def secondProjection
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    ClassifyingContext.concat (singletonContext definition goal)
      (singletonContext definition goal) ⟶
        singletonContext definition goal :=
  .cons (OpenDerivation.assumption (definition := definition)
    (context := [goal, goal]) (1 : Fin 2)) .nil

private theorem projections_distinct
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    firstProjection definition goal ≠ secondProjection definition goal := by
  intro equal
  have heads := congrArg
    (fun proofs : OpenDerivationList definition [goal, goal] [goal] =>
      proofs.get (0 : Fin 1)) equal
  change (OpenDerivation.assumption (definition := definition)
    (context := [goal, goal]) (0 : Fin 2)) =
    OpenDerivation.assumption (definition := definition)
      (context := [goal, goal]) (1 : Fin 2) at heads
  exact ClassifyingContext.duplicate_assumptions_distinct definition goal heads

/-- A judgment with no closed certificate has no self-exponential in the
finite-product certificate context category, even without asking the
candidate hom equivalences to be natural. -/
theorem no_self_exponential_of_no_closed
    (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern)
    (noClosed : ∀ candidate : Pattern,
      ¬ Nonempty (OpenDerivation definition [] candidate)) :
    ¬ ∃ exponent : ClassifyingContext definition,
      ∀ context : ClassifyingContext definition,
        Nonempty ((ClassifyingContext.concat context
          (singletonContext definition goal) ⟶
            singletonContext definition goal) ≃
          (context ⟶ exponent)) := by
  rintro ⟨exponent, homEquiv⟩
  let empty := ClassifyingContext.emptyContext definition
  let one := singletonContext definition goal
  have identityAtEmpty : ClassifyingContext.concat empty one ⟶ one :=
    .cons (OpenDerivation.assumption (definition := definition)
      (context := [goal]) (0 : Fin 1)) .nil
  obtain ⟨emptyEquiv⟩ := homEquiv empty
  have emptyToExponent : empty ⟶ exponent :=
    emptyEquiv identityAtEmpty
  have exponentEmpty : exponent.judgments = [] :=
    empty_source_hom_target_empty definition noClosed exponent
      emptyToExponent
  obtain ⟨oneEquiv⟩ := homEquiv one
  have imagesEqual :
      oneEquiv (firstProjection definition goal) =
        oneEquiv (secondProjection definition goal) :=
    hom_to_empty_unique definition one exponent exponentEmpty _ _
  exact projections_distinct definition goal
    (oneEquiv.injective imagesEqual)

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.no_self_exponential_of_no_closed

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.ExponentialCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private def goal : Pattern := .apply "ExponentialCanary-A" []

private def presentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend (LanguageDef.empty "no-rules-exponential-canary")
    { judgments := [{ head := "ExponentialCanary-A", arity := 0 }]
      rules := [] }

private theorem presentation_valid : presentation.isValid = true := by
  decide +kernel

private def validated : ValidatedCalculusLanguageDef :=
  ⟨presentation, presentation_valid⟩

/-- A rule-free calculus has no closed proof of any goal, even though its
nonempty contexts have assumption proofs. -/
private theorem no_closed_proofs (candidate : Pattern) :
    ¬ Nonempty (OpenDerivation validated [] candidate) := by
  rintro ⟨proof⟩
  cases proof with
  | assumption index => exact index.elim0
  | byRule ruleInstance application _ =>
      cases application with
      | intro rule lookup _ _ _ _ =>
          simp [validated, presentation,
            CalculusLanguageDef.lookupRule?] at lookup

/-- In a concrete validated authored calculus, the existing finite-product
classifying context category lacks even the self-exponential of its one
declared judgment. -/
theorem no_self_exponential :
    ¬ ∃ exponent : ClassifyingContext validated,
      ∀ context : ClassifyingContext validated,
        Nonempty ((ClassifyingContext.concat context
          (⟨[goal]⟩ : ClassifyingContext validated) ⟶
            (⟨[goal]⟩ : ClassifyingContext validated)) ≃
          (context ⟶ exponent)) :=
  no_self_exponential_of_no_closed validated goal no_closed_proofs

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.ExponentialCanary

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ExponentialCanary.no_self_exponential
