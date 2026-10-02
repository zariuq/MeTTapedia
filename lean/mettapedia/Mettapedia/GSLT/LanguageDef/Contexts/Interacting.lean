import Mettapedia.GSLT.LanguageDef.Contexts.Presented

/-!
# The interacting sort among the interfaces

The behavioural theory of an interactive presentation lives on the closed
terms of its interacting sort.  Those are the terms of one interface of the
presentation's context theory, with the same static equivalence and the same
reduction.  So the bisimilarity of the behavioural theory is what the probe
that sees only reduction sees at that interface, and bisimilarity over all
context-labelled transitions refines it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

variable (base : BasePremiseEvaluator) (presentation : InteractivePresentation)

/-- The interface of the closed terms of the interacting sort. -/
abbrev interactingInterface : Interface :=
  closedInterface (presentation := presentation.presentation) presentation.interactingLangSort

variable {presentation}

/-- A closed term of the interacting sort, as a term of its interface. -/
abbrev ofInteracting (term : presentation.Term) :
    Term presentation.presentation.language (interactingInterface presentation) :=
  ofClosed term

/-- The static equivalence of the interacting interface is the static
equivalence of the behavioural theory. -/
theorem termSetoid_ofInteracting_iff (left right : presentation.Term) :
    (termSetoid base presentation.presentation.language (interactingInterface presentation)).r
        (ofInteracting left) (ofInteracting right) ↔
      (presentedEquationSetoid base presentation).r left right := by
  constructor
  · intro equivalent
    have transported : ∀ first second :
        Term presentation.presentation.language (interactingInterface presentation),
        (termSetoid base presentation.presentation.language
          (interactingInterface presentation)).r first second →
        (presentedEquationSetoid base presentation).r (toClosed first) (toClosed second) := by
      intro first second related
      induction related with
      | rel first second step => exact Relation.EqvGen.rel _ _ step
      | refl term => exact Relation.EqvGen.refl _
      | symm first second _ recurse => exact Relation.EqvGen.symm _ _ recurse
      | trans first middle second _ _ firstStep secondStep =>
          exact Relation.EqvGen.trans _ _ _ firstStep secondStep
    exact transported _ _ equivalent
  · intro equivalent
    induction equivalent with
    | rel first second step => exact Relation.EqvGen.rel _ _ step
    | refl term => exact Relation.EqvGen.refl _
    | symm first second _ recurse => exact Relation.EqvGen.symm _ _ recurse
    | trans first middle second _ _ firstStep secondStep =>
        exact Relation.EqvGen.trans _ _ _ firstStep secondStep

/-- The reduction of the interacting interface is the reduction of the
behavioural theory. -/
theorem termStep_ofInteracting_iff (source target : presentation.Term) :
    TermStep base presentation.presentation.language (ofInteracting source)
        (ofInteracting target) ↔
      presentedStep base presentation source target := by
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨toClosed redex, toClosed contractum,
      (termSetoid_ofInteracting_iff base source (toClosed redex)).mp before, step,
      (termSetoid_ofInteracting_iff base (toClosed contractum) target).mp after⟩
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨ofInteracting redex, ofInteracting contractum,
      (termSetoid_ofInteracting_iff base source redex).mpr before, step,
      (termSetoid_ofInteracting_iff base contractum target).mpr after⟩

/-- **The behavioural theory is the context theory at the interacting
interface**: their bisimilarities agree. -/
theorem gslt_bisimilar_iff (left right : presentation.Term) :
    ((contextTheory base presentation.presentation).gslt
        (interactingInterface presentation)).Bisimilar (ofInteracting left)
        (ofInteracting right) ↔
      (presentedGSLT base presentation).Bisimilar left right := by
  constructor
  · intro bisimilar
    have transported := GSLT.bisimilar_map_of_step_iff
      (source := (contextTheory base presentation.presentation).gslt
        (interactingInterface presentation))
      (target := presentedGSLT base presentation)
      (closedEquiv (presentation := presentation.presentation)
        presentation.interactingLangSort).symm
      (fun first second =>
        (termStep_ofInteracting_iff base (toClosed first) (toClosed second)))
      bisimilar
    exact transported
  · intro bisimilar
    exact GSLT.bisimilar_map_of_step_iff
      (source := presentedGSLT base presentation)
      (target := (contextTheory base presentation.presentation).gslt
        (interactingInterface presentation))
      (closedEquiv (presentation := presentation.presentation)
        presentation.interactingLangSort)
      (fun first second => (termStep_ofInteracting_iff base first second).symm)
      bisimilar

/-- **Bisimilarity over all context-labelled transitions refines the
bisimilarity of the behavioural theory.** -/
theorem presentedBisimilar_of_fullProbe {left right : presentation.Term}
    (bisimilar : (contextTheory base presentation.presentation).fullProbe.Bisimilar
      (index := interactingInterface presentation) (ofInteracting left) (ofInteracting right)) :
    (presentedGSLT base presentation).Bisimilar left right :=
  (gslt_bisimilar_iff base left right).mp
    ((contextTheory base presentation.presentation).bisimilar_toGSLT bisimilar)

/-- The probe that sees only reduction sees the bisimilarity of the
behavioural theory. -/
theorem reductionProbe_bisimilar_iff_presented (left right : presentation.Term) :
    (contextTheory base presentation.presentation).reductionProbe.Bisimilar
        (index := interactingInterface presentation) (ofInteracting left)
        (ofInteracting right) ↔
      (presentedGSLT base presentation).Bisimilar left right :=
  ((contextTheory base presentation.presentation).reductionProbe_bisimilar_iff).trans
    (gslt_bisimilar_iff base left right)

end Mettapedia.GSLT.LanguageDef.Contexts
