import Mettapedia.Computability.ReflectiveCode
import Mettapedia.TypeTheory.ContextualCode

/-!
# Contextual code as an equality-level reflective interface

At one selected modal fibre, contextual quotation and splicing have the same
raw shape as a reflective-code interface: bodies are quoted to code and code
is spliced back to bodies.  This module identifies the law level precisely.

The contextual beta and eta structures imply literal equality laws at every
selected fibre.  Consequently they are stronger than a merely operational
execution witness or a law holding only after quotienting.  Conversely, an
operational splice witness recovers the equality-level beta law only when its
step discipline reflects endpoint equality.

This comparison does not identify contextual code with process-calculus
reflection.  In particular, it does not manufacture free execution from a
quote/drop equation, erase proof-relevant execution receipts, or select a
modal type theory.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCodeReflection

open Mettapedia.Computability.ReflectiveCode
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ContextualCode
open Mettapedia.TypeTheory.SelectedModalIntroduction

universe uStep

variable {modes : ModeTheory} {cwf : ModalCwF modes}
variable {laws : ModalCwFLaws modes cwf}
variable {selection : WideSubtheory modes}
variable {quotation : SelectedQuotationTermStructure modes cwf laws selection}
variable {splicing : SelectedSpliceTermStructure modes cwf laws selection}

/-- At a selected modal fibre, bodies are the process-like carrier and modal
terms are the code/name-like carrier of the generic reflection interface. -/
def selectedFibreInterface
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    Interface
      (cwf.Tm (cwf.lock modality context) type)
      (cwf.Tm context (cwf.boxTy modality type)) where
  quote := quotation.introduce modality admitted
  drop := splicing.splice modality admitted

/-- Contextual quote-then-splice beta is literal beta, not merely a reduction
or quotient equation, at each selected fibre. -/
theorem staticBeta_at_selectedFibre
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    (selectedFibreInterface (laws := laws) (quotation := quotation)
      (splicing := splicing) modality admitted
      (context := context) (type := type)).StaticBeta := by
  intro body
  exact beta.splice_quote modality admitted body

/-- Contextual splice-then-quote eta is literal eta at each selected fibre. -/
theorem staticEta_at_selectedFibre
    (eta : SelectedQuoteSpliceEta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    (selectedFibreInterface (laws := laws) (quotation := quotation)
      (splicing := splicing) modality admitted
      (context := context) (type := type)).StaticEta := by
  intro code
  exact eta.quote_splice modality admitted code

/-- Equality-level contextual beta can be viewed operationally for any
reflexive, proof-relevant execution discipline.  The execution witness may
still retain routes, occurrences, schedules, or costs. -/
def operationalBeta_at_selectedFibre
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)}
    {Step : cwf.Tm (cwf.lock modality context) type ->
      cwf.Tm (cwf.lock modality context) type -> Type uStep}
    (stepRefl : forall body, Step body body) :
    (selectedFibreInterface (laws := laws) (quotation := quotation)
      (splicing := splicing) modality admitted
      (context := context) (type := type)).OperationalBeta Step :=
  Interface.operationalBeta_of_staticBeta
    (selectedFibreInterface (laws := laws) (quotation := quotation)
      (splicing := splicing) modality admitted
      (context := context) (type := type))
    (staticBeta_at_selectedFibre (laws := laws) beta modality admitted) stepRefl

/-- An operational splice law recovers literal beta at the selected fibre
only under the explicit endpoint-equality reflection hypothesis. -/
theorem staticBeta_of_operational_at_selectedFibre
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)}
    {Step : cwf.Tm (cwf.lock modality context) type ->
      cwf.Tm (cwf.lock modality context) type -> Type uStep}
    (execution :
      (selectedFibreInterface (laws := laws) (quotation := quotation)
        (splicing := splicing) modality admitted
        (context := context) (type := type)).OperationalBeta Step)
    (reflectsEquality : Interface.StepReflectsEquality Step) :
    (selectedFibreInterface (laws := laws) (quotation := quotation)
      (splicing := splicing) modality admitted
      (context := context) (type := type)).StaticBeta :=
  Interface.staticBeta_of_operationalBeta
    (selectedFibreInterface (laws := laws) (quotation := quotation)
      (splicing := splicing) modality admitted
      (context := context) (type := type))
    execution reflectsEquality

/-- Beta and eta therefore give an exact body/code equivalence at a selected
fibre.  This is a local capability result; it does not assert that all modes,
modalities, or operational reflections satisfy these laws. -/
def exactBodyCodeEquiv_at_selectedFibre
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    (eta : SelectedQuoteSpliceEta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    cwf.Tm (cwf.lock modality context) type ≃
      cwf.Tm context (cwf.boxTy modality type) :=
  Interface.exactEquiv
    (selectedFibreInterface (laws := laws) (quotation := quotation)
      (splicing := splicing) modality admitted
      (context := context) (type := type))
    (staticBeta_at_selectedFibre (laws := laws) beta modality admitted)
    (staticEta_at_selectedFibre (laws := laws) eta modality admitted)

#print axioms staticBeta_at_selectedFibre
#print axioms staticEta_at_selectedFibre
#print axioms operationalBeta_at_selectedFibre
#print axioms staticBeta_of_operational_at_selectedFibre
#print axioms exactBodyCodeEquiv_at_selectedFibre

end Mettapedia.TypeTheory.ContextualCodeReflection
