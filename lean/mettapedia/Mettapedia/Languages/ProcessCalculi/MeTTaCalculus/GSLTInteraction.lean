import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

/-!
# MeTTa-calculus as an interactive GSLT

The MeTTa-calculus already authors its `COMM` relation as a rewrite over a
bare parallel hash-bag.  This module selects that exact sort, constructor, and
rewrite through the generic interactive-GSLT interface.  It introduces no
second operational relation.

The selected contact data form a structural boundary; `mettaCalcGSLT` below
derives the actual behavioral theory using the declared premise environment.
Persistent space observation and linear contact remain distinct access modes,
as proved in `SpaceChannelBoundary` and `SpaceInteraction`.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.GSLTInteraction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- The exact validated five-field MeTTa-calculus definition. -/
def mettaCalcValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨mettaCalc, mettaCalc_validate_eq_nil⟩

/-- The authored process sort. -/
def mettaCalcProcessSort : DeclaredSort mettaCalcValidatedLanguageDef :=
  ⟨mettaCalc.types[0], by
    change List.Mem mettaCalc.types[0] mettaCalc.types
    exact List.getElem_mem (by simp [mettaCalc])⟩

/-- The authored bare hash-bag constructor used by `pPar`. -/
def mettaCalcParallelConstructor :
    DeclaredConstructor mettaCalcValidatedLanguageDef :=
  ⟨mettaCalc.terms[1], by
    change List.Mem mettaCalc.terms[1] mettaCalc.terms
    exact List.getElem_mem (by simp [mettaCalc])⟩

/-- The authored symmetric communication rewrite. -/
def mettaCalcCommRewrite : DeclaredRewrite mettaCalcValidatedLanguageDef :=
  ⟨mettaCalc.rewrites[0], by
    change List.Mem mettaCalc.rewrites[0] mettaCalc.rewrites
    exact List.getElem_mem (by simp [mettaCalc])⟩

/-- The MeTTa-calculus interaction selection, retaining the sole authored
language definition verbatim. -/
def mettaCalcInteractivePresentation : InteractivePresentation where
  presentation := mettaCalcValidatedLanguageDef
  interactingSort := mettaCalcProcessSort
  contactConstructor := mettaCalcParallelConstructor
  interactionRewrite := mettaCalcCommRewrite
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, mettaCalcCommRewrite, mettaCalc, commSymRule]

/-- The behavioral GSLT induced by the exact authored MeTTa-calculus and its
declared premise environment.  This is the actual `(T,E,R)` object; the
interactive presentation above only selects its contact interface. -/
def mettaCalcGSLT : GSLT :=
  presentedGSLT (engineBasePremises mettaCalcRelEnv)
    mettaCalcInteractivePresentation

/-- Every step emitted by the current bounded executable is a genuine step
of the unbounded declarative MeTTa-calculus GSLT.  The converse is
intentionally not asserted: the executable contextual depth is finite. -/
theorem executable_step_to_mettaCalcGSLT
    {source target : mettaCalcInteractivePresentation.Term}
    (executes : target.1 ∈ step source.1) :
    mettaCalcGSLT.Step source target := by
  apply primitiveStep_to_presentedStep
  change Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
    (engineBasePremises mettaCalcRelEnv) mettaCalc source.1 target.1
  refine ⟨executableContextFuel, ?_⟩
  apply mem_rewriteAt_iff_stepAt.mp
  simpa [step, reductsUsing] using executes

theorem mettaCalc_contact_constructor_label :
    mettaCalcInteractivePresentation.contactConstructor.1.label = "MPar" := by
  simp [mettaCalcInteractivePresentation, mettaCalcParallelConstructor,
    mettaCalc]

theorem mettaCalc_interaction_rewrite_name :
    mettaCalcInteractivePresentation.interactionRewrite.1.name = "CommSym" := by
  simp [mettaCalcInteractivePresentation, mettaCalcCommRewrite, mettaCalc,
    commSymRule]

/-- Positive control: symmetric `COMM` is selected as collection contact. -/
theorem mettaCalc_comm_interaction_headed :
    InteractionHeaded
      mettaCalcInteractivePresentation.contactRepresentation
      mettaCalcInteractivePresentation.contactConstructor.1
      mettaCalcInteractivePresentation.interactionRewrite.1.left :=
  mettaCalcInteractivePresentation.interactionHeaded

/-- Negative control: procedural reflection is not itself a contact source. -/
theorem mettaCalc_reflection_not_interaction_headed (name process : Pattern) :
    ¬ InteractionHeaded
      mettaCalcInteractivePresentation.contactRepresentation
      mettaCalcInteractivePresentation.contactConstructor.1
      (pReflect name process) := by
  simp [mettaCalcInteractivePresentation, pReflect, InteractionHeaded]

/-! ## Exact commonality and exact difference with rho -/

/-- MeTTa-calculus and rho select the same bare hash-bag representation for
binary contact.  This is a shared interaction shape, not an identification of
their rewrite rules. -/
theorem mettaCalc_rho_contact_representation_agrees :
    mettaCalcInteractivePresentation.contactRepresentation =
      rhoInteractivePresentation.contactRepresentation := by
  rfl

/-- The selected interactions remain different authored rules: symmetric
unification contact is not rho's asymmetric input/output communication. -/
theorem mettaCalc_rho_interaction_rewrites_distinct :
    mettaCalcInteractivePresentation.interactionRewrite.1.name ≠
      rhoInteractivePresentation.interactionRewrite.1.name := by
  rw [mettaCalc_interaction_rewrite_name]
  simp [rhoInteractivePresentation, rhoCalc, rhoCommRewrite]

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.GSLTInteraction
