import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mettapedia.GSLT.LanguageDef.InteractionCut
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# LanguageDef presentations of kernel interactive theories

Objects of `IGSLT` and `CIGSLT` interpret as kernel `Interactive` and
`KernelCut`. Morphisms of those LanguageDef categories induce behavioral
maps (`IGSLT.semantics`); transporting Type-valued firings along
`mapPattern` is a separate matching-commutation obligation and is not
claimed here.

No new LanguageDef. No Foundation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InteractiveSemantics

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- A firing of the selected interaction rewrite, with the match bindings
retained. Distinct bindings are distinct events even when endpoints agree. -/
structure SelectedRewriteFiring (presentation : InteractivePresentation)
    (source target : presentation.Term) where
  bindings : Bindings
  matched :
    bindings ∈ matchPatternForRule presentation.presentation.language
      presentation.interactionRewrite.1 source.1
  applied :
    applyBindingsForRule presentation.presentation.language
      presentation.interactionRewrite.1 bindings = target.1
  premisesEmpty : presentation.interactionRewrite.1.premises = []

namespace SelectedRewriteFiring

theorem toPrimitive {presentation : InteractivePresentation}
    {source target : presentation.Term}
    (event : SelectedRewriteFiring presentation source target) :
    presentedPrimitiveStep defaultBasePremises presentation source target := by
  refine ⟨1, ?_⟩
  refine StepAt.rule (fuel := 0) presentation.interactionRewrite.2
    event.matched ?_ event.applied
  rw [event.premisesEmpty]
  exact PremisesAt.nil (fuel := 0) event.bindings

theorem toStep {presentation : InteractivePresentation}
    {source target : presentation.Term}
    (event : SelectedRewriteFiring presentation source target) :
    presentation.toGSLT.Step source target :=
  primitiveStep_to_presentedStep event.toPrimitive

end SelectedRewriteFiring

/-- Kernel interactive theory of an iGSLT: one site, events the selected
interaction rewrite's firings. Other authored rewrites remain GSLT steps
but are not this site. Completeness is not claimed. -/
def toInteractive (theory : IGSLT) : Interactive where
  theory := theory.toGSLT
  site :=
    { Site := Unit
      Event := fun _ source target =>
        SelectedRewriteFiring theory.presentation source target
      sound := fun event => event.toStep }

@[simp] theorem toInteractive_erase (theory : IGSLT) :
    (toInteractive theory).erase = theory.toGSLT :=
  rfl

theorem toInteractive_erase_semantics (theory : IGSLT) :
    (toInteractive theory).erase = IGSLT.semantics.obj theory :=
  rfl

/-- Identity iGSLT morphisms act as identity interactive morphisms. -/
def toInteractive_map_id (theory : IGSLT) :
    Interactive.Morphism (toInteractive theory) (toInteractive theory) :=
  Interactive.Morphism.id (toInteractive theory)

theorem toInteractive_map_id_base (theory : IGSLT) :
    (toInteractive_map_id theory).base = IGSLT.semantics.map (IGSLT.Morphism.id theory) := by
  apply GSLT.Morphism.ext
  funext term
  change term = (IGSLT.Morphism.id theory).mapTerm term
  exact (IGSLT.Morphism.mapTerm_id theory term).symm

/-- A CIGSLT supplies an empty-premise interaction rewrite, hence a kernel
cut on the interpreted interactive theory. -/
def toKernelCut (theory : CIGSLT) : KernelCut where
  host := toInteractive theory.theory
  cutSite := ()

theorem toKernelCut_forget (theory : CIGSLT) :
    KernelCut.forget (toKernelCut theory) = toInteractive (CIGSLT.forget.obj theory) :=
  rfl

theorem cigslt_interaction_premises_empty (theory : CIGSLT) :
    theory.theory.presentation.interactionRewrite.1.premises = [] :=
  theory.cut.interactionPremisesEmpty

def rhoInteractive : Interactive :=
  toInteractive rhoIGSLT

theorem rhoInteractive_erase :
    rhoInteractive.erase = rhoIGSLT.toGSLT :=
  rfl

/-- Rho's selected rewrite is COMM with empty premises, so it is a kernel
cut. -/
def rhoKernelCut : KernelCut :=
  toKernelCut
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction.rhoCIGSLT

theorem rhoKernelCut_is_rhoInteractive :
    rhoKernelCut.host = rhoInteractive :=
  rfl

#print axioms toInteractive_erase_semantics
#print axioms toKernelCut_forget
#print axioms cigslt_interaction_premises_empty
#print axioms rhoKernelCut_is_rhoInteractive

end Mettapedia.GSLT.LanguageDef.InteractiveSemantics
