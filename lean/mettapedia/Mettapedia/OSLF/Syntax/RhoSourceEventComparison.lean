import Mettapedia.OSLF.Syntax.RhoSourceEquationModel
import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents
import Mettapedia.OSLF.Syntax.RuleListEventEmbedding

/-!
# Chapter 7 source rho events over the full equation model

The COMM-only and COMM-plus-Drop profiles share the complete source equation
quotient. The latter extends the former's located event presheaf, preserving
rule indices, locations, and both quotient-valued endpoints. Drop creates a
new edge over those same states. This is stronger than merely comparing the
two proposition-valued step relations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSourceEventComparison

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.RuleListEventEmbedding

/-- The concrete Comm-to-Comm-plus-Drop extension is an instance of the
general rule-occurrence embedding, with the complete source equations fixed. -/
def sourceCommRuleEmbedding : Embedding
    rhoSourceComm.toUnpositioned.rules
    rhoSourceWithDrop.toUnpositioned.rules where
  index := fun _ => ⟨0, by decide⟩
  index_injective := by
    intro i j _
    fin_cases i
    fin_cases j
    rfl
  rule_eq := by
    intro i
    fin_cases i
    rfl

/-- Embed a located COMM event into the combined source presentation without
erasing its selected structural occurrence or root assignment. -/
def embedCommEvent {Γ : Ctx sig} {sort : Srt}
    (event : PresentationInstance rhoSourceComm.toUnpositioned Γ sort) :
    PresentationInstance rhoSourceWithDrop.toUnpositioned Γ sort := by
  rcases event with ⟨i, firing⟩
  have bound : i.val < 1 := by
    simpa [rhoSourceComm, Presentation.toUnpositioned] using i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    change i.val = 0
    omega)
  subst i
  exact ⟨⟨0, by decide⟩, firing⟩

/-- The previously constructed rho inclusion is exactly the instance of the
general occurrence transport, including its retained firing location. -/
theorem sourceCommEmbedding_agrees {Γ : Ctx sig} {sort : Srt}
    (event : PresentationInstance rhoSourceComm.toUnpositioned Γ sort) :
    embedEvent (E := rhoSourceE) sourceCommRuleEmbedding event =
      embedCommEvent event := by
  rcases event with ⟨i, firing⟩
  fin_cases i
  rfl

/-- The general rule-extension theorem recovers preservation of all closed
communication steps, including source equation closure on both endpoints. -/
theorem source_comm_step_via_general_embedding {sort : Srt}
    {source target : Term sig [] sort}
    (step : rhoSourceComm.StepModE source target) :
    rhoSourceWithDrop.StepModE source target := by
  apply (rhoSourceWithDrop.stepModE_iff_toUnpositioned).mpr
  exact stepModE_of_embedding sourceCommRuleEmbedding rhoSourceE
    ((rhoSourceComm.stepModE_iff_toUnpositioned).mp step)

theorem embedCommEvent_source {Γ : Ctx sig} {sort : Srt}
    (event : PresentationInstance rhoSourceComm.toUnpositioned Γ sort) :
    (embedCommEvent event).source = event.source := by
  rcases event with ⟨i, firing⟩
  have bound : i.val < 1 := by
    simpa [rhoSourceComm, Presentation.toUnpositioned] using i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    change i.val = 0
    omega)
  subst i
  rfl

theorem embedCommEvent_target {Γ : Ctx sig} {sort : Srt}
    (event : PresentationInstance rhoSourceComm.toUnpositioned Γ sort) :
    (embedCommEvent event).target = event.target := by
  rcases event with ⟨i, firing⟩
  have bound : i.val < 1 := by
    simpa [rhoSourceComm, Presentation.toUnpositioned] using i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    change i.val = 0
    omega)
  subst i
  rfl

/-- The event inclusion is natural under every substitution of the ambient
context, including those passing beneath input binders. -/
theorem embedCommEvent_map {Γ Δ : Ctx sig} {sort : Srt}
    (sigma : Sub sig Γ Δ)
    (event : PresentationInstance rhoSourceComm.toUnpositioned Γ sort) :
    embedCommEvent (PresentationInstance.map sigma event) =
      PresentationInstance.map sigma (embedCommEvent event) := by
  rcases event with ⟨i, firing⟩
  have bound : i.val < 1 := by
    simpa [rhoSourceComm, Presentation.toUnpositioned] using i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    change i.val = 0
    omega)
  subst i
  rfl

/-- A natural transformation of located operational event presheaves. -/
def eventEmbedding (sort : Srt) :
    presentationEventPresheaf rhoSourceComm.toUnpositioned sort ⟶
      presentationEventPresheaf rhoSourceWithDrop.toUnpositioned sort where
  app X := TypeCat.ofHom embedCommEvent
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact embedCommEvent_map f.unop event

/-- The source endpoint of an embedded event is unchanged even after passing
to the source equation classes. -/
theorem eventEmbedding_source (sort : Srt) :
    eventEmbedding sort ≫
        presentationSourceNatural rhoSourceWithDrop.toUnpositioned sort =
      presentationSourceNatural rhoSourceComm.toUnpositioned sort := by
  ext X event
  exact congrArg (Quotient.mk _) (embedCommEvent_source event)

/-- The same comparison holds for target equation classes. -/
theorem eventEmbedding_target (sort : Srt) :
    eventEmbedding sort ≫
        presentationTargetNatural rhoSourceWithDrop.toUnpositioned sort =
      presentationTargetNatural rhoSourceComm.toUnpositioned sort := by
  ext X event
  exact congrArg (Quotient.mk _) (embedCommEvent_target event)

/-- The general rule-catalogue functor sends the actual rho inclusion to
the previously checked natural event embedding. -/
theorem sourceCommGraphMap_agrees (sort : Srt) :
    ((eventGraphFunctor rhoSourceE sort).map sourceCommRuleEmbedding).edgeMap =
      eventEmbedding sort := by
  ext X event
  exact sourceCommEmbedding_agrees event

/-- The complete source equation model admits an actual retained Drop event
between the classes of `*(@0)` and `0`. -/
theorem source_drop_has_class_event :
    ∃ event : PresentationInstance rhoSourceWithDrop.toUnpositioned [] Srt.pr,
      (Quotient.mk _ event.source : TermQ rhoSourceE [] Srt.pr) =
        Quotient.mk _ dropChan ∧
      (Quotient.mk _ event.target : TermQ rhoSourceE [] Srt.pr) =
        Quotient.mk _ nilP := by
  exact (authored_class_endpoints_iff_stepModE
    rhoSourceWithDrop.toUnpositioned Srt.pr dropChan nilP).mpr
      ((rhoSourceWithDrop.stepModE_iff_toUnpositioned).mp source_drop_nil)

/-- The same equation-class edge has no COMM-only event. Equations can
identify endpoints but cannot manufacture a firing without an output. -/
theorem source_drop_has_no_comm_event :
    ¬ ∃ event : PresentationInstance rhoSourceComm.toUnpositioned [] Srt.pr,
      (Quotient.mk _ event.source : TermQ rhoSourceE [] Srt.pr) =
        Quotient.mk _ dropChan ∧
      (Quotient.mk _ event.target : TermQ rhoSourceE [] Srt.pr) =
        Quotient.mk _ nilP := by
  intro event
  have step := (authored_class_endpoints_iff_stepModE
    rhoSourceComm.toUnpositioned Srt.pr dropChan nilP).mp event
  exact source_drop_nil_not_comm nilP
    ((rhoSourceComm.stepModE_iff_toUnpositioned).mpr step)

end Mettapedia.OSLF.Binding.RhoSourceEventComparison
