import Mettapedia.GSLT.Core.WriterGSLT
import Mettapedia.GSLT.Causality.OccurrenceHistory

/-!
# Occurrence history is the writer GSLT of a site

`OccurrenceHistory.Element` is the category of elements of `Hom(root, -)`.
Its writer states are terms of `spendLift (occurrenceGrading …)`.  This file
places that object in the category of GSLTs:

* a complete site makes the occurrence grading total;
* `π` is then `eraseMorphism` of that writer;
* the origin element is `η` of the root;
* `Element.forget` is `π` on `toWriter`.

Reversible (backward) steps stay in `Trace.ReversibleStep`.  They are a path
category, not a second GSLT of stored history.  No LanguageDef.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Mettapedia.GSLT.Causality.HistoryCover

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.WriterGSLT

universe uSite uEvent

variable {theory : GSLT}

local instance listAppendMonoid {α : Type*} : Monoid (List α) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := []
  one_mul := List.nil_append
  mul_one := List.append_nil

/-- Completeness of a site is exactly totality of the occurrence grading. -/
theorem occurrenceGrading_total
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (complete : P.Complete) :
    (occurrenceGrading P eq_iff).Total := by
  intro source target step
  obtain ⟨⟨site, evidence⟩⟩ := complete step
  refine ⟨[⟨source, target, ⟨site, evidence⟩⟩], ?_⟩
  exact ⟨⟨site, evidence⟩, rfl⟩

/-- The history GSLT of a complete, discrete-equation site. -/
abbrev historyGSLT
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (_complete : P.Complete) : GSLT :=
  theory.spendLift (occurrenceGrading P eq_iff)

/-- `π` for the occurrence writer. -/
def historyErase
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (complete : P.Complete) :
    GSLT.Morphism (historyGSLT P eq_iff complete) theory :=
  eraseMorphism (occurrenceGrading P eq_iff)
    (occurrenceGrading_total P eq_iff complete)

/-- `η` for the occurrence writer. -/
def historyEmbed
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (complete : P.Complete) :
    GSLT.Morphism theory (historyGSLT P eq_iff complete) :=
  embedMorphism (occurrenceGrading P eq_iff)
    (occurrenceGrading_total P eq_iff complete)

theorem history_erase_comp_embed
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (complete : P.Complete) :
    GSLT.Morphism.comp (historyErase P eq_iff complete)
        (historyEmbed P eq_iff complete) =
      GSLT.Morphism.id theory :=
  erase_comp_embed (occurrenceGrading P eq_iff)
    (occurrenceGrading_total P eq_iff complete)

/-- The origin element is the image of the root under `η`. -/
theorem origin_is_embed
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (complete : P.Complete) (root : theory.Term) :
    (originElement P root).toWriter =
      (historyEmbed P eq_iff complete).toFun root :=
  rfl

/-- Forgetting an element is `π` of its writer state. -/
theorem forget_is_erase
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (complete : P.Complete) {root : theory.Term}
    (element : Element P root) :
    element.forget =
      (historyErase P eq_iff complete).toFun element.toWriter :=
  rfl

/-- Extending an element is a step of the history GSLT. -/
theorem extend_is_history_step
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    (complete : P.Complete) {root target : theory.Term}
    (element : Element P root) (occurrence : Occurrence P element.target target) :
    (historyGSLT P eq_iff complete).Step
      element.toWriter (element.extend occurrence).toWriter :=
  extend_is_spendLift_step P eq_iff element occurrence

/-! ## Grid canary

The two-bit grid is a complete discrete site.  Its history GSLT is the
occurrence writer; `π ∘ η = id`; the origin is `η` of the origin cell. -/

theorem grid_complete : gridPresentation.Complete := by
  intro source target step
  rcases step with horiz | vert
  · exact ⟨⟨GridSite.horiz, ⟨horiz⟩⟩⟩
  · exact ⟨⟨GridSite.vert, ⟨vert⟩⟩⟩

theorem grid_occurrence_total :
    (occurrenceGrading gridPresentation grid_eq_iff).Total :=
  occurrenceGrading_total gridPresentation grid_eq_iff grid_complete

theorem grid_erase_comp_embed :
    GSLT.Morphism.comp (historyErase gridPresentation grid_eq_iff grid_complete)
        (historyEmbed gridPresentation grid_eq_iff grid_complete) =
      GSLT.Morphism.id gridTheory :=
  history_erase_comp_embed gridPresentation grid_eq_iff grid_complete

theorem grid_origin_is_embed :
    (originElement gridPresentation gridOrigin).toWriter =
      (historyEmbed gridPresentation grid_eq_iff grid_complete).toFun
        gridOrigin :=
  origin_is_embed gridPresentation grid_eq_iff grid_complete gridOrigin

theorem grid_forget_is_erase :
    (originElement gridPresentation gridOrigin).forget =
      (historyErase gridPresentation grid_eq_iff grid_complete).toFun
        (originElement gridPresentation gridOrigin).toWriter :=
  forget_is_erase gridPresentation grid_eq_iff grid_complete
    (originElement gridPresentation gridOrigin)

theorem grid_extend_is_history_step :
    (historyGSLT gridPresentation grid_eq_iff grid_complete).Step
      ((originElement gridPresentation gridOrigin).toWriter)
      (((originElement gridPresentation gridOrigin).extend gridHorizOcc).toWriter) :=
  extend_is_history_step gridPresentation grid_eq_iff grid_complete
    (originElement gridPresentation gridOrigin) gridHorizOcc

#print axioms occurrenceGrading_total
#print axioms history_erase_comp_embed
#print axioms origin_is_embed
#print axioms forget_is_erase
#print axioms extend_is_history_step
#print axioms grid_complete
#print axioms grid_erase_comp_embed
#print axioms grid_origin_is_embed
#print axioms grid_extend_is_history_step

end Mettapedia.GSLT.Causality.HistoryCover
