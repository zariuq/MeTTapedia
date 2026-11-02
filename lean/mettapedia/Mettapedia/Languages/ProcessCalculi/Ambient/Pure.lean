import Mettapedia.Languages.ProcessCalculi.Ambient.FullLaws
import Mettapedia.Languages.ProcessCalculi.Ambient.FullReflection
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Extensions

/-!
# The pure calculus inside the core

The core of the calculus with communication extends the pure calculus by constructors (`coreExtension`):
capabilities and paths, the capability prefix, and the inputs and outputs of names and capabilities (`commLabels`),
with the same laws. Each law of the core has a shape that applies only the constructors of restriction, replication,
the bag and ambients, so its two sides apply the same constructors of communication (`AmbShape.avoids_iff`): the laws
keep a pure process pure (`coreKeeps`). The static theory of the core therefore extends that of the pure calculus
conservatively: a chain of laws of the core from a pure process is a chain of the pure calculus. A firing of the pure
calculus keeps a process pure as well (`AmbNuRawStep.avoids`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Pure

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (TermExtension KeepsAvoiding avoids avoids_apply avoids_collection
  avoids_lambda avoids_lift LawShape.avoids_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientNuCalc AmbShape ambient_generator_shape
  ambient_premises_nil AmbNuRawStep)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc commTerms capRule)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb)

/-- The labels of the constructors the core adds to the pure calculus. -/
def commLabels : List String :=
  ["CapIn", "CapOut", "CapOpen", "CapEps", "CapPath", "ACap", "AInName", "AOutName", "AInCap", "AOutCap"]

/-- **The core extends the pure calculus by the constructors of communication**, with the same laws. -/
theorem coreExtension : TermExtension ambientNuCalc ambientCoreCalc commLabels where
  terms := List.subset_append_left _ _
  labelled := by
    intro rule member outside
    rcases List.mem_append.mp member with inside | added
    · exact absurd inside outside
    · simp only [commTerms, capRule, List.mem_cons, List.not_mem_nil, or_false] at added
      rcases added with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  noCollections := by
    intro rule member outside parameter present kind
    rcases List.mem_append.mp member with inside | added
    · exact absurd inside outside
    · simp only [commTerms, capRule, List.mem_cons, List.not_mem_nil, or_false] at added
      rcases added with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present <;>
        rcases present with rfl | rfl <;> rfl
  apart := by
    intro rule member
    simp only [ambientNuCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Full.terms,
      Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefixRule, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by decide, fun algebra declared unit unitIs => ?_⟩ <;> cases declared
    cases unitIs
    decide
  equations := rfl
  premises := fun _ member => ambient_premises_nil member

theorem avoids_amb {name content : Pattern} :
    avoids commLabels (amb name content) = true ↔
      avoids commLabels name = true ∧ avoids commLabels content = true := by
  simp [amb, commLabels]

/-- **The two sides of a law of the core apply the same constructors of communication.** -/
theorem AmbShape.avoids_iff {source target : Pattern} (shape : AmbShape source target) :
    avoids commLabels source = true ↔ avoids commLabels target = true := by
  cases shape with
  | law shape => exact shape.avoids_iff (by decide) (by decide) (by decide) (by simp)
  | boundary name binder body => simp [commLabels]
  | boundaryReverse name binder body => simp [commLabels]

/-- **The laws of the core keep a pure process pure.** -/
theorem coreKeeps (base : BasePremiseEvaluator) : KeepsAvoiding base ambientCoreCalc commLabels := by
  intro source target generator
  rcases ambient_generator_shape generator with shape | shape
  · exact AmbShape.avoids_iff shape
  · exact (AmbShape.avoids_iff shape).symm

/-- **A firing of the pure calculus keeps a process pure.** -/
theorem AmbNuRawStep.avoids {source target : Pattern} (step : AmbNuRawStep source target)
    (avoiding : avoids commLabels source = true) : avoids commLabels target = true := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
      rw [avoids_collection] at avoiding
      have opening := avoiding _ (List.getElem_mem hi)
      rw [capability] at opening
      have bounded := avoiding _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [boundary, avoids_amb] at bounded
      simp only [avoids_apply, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at opening
      rw [avoids_collection]
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · exact opening.2.2
      · rcases List.mem_cons.mp member with rfl | member
        · exact bounded.2
        · exact avoiding _ (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member))
  | enter i hi j hj name target process host k hk mover capability destination =>
      rw [avoids_collection] at avoiding
      have moving := avoiding _ (List.getElem_mem hi)
      rw [mover, avoids_amb, avoids_collection] at moving
      have entering := moving.2 _ (List.getElem_mem hk)
      rw [capability] at entering
      simp only [avoids_apply, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at entering
      have hosting := avoiding _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [destination, avoids_amb] at hosting
      rw [avoids_collection]
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · rw [avoids_amb, avoids_collection]
        refine ⟨entering.2.1, fun inside insideMember => ?_⟩
        rcases List.mem_cons.mp insideMember with rfl | insideMember
        · rw [avoids_amb, avoids_collection]
          refine ⟨moving.1, fun moved movedMember => ?_⟩
          rcases List.mem_cons.mp movedMember with rfl | movedMember
          · exact entering.2.2
          · exact moving.2 _ (List.mem_of_mem_eraseIdx movedMember)
        · rcases List.mem_cons.mp insideMember with rfl | insideMember
          · exact hosting.2
          · cases insideMember
      · exact avoiding _ (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member))
  | exit i hi name parent process k hk mover capability =>
      rw [avoids_amb, avoids_collection] at avoiding
      have moving := avoiding.2 _ (List.getElem_mem hi)
      rw [mover, avoids_amb, avoids_collection] at moving
      have exiting := moving.2 _ (List.getElem_mem hk)
      rw [capability] at exiting
      simp only [avoids_apply, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at exiting
      rw [avoids_collection]
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · rw [avoids_amb, avoids_collection]
        refine ⟨moving.1, fun moved movedMember => ?_⟩
        rcases List.mem_cons.mp movedMember with rfl | movedMember
        · exact exiting.2.2
        · exact moving.2 _ (List.mem_of_mem_eraseIdx movedMember)
      · rcases List.mem_cons.mp member with rfl | member
        · rw [avoids_amb, avoids_collection]
          exact ⟨avoiding.1, fun other otherMember => avoiding.2 _ (List.mem_of_mem_eraseIdx otherMember)⟩
        · cases member
  | par i hi inner recurse =>
      rw [avoids_collection] at avoiding ⊢
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · exact recurse (avoiding _ (List.getElem_mem hi))
      · exact avoiding _ (List.mem_of_mem_eraseIdx member)
  | res binder inner recurse =>
      simp only [avoids_apply, avoids_lambda, List.mem_singleton, forall_eq] at avoiding ⊢
      exact ⟨avoiding.1, recurse avoiding.2⟩
  | ambient name inner recurse =>
      rw [avoids_amb] at avoiding ⊢
      exact ⟨avoiding.1, recurse avoiding.2⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Pure
