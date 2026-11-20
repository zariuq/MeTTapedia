import Mettapedia.GSLT.Core.OperationalColimitReductionSupport

/-!
# Common-stage witnesses for finite ambient paths

Every finite path in the constructed filtered operational colimit is
realized by a finite path in one stage. Middle terms are synchronized by
the same transport construction used for equations and single reductions.

These are propositional path witnesses. Rule occurrences, answer-stream
multiplicities, divergence and effective stage selection are separate
observations; this theorem does not supply those laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open CategoryTheory

universe u v

variable {J : Type u} [SmallCategory J]

abbrev HasStagePath (diagram : J ⥤ OperationalTheory.{u})
    (left right : Term diagram) : Prop :=
  HasStageRelation diagram (fun stage => (diagram.obj stage).theory.MultiStep) left right

/-- Forward operational translations carry finite paths; local step
reflection is not required for this direction. -/
theorem carryPath {source : Mettapedia.GSLT.GSLT.{u}} {target : Mettapedia.GSLT.GSLT.{v}}
    (translation : OperationalTranslation source target) {left right : source.Term}
    (path : source.MultiStep left right) :
    target.MultiStep (translation.mapTerm left) (translation.mapTerm right) := by
  exact GSLT.MultiStep.rec (S := source)
    (motive := fun first last _ => target.MultiStep (translation.mapTerm first) (translation.mapTerm last))
    (fun term => .refl (translation.mapTerm term))
    (fun edge _ ih => .step (translation.mapStep edge) ih) path

variable [IsFilteredOrEmpty J]

theorem multiStep_iff_has_stage_path (diagram : J ⥤ OperationalTheory.{u})
    {left right : Term diagram} :
    (theory diagram).MultiStep left right ↔ HasStagePath diagram left right := by
  constructor
  · intro path
    exact GSLT.MultiStep.rec (S := theory diagram)
      (motive := fun first last _ => HasStagePath diagram first last)
      (fun term => by
        obtain ⟨stage, representative, same⟩ := term_from_stage diagram term
        exact ⟨stage, representative, representative, same, same, .refl _⟩)
      (fun edge _ ih =>
        stage_relations_compose diagram _ _ _
          (fun {_ _} route {_ _} step => (diagram.map route).mapStep step)
          (fun {_ _} route {_ _} path => carryPath (diagram.map route) path)
          (fun _ {_ _ _} step path => .step step path)
          ((reduction_iff_has_stage_reduction diagram).mp edge) ih) path
  · rintro ⟨stage, before, after, first, last, path⟩
    rw [← first, ← last]
    exact carryPath (inclusion diagram stage) path

#print axioms multiStep_iff_has_stage_path

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
