import Mettapedia.GSLT.Core.OperationalColimitStageEquality

/-!
# Composition of common-stage relation witnesses

Two adjacent relation witnesses may have different authored stages.
Filteredness brings them together and equalizes their middle carrier
representatives. Transport preservation and the stage's own composition
law then give a witness for the composite. Equations, reductions and finite
paths use this one alignment construction with their actual local laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open CategoryTheory

universe u

variable {J : Type u} [SmallCategory J]

abbrev StageRelation (diagram : J ⥤ OperationalTheory.{u}) :=
  ∀ stage : J, (diagram.obj stage).theory.Term → (diagram.obj stage).theory.Term → Prop

def HasStageRelation (diagram : J ⥤ OperationalTheory.{u}) (relation : StageRelation diagram)
    (left right : Term diagram) : Prop :=
  ∃ stage, ∃ before after : (diagram.obj stage).theory.Term,
    inject diagram stage before = left ∧ inject diagram stage after = right ∧
      relation stage before after

variable [IsFilteredOrEmpty J]

/-- Adjacent witnesses compose after actual stage transport. Only the two
local relation laws and their transport laws are supplied; the common stage
and agreement of its middle terms are constructed here. -/
theorem stage_relations_compose (diagram : J ⥤ OperationalTheory.{u})
    (first second composite : StageRelation diagram)
    (carryFirst : ∀ {a b : J} (route : a ⟶ b) {left right : (diagram.obj a).theory.Term},
      first a left right → first b ((diagram.map route).mapTerm left)
        ((diagram.map route).mapTerm right))
    (carrySecond : ∀ {a b : J} (route : a ⟶ b) {left right : (diagram.obj a).theory.Term},
      second a left right → second b ((diagram.map route).mapTerm left)
        ((diagram.map route).mapTerm right))
    (compose : ∀ (stage : J) {left middle right : (diagram.obj stage).theory.Term},
      first stage left middle → second stage middle right → composite stage left right)
    {left middle right : Term diagram}
    (earlier : HasStageRelation diagram first left middle)
    (later : HasStageRelation diagram second middle right) :
    HasStageRelation diagram composite left right := by
  obtain ⟨firstStage, firstBefore, firstAfter, firstImage, middleImage, firstRelation⟩ := earlier
  obtain ⟨lastStage, lastBefore, lastAfter, middleImage', lastImage, lastRelation⟩ := later
  have same : inject diagram firstStage firstAfter = inject diagram lastStage lastBefore :=
    middleImage.trans middleImage'.symm
  obtain ⟨common, firstRoute, lastRoute, same⟩ :=
    (inject_eq_iff_eventually_equal diagram firstAfter lastBefore).mp same
  refine ⟨common, (diagram.map firstRoute).mapTerm firstBefore,
    (diagram.map lastRoute).mapTerm lastAfter,
    (inject_along diagram firstRoute firstBefore).symm.trans firstImage,
    (inject_along diagram lastRoute lastAfter).symm.trans lastImage, ?_⟩
  have carriedFirst := carryFirst firstRoute firstRelation
  have carriedSecond := carrySecond lastRoute lastRelation
  rw [same] at carriedFirst
  exact compose common carriedFirst carriedSecond

#print axioms stage_relations_compose

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
