import Mettapedia.GSLT.Core.OperationalColimitPathSupport

/-!
# Positive witnesses after an explicitly named source stage

Common-stage support can retain an endpoint's original stage and give an
actual route out of it. This strengthens existence of arbitrary stage
representatives without assuming that stage maps are injective or reflect
reductions. The witness is positive; no future absence follows from it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open CategoryTheory

universe u

variable {J : Type u} [SmallCategory J] [IsFilteredOrEmpty J]

theorem stage_relation_from_inject (diagram : J ⥤ OperationalTheory.{u})
    (relation : StageRelation diagram)
    (carry : ∀ {a b : J} (route : a ⟶ b) {left right : (diagram.obj a).theory.Term},
      relation a left right → relation b ((diagram.map route).mapTerm left)
        ((diagram.map route).mapTerm right))
    {site : J} (start : (diagram.obj site).theory.Term) {finish : Term diagram}
    (supported : HasStageRelation diagram relation (inject diagram site start) finish) :
    ∃ future, ∃ route : site ⟶ future, ∃ after : (diagram.obj future).theory.Term,
      relation future ((diagram.map route).mapTerm start) after ∧
        inject diagram future after = finish := by
  obtain ⟨stage, before, after, first, last, related⟩ := supported
  obtain ⟨common, fromWitness, fromSite, same⟩ :=
    (inject_eq_iff_eventually_equal diagram before start).mp first
  refine ⟨common, fromSite, (diagram.map fromWitness).mapTerm after, ?_,
    (inject_along diagram fromWitness after).symm.trans last⟩
  have transported := carry fromWitness related
  rw [same] at transported
  exact transported

theorem equivalent_from_stage_iff (diagram : J ⥤ OperationalTheory.{u})
    {site : J} (start : (diagram.obj site).theory.Term) (finish : Term diagram) :
    Equivalent diagram (inject diagram site start) finish ↔
      ∃ future, ∃ route : site ⟶ future, ∃ after : (diagram.obj future).theory.Term,
        (diagram.obj future).theory.Equiv ((diagram.map route).mapTerm start) after ∧
          inject diagram future after = finish := by
  constructor
  · intro equivalent
    exact stage_relation_from_inject diagram _
      (fun {_ _} route {_ _} equation => (diagram.map route).mapEquiv equation) start
      ((equivalent_iff_has_stage_equation diagram).mp equivalent)
  · rintro ⟨future, route, after, equivalent, same⟩
    apply (equivalent_iff_has_stage_equation diagram).mpr
    exact ⟨future, _, after, (inject_along diagram route start).symm, same, equivalent⟩

theorem reduction_from_stage_iff (diagram : J ⥤ OperationalTheory.{u})
    {site : J} (start : (diagram.obj site).theory.Term) (finish : Term diagram) :
    Reduction diagram (inject diagram site start) finish ↔
      ∃ future, ∃ route : site ⟶ future, ∃ after : (diagram.obj future).theory.Term,
        (diagram.obj future).theory.Step ((diagram.map route).mapTerm start) after ∧
          inject diagram future after = finish := by
  constructor
  · intro step
    exact stage_relation_from_inject diagram _
      (fun {_ _} route {_ _} step => (diagram.map route).mapStep step) start
      ((reduction_iff_has_stage_reduction diagram).mp step)
  · rintro ⟨future, route, after, step, same⟩
    apply (reduction_iff_has_stage_reduction diagram).mpr
    exact ⟨future, _, after, (inject_along diagram route start).symm, same, step⟩

theorem multiStep_from_stage_iff (diagram : J ⥤ OperationalTheory.{u})
    {site : J} (start : (diagram.obj site).theory.Term) (finish : Term diagram) :
    (theory diagram).MultiStep (inject diagram site start) finish ↔
      ∃ future, ∃ route : site ⟶ future, ∃ after : (diagram.obj future).theory.Term,
        (diagram.obj future).theory.MultiStep ((diagram.map route).mapTerm start) after ∧
          inject diagram future after = finish := by
  constructor
  · intro path
    exact stage_relation_from_inject diagram _
      (fun {_ _} route {_ _} path => carryPath (diagram.map route) path) start
      ((multiStep_iff_has_stage_path diagram).mp path)
  · rintro ⟨future, route, after, path, same⟩
    apply (multiStep_iff_has_stage_path diagram).mpr
    exact ⟨future, _, after, (inject_along diagram route start).symm, same, path⟩

#print axioms stage_relation_from_inject
#print axioms equivalent_from_stage_iff
#print axioms reduction_from_stage_iff
#print axioms multiStep_from_stage_iff

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
