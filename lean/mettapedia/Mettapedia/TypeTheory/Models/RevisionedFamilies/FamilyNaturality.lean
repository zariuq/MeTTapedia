import Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent
import Mettapedia.OSLF.Framework.WMCalculusQuotientFunctor

/-!
# Dependent WM observations across semantic backend maps

An operation-preserving reading map need not preserve behavioral agreement:
its target may have additional queries. Exactly when agreement is preserved,
the map becomes a substitution between observable-state contexts in Prime's
existing semantic families CwF. Reindexing every dependent family along
that substitution commutes with reindexing along the raw-state backend map.
The construction is functorial on the already defined category of behavioral
reading maps; it does not manufacture a quotient map for an arbitrary backend.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyNaturality

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusQuotientFunctor
open Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent

/-- A reading morphism yields a CwF substitution on observable state
contexts exactly if it preserves the agreement relation that defines those
contexts. No query-surjectivity hypothesis is silently assumed. -/
theorem observableSub_exists_iff_agree_forward
    {S₁ Q₁ V₁ S₂ Q₂ V₂ : Type}
    {source : WMReading S₁ Q₁ V₁} {target : WMReading S₂ Q₂ V₂}
    (hom : ReadingMorphism source target) :
    (∃ quotientSub : familiesCwF.Sub
        (observableContext source) (observableContext target),
      ∀ state, quotientSub (classOf source state) =
        classOf target (hom.mapState state)) ↔
      ∀ first second, source.Agree .state first second →
        target.Agree .state (hom.mapState first) (hom.mapState second) := by
  constructor
  · rintro ⟨quotientSub, commutes⟩ first second agree
    have equalClasses := (classOf_eq_iff_agree source first second).2 agree
    have mapped := congrArg quotientSub equalClasses
    rw [commutes first, commutes second] at mapped
    exact (classOf_eq_iff_agree target _ _).1 mapped
  · intro preserves
    refine ⟨Quotient.lift
      (fun state => classOf target (hom.mapState state)) ?_, ?_⟩
    · intro first second agree
      exact (classOf_eq_iff_agree target _ _).2
        (preserves first second agree)
    · intro state
      rfl

/-- Pull back an observable target family along the lawful behavioral
backend map's quotient substitution. -/
def pullFamily {source target : BehavioralReading}
    (hom : source ⟶ target)
    (P : familiesCwF.Ty (observableContext target.model.reading)) :
    familiesCwF.Ty (observableContext source.model.reading) :=
  familiesCwF.tySub P (quotientMap hom).mapState

/-- The dependent-family square commutes on raw states: quotient first and
then backend map gives the same fibre as backend map first and then quotient.
This is the CwF-level naturality law behind backend-independent observations. -/
theorem pullFamily_raw_square {source target : BehavioralReading}
    (hom : source ⟶ target)
    (P : familiesCwF.Ty (observableContext target.model.reading)) :
    familiesCwF.tySub (pullFamily hom P)
      (observationSub source.model.reading) =
    familiesCwF.tySub
      (familiesCwF.tySub P (observationSub target.model.reading))
      hom.readingMap.mapState := by
  funext state
  exact congrArg P (quotientMap_state hom state)

/-- The identity backend map acts as identity on every observable dependent
family, not merely on its extensional support. -/
theorem pullFamily_id (source : BehavioralReading)
    (P : familiesCwF.Ty (observableContext source.model.reading)) :
    pullFamily (𝟙 source) P = P := by
  rw [pullFamily, quotientMap_id]
  funext state
  rfl

/-- Reindexing observable families respects composition of behavioral
backend maps. -/
theorem pullFamily_comp {first middle last : BehavioralReading}
    (f : first ⟶ middle) (g : middle ⟶ last)
    (P : familiesCwF.Ty (observableContext last.model.reading)) :
    pullFamily (f ≫ g) P = pullFamily f (pullFamily g P) := by
  rw [pullFamily, quotientMap_comp]
  funext state
  rfl

/-- If agreement fails to survive a backend map, no substitution between
observable-state CwF contexts can commute with that map on raw states. -/
theorem no_observableSub_of_failed_agreement
    {S₁ Q₁ V₁ S₂ Q₂ V₂ : Type}
    {source : WMReading S₁ Q₁ V₁} {target : WMReading S₂ Q₂ V₂}
    (hom : ReadingMorphism source target)
    (fails : ¬ ∀ first second, source.Agree .state first second →
      target.Agree .state (hom.mapState first) (hom.mapState second)) :
    ¬ ∃ quotientSub : familiesCwF.Sub
        (observableContext source) (observableContext target),
      ∀ state, quotientSub (classOf source state) =
        classOf target (hom.mapState state) := by
  exact mt (observableSub_exists_iff_agree_forward hom).1 fails

end Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyNaturality
