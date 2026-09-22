import Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of lawful WM-calculus readings

Objects are models of the existing three-sorted WM signature and its core
observation laws. Arrows are operation- and valuation-preserving reading
morphisms. This gives categorical backend substitution a literal meaning:
maps preserve the interpretation of authored WM terms and the native answer
graph, while behavioral agreement requires the separate query-coverage law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusReadingCategory

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient

/-- A model of the WM signature with the actual core observation laws. -/
structure LawfulReading where
  State : Type
  Query : Type
  Evidence : Type
  reading : WMReading State Query Evidence
  laws : reading.CoreLaws

/-- Homomorphisms preserve the sorted syntax and named valuations. -/
instance : Category LawfulReading where
  Hom source target := ReadingMorphism source.reading target.reading
  id source := ReadingMorphism.id source.reading
  comp f g := ReadingMorphism.comp f g
  id_comp := by
    intro source target hom
    cases hom
    rfl
  comp_id := by
    intro source target hom
    cases hom
    rfl
  assoc := by
    intro first second third fourth f g h
    cases f
    cases g
    cases h
    rfl

/-- The observational quotient is itself a lawful reading object. -/
def quotientObject (model : LawfulReading) : LawfulReading where
  State := ObsState model.reading
  Query := model.Query
  Evidence := model.Evidence
  reading := quotientReading model.reading model.laws
  laws := quotientReading_coreLaws model.reading model.laws

/-- Every lawful reading has a canonical arrow to its observational
quotient. The arrow preserves syntax and the dependent answer graph. -/
def quotientArrow (model : LawfulReading) : model ⟶ quotientObject model :=
  quotientMorphism model.reading model.laws

/-- This arrow maps a state to its observational class. -/
theorem quotientArrow_state (model : LawfulReading) (state : model.State) :
    (quotientArrow model).mapState state = classOf model.reading state :=
  rfl

/-- Target observations distinguish its states. This is stronger than the
WM laws and is not silently assumed for arbitrary backends. -/
def ObservationSeparated (model : LawfulReading) : Prop :=
  ∀ first second : model.State,
    model.reading.Agree .state first second → first = second

/-- The canonical observational quotient always belongs to the separated
part of the reading category. -/
theorem quotientObject_separated (model : LawfulReading) :
    ObservationSeparated (quotientObject model) := by
  intro first second agree
  exact (quotientReading_agree_iff_eq model.reading model.laws
    first second).1 agree

/-- Exact factorability condition: the state map must identify states that
the source cannot distinguish. -/
def StateCompatible {source target : LawfulReading}
    (hom : source ⟶ target) : Prop :=
  ∀ first second : source.State,
    source.reading.Agree .state first second →
      hom.mapState first = hom.mapState second

/-- Query coverage and an observation-separated target are sufficient for
the exact factorability condition. Neither is assumed for all morphisms. -/
theorem stateCompatible_of_cover_separated {source target : LawfulReading}
    (hom : source ⟶ target)
    (covers : Function.Surjective hom.mapQuery)
    (separated : ObservationSeparated target) :
    StateCompatible hom := by
  intro first second agree
  exact separated _ _ (hom.agree_map covers .state agree)

/-- A compatible state map descends from raw states to behavioral classes. -/
def factorState {source target : LawfulReading}
    (hom : source ⟶ target)
    (compatible : StateCompatible hom) :
    (quotientObject source).State → target.State :=
  Quotient.lift hom.mapState (by
    intro first second agree
    exact compatible first second agree)

/-- The factor is itself a WM-reading morphism, not merely a function on
state classes. -/
def factorArrow {source target : LawfulReading}
    (hom : source ⟶ target)
    (compatible : StateCompatible hom) :
    quotientObject source ⟶ target where
  mapState := factorState hom compatible
  mapQuery := hom.mapQuery
  mapEvidence := hom.mapEvidence
  revise_comm := by
    intro first second
    induction first using Quotient.inductionOn with
    | _ first' =>
      induction second using Quotient.inductionOn with
      | _ second' =>
        exact hom.revise_comm first' second'
  extract_comm := by
    intro state query
    induction state using Quotient.inductionOn with
    | _ state' => exact hom.extract_comm state' query
  combine_comm := hom.combine_comm
  zero_comm := hom.zero_comm
  world_comm := hom.world_comm
  query_comm := hom.query_comm

/-- The raw-state map factors through the quotient arrow on every sort. -/
theorem quotientArrow_factorization {source target : LawfulReading}
    (hom : source ⟶ target)
    (compatible : StateCompatible hom) :
    quotientArrow source ≫ factorArrow hom compatible = hom := by
  cases hom
  rfl

/-- The factor is unique among all reading morphisms whose composite with
the quotient arrow is the given raw-state morphism. -/
theorem quotientArrow_factor_unique {source target : LawfulReading}
    (hom : source ⟶ target)
    (compatible : StateCompatible hom)
    (candidate : quotientObject source ⟶ target)
    (factorizes : quotientArrow source ≫ candidate = hom) :
    candidate = factorArrow hom compatible := by
  apply ReadingMorphism.ext
  · funext state
    induction state using Quotient.inductionOn with
    | _ raw =>
      have equal := congrArg (fun map : source ⟶ target => map.mapState raw) factorizes
      exact equal
  · exact congrArg (fun map : source ⟶ target => map.mapQuery) factorizes
  · exact congrArg (fun map : source ⟶ target => map.mapEvidence) factorizes

/-- Any proposed factorization forces the exact state-compatibility law.
This is the necessary half of the quotient's universal property. -/
theorem stateCompatible_of_factorization {source target : LawfulReading}
    (hom : source ⟶ target)
    (candidate : quotientObject source ⟶ target)
    (factorizes : quotientArrow source ≫ candidate = hom) :
    StateCompatible hom := by
  intro first second agree
  have equalClasses :=
    (classOf_eq_iff_agree source.reading first second).2 agree
  have firstMap := congrArg (fun map : source ⟶ target => map.mapState first) factorizes
  have secondMap := congrArg (fun map : source ⟶ target => map.mapState second) factorizes
  calc
    hom.mapState first = candidate.mapState (classOf source.reading first) := firstMap.symm
    _ = candidate.mapState (classOf source.reading second) := congrArg candidate.mapState equalClasses
    _ = hom.mapState second := secondMap

/-- A morphism factors through the observational quotient exactly when its
state map respects source agreement; the factor is then unique. -/
theorem factorsThroughQuotient_iff {source target : LawfulReading}
    (hom : source ⟶ target) :
    (∃ factor : quotientObject source ⟶ target,
      quotientArrow source ≫ factor = hom) ↔ StateCompatible hom := by
  constructor
  · rintro ⟨factor, equal⟩
    exact stateCompatible_of_factorization hom factor equal
  · intro compatible
    exact ⟨factorArrow hom compatible,
      quotientArrow_factorization hom compatible⟩

/-- If a source agreement is distinguished by the target, no morphism out
of the quotient can reproduce the original map. Missing target-query
coverage can produce exactly this obstruction. -/
theorem no_factor_of_agreement_lost {source target : LawfulReading}
    (hom : source ⟶ target)
    (witness : ∃ first second : source.State,
      source.reading.Agree .state first second ∧
      ¬ target.reading.Agree .state
        (hom.mapState first) (hom.mapState second)) :
    ¬ ∃ factor : quotientObject source ⟶ target,
      quotientArrow source ≫ factor = hom := by
  rintro ⟨factor, factorizes⟩
  obtain ⟨first, second, agree, lost⟩ := witness
  have equal := (stateCompatible_of_factorization hom factor factorizes)
    first second agree
  exact lost (by rw [equal]; exact target.reading.agree_refl .state _)

end Mettapedia.OSLF.Framework.WMCalculusReadingCategory
