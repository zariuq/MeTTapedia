import Mettapedia.OSLF.Syntax.CanonicalRelationQueryEvents

/-!
# Occurrence-aware translations of relation-query tables

The existing relation-environment preorder compares only tuple values. A
translation of proof-relevant query events needs an action on selected tuple
positions, with an equation saying that the selected tuple is preserved.
These maps compose and act on the dependent query events. Faithful maps also
preserve the distinction between separate occurrences of the same tuple.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalRelationQueryTranslations

open Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames
open Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- A translation of the actual relation-query tables at every language,
assignment and query. It explicitly maps selected row positions. -/
structure TableMap (source target : RelationEnv) where
  onTuple : ∀ (lang : LanguageDef) (initial : Bindings)
    (relation : String) (arguments : List Pattern),
    Fin (relationTuples source lang initial relation arguments).length →
      Fin (relationTuples target lang initial relation arguments).length
  preserves : ∀ lang initial relation arguments position,
    (relationTuples target lang initial relation arguments).get
      (onTuple lang initial relation arguments position) =
    (relationTuples source lang initial relation arguments).get position

namespace TableMap

variable {first middle last fourth : RelationEnv}

/-- Table maps with the same action on occurrences are equal; their value
equations are proof-irrelevant. -/
theorem ext {f g : TableMap first last}
    (h : f.onTuple = g.onTuple) : f = g := by
  cases f with
  | mk fOn fPreserves =>
      cases g with
      | mk gOn gPreserves =>
          cases h
          rfl

def id (source : RelationEnv) : TableMap source source where
  onTuple := fun _ _ _ _ position => position
  preserves := by intros; rfl

def comp (f : TableMap first middle) (g : TableMap middle last) :
    TableMap first last where
  onTuple := fun lang initial relation arguments position =>
    g.onTuple lang initial relation arguments
      (f.onTuple lang initial relation arguments position)
  preserves := by
    intro lang initial relation arguments position
    exact (g.preserves lang initial relation arguments
      (f.onTuple lang initial relation arguments position)).trans
      (f.preserves lang initial relation arguments position)

theorem id_comp (f : TableMap first middle) :
    comp (id first) f = f := by
  apply ext
  rfl

theorem comp_id (f : TableMap first middle) :
    comp f (id middle) = f := by
  apply ext
  rfl

theorem comp_assoc (f : TableMap first middle)
    (g : TableMap middle last) (h : TableMap last fourth) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  rfl

/-- A table map is faithful when it does not identify separate selected row
occurrences in any actual query table. -/
def Faithful (f : TableMap first middle) : Prop :=
  ∀ lang initial relation arguments,
    Function.Injective (f.onTuple lang initial relation arguments)

theorem faithful_id (source : RelationEnv) :
    (id source).Faithful := by
  intro lang initial relation arguments
  exact Function.injective_id

theorem faithful_comp (f : TableMap first middle)
    (g : TableMap middle last) (hf : f.Faithful) (hg : g.Faithful) :
    (comp f g).Faithful := by
  intro lang initial relation arguments
  exact (hg lang initial relation arguments).comp
    (hf lang initial relation arguments)

/-- The empty external table embeds into every relation environment. Its
built-in rows retain exactly their original positions and tuple values. -/
def emptyTo (target : RelationEnv) : TableMap RelationEnv.empty target where
  onTuple := by
    intro lang initial relation arguments position
    refine ⟨position.1, ?_⟩
    have sourceBound : position.1 <
        (builtinRelationTuples lang relation
          (arguments.map (applyBindings initial))).length := by
      simpa [relationTuples, RelationEnv.empty] using position.2
    have bound :
        (builtinRelationTuples lang relation
          (arguments.map (applyBindings initial))).length ≤
        (relationTuples target lang initial relation arguments).length := by
      simp [relationTuples]
    exact Nat.lt_of_lt_of_le sourceBound bound
  preserves := by
    intro lang initial relation arguments position
    have sourceBound : position.1 <
        (builtinRelationTuples lang relation
          (arguments.map (applyBindings initial))).length := by
      simpa [relationTuples, RelationEnv.empty] using position.2
    have targetBound : position.1 <
        (builtinRelationTuples lang relation
          (arguments.map (applyBindings initial)) ++
          target.tuples relation
            (arguments.map (applyBindings initial))).length := by
      simp only [List.length_append]
      omega
    change
      (builtinRelationTuples lang relation
        (arguments.map (applyBindings initial)) ++
        target.tuples relation
          (arguments.map (applyBindings initial)))[position.1]'targetBound =
      (builtinRelationTuples lang relation
        (arguments.map (applyBindings initial)) ++
        ([] : List (List Pattern)))[position.1]'position.2
    simp only [List.getElem_append_left sourceBound, List.append_nil]

theorem emptyTo_faithful (target : RelationEnv) :
    (emptyTo target).Faithful := by
  intro lang initial relation arguments firstPosition secondPosition equal
  apply Fin.ext
  simpa [emptyTo] using congrArg Fin.val equal

end TableMap

/-- Translate a retained query event by its selected tuple occurrence. The
argument match and merge equation are unchanged because the tuple value is
preserved exactly. -/
def mapEvent {source target : RelationEnv} (translation : TableMap source target)
    {lang : LanguageDef} {initial final : Bindings}
    {relation : String} {arguments : List Pattern}
    (event : Event source lang initial relation arguments final) :
    Event target lang initial relation arguments final where
  tuple := event.tuple
  selectedTuple :=
    ⟨translation.onTuple lang initial relation arguments
      event.selectedTuple.position,
      (translation.preserves lang initial relation arguments
        event.selectedTuple.position).trans event.selectedTuple.represents⟩
  extension := event.extension
  selectedMatch := event.selectedMatch
  merge := event.merge

theorem mapEvent_id {source : RelationEnv}
    {lang : LanguageDef} {initial final : Bindings}
    {relation : String} {arguments : List Pattern}
    (event : Event source lang initial relation arguments final) :
    mapEvent (TableMap.id source) event = event := by
  cases event
  rfl

theorem mapEvent_comp {first middle last : RelationEnv}
    (f : TableMap first middle) (g : TableMap middle last)
    {lang : LanguageDef} {initial final : Bindings}
    {relation : String} {arguments : List Pattern}
    (event : Event first lang initial relation arguments final) :
    mapEvent (TableMap.comp f g) event =
      mapEvent g (mapEvent f event) := by
  cases event
  rfl

/-- Faithful table maps preserve distinct tuple-occurrence choices, even if
the two tuples and their final assignments are equal. -/
theorem mapEvent_distinct_tuple_positions
    {source target : RelationEnv} (translation : TableMap source target)
    (faithful : translation.Faithful)
    {lang : LanguageDef} {initial final : Bindings}
    {relation : String} {arguments : List Pattern}
    (first second : Event source lang initial relation arguments final)
    (different : first.selectedTuple.position ≠
      second.selectedTuple.position) :
    mapEvent translation first ≠ mapEvent translation second := by
  intro equal
  apply different
  apply faithful lang initial relation arguments
  exact congrArg (fun event => event.selectedTuple.position) equal

/-- A position-preserving table translation sends every executable query
result to an executable query result in the target environment. -/
theorem query_result_mono
    {source target : RelationEnv} (translation : TableMap source target)
    {lang : LanguageDef} {initial final : Bindings}
    {relation : String} {arguments : List Pattern}
    (result : final ∈ relationQueryStep source lang initial
      relation arguments) :
    final ∈ relationQueryStep target lang initial relation arguments := by
  obtain ⟨event⟩ := result_iff_event.mp result
  exact event_mem_result (mapEvent translation event)

/-- A translation of actual query-table positions preserves every bounded
canonical contextual derivation, including ordered relation-query premises
and recursively discharged congruence premises. -/
theorem stepAt_mono_tableMap
    {source target : RelationEnv} (translation : TableMap source target)
    {lang : LanguageDef} {fuel : Nat} {before after : Pattern}
    (evidence : StepAt (engineBasePremises source) lang fuel before after) :
    StepAt (engineBasePremises target) lang fuel before after := by
  induction fuel generalizing before after with
  | zero => cases evidence
  | succ previous inductionHypothesis =>
      have premiseMono :
          ∀ {initial final : Bindings} {premise : Premise},
            PremiseAt (engineBasePremises source) lang previous
                initial premise final →
              PremiseAt (engineBasePremises target) lang previous
                initial premise final := by
        intro initial final premise premiseEvidence
        cases premiseEvidence with
        | freshness member => exact .freshness member
        | relationQuery member =>
            apply PremiseAt.relationQuery
            apply query_result_mono translation
            simpa [engineBasePremises, premiseStepWithEnv] using member
        | forAll member => exact .forAll member
        | congruence recursive matched merged =>
            exact .congruence (inductionHypothesis recursive) matched merged
        | scopedRoot empty recursive matched merged =>
            exact .scopedRoot empty (inductionHypothesis recursive) matched merged
      have premisesMono :
          ∀ {initial final : Bindings} {premises : List Premise},
            PremisesAt (engineBasePremises source) lang previous
                initial premises final →
              PremisesAt (engineBasePremises target) lang previous
                initial premises final := by
        intro initial final premises premiseEvidence
        induction premises generalizing initial final with
        | nil =>
            cases premiseEvidence
            exact .nil initial
        | cons premise rest inductionHypothesis =>
            cases premiseEvidence with
            | cons first tail =>
                exact .cons (premiseMono first) (inductionHypothesis tail)
      cases evidence with
      | rule declared matched premises result =>
          exact .rule declared matched (premisesMono premises) result

/-- The unbounded least relation inherits the same table-translation law. -/
theorem step_mono_tableMap
    {source target : RelationEnv} (translation : TableMap source target)
    {lang : LanguageDef} {before after : Pattern}
    (evidence : Step (engineBasePremises source) lang before after) :
    Step (engineBasePremises target) lang before after := by
  obtain ⟨fuel, bounded⟩ := evidence
  exact ⟨fuel, stepAt_mono_tableMap translation bounded⟩

/-- The proved relational transport also preserves each executable endpoint
at the same contextual fuel. This does not identify distinct firing trees. -/
theorem rewriteAt_mono_tableMap
    {source target : RelationEnv} (translation : TableMap source target)
    (lang : LanguageDef) (fuel : Nat) (before after : Pattern)
    (result : after ∈ rewriteAt (engineBasePremises source) lang fuel before) :
    after ∈ rewriteAt (engineBasePremises target) lang fuel before :=
  mem_rewriteAt_iff_stepAt.mpr
    (stepAt_mono_tableMap translation
      (mem_rewriteAt_iff_stepAt.mp result))

#print axioms TableMap.id_comp
#print axioms TableMap.comp_id
#print axioms TableMap.comp_assoc
#print axioms TableMap.faithful_comp
#print axioms TableMap.emptyTo_faithful
#print axioms mapEvent_id
#print axioms mapEvent_comp
#print axioms mapEvent_distinct_tuple_positions
#print axioms query_result_mono
#print axioms stepAt_mono_tableMap
#print axioms step_mono_tableMap
#print axioms rewriteAt_mono_tableMap

end Mettapedia.OSLF.Binding.CanonicalRelationQueryTranslations
