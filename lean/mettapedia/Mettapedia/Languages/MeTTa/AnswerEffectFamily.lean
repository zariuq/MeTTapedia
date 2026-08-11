import Mettapedia.GSLT.Dynamics.AnswerEffect

/-!
# Reflective query indexed by an answer effect

There need not be one weakest MeTTa answer carrier.  Ordered enumeration,
occurrence bags, finite support, weights, and provenance make different
observable distinctions.  This module isolates that choice as an index of the
reflective query semantics instead of fixing it inside the definition of
query.

An answer-effect morphism transports a query model and commutes with query.
Consequently a quotient such as `List -> Multiset -> Finset` is compositional,
but the non-faithfulness theorems in `AnswerEffect.lean` remain explicit: a
downstream support model cannot claim to preserve order or multiplicity.

This is the answer-production axis of a MeTTa-family model, not a definition
of the whole family.  Reflection, inertness, internal control, capabilities,
and observation remain independent structure.
-/

namespace Mettapedia.Languages.MeTTa.AnswerEffectFamily

open Mettapedia.GSLT.Dynamics.AnswerEffects

universe u

/-- The part of a reflective query model that depends on its answer effect.

The ambient space supplies occurrences.  Matching an occurrence may itself
produce alternatives, and instantiation turns each successful binding into an
answer atom. -/
structure ReflectiveQueryModel (effect : AnswerEffect.{u}) where
  Atom : Type u
  Space : Type u
  Binding : Type u
  occurrences : Space -> effect.Carrier Atom
  matchAtom : Atom -> Atom -> effect.Carrier Binding
  instantiate : Binding -> Atom -> Atom

namespace ReflectiveQueryModel

/-- Query an explicitly supplied collection of source occurrences. -/
def queryFrom {effect : AnswerEffect.{u}}
    (model : ReflectiveQueryModel effect)
    (source : effect.Carrier model.Atom) (pattern template : model.Atom) :
    effect.Carrier model.Atom :=
  effect.bind source fun candidate =>
    effect.bind (model.matchAtom pattern candidate) fun binding =>
      effect.pure (model.instantiate binding template)

/-- Reflective query of a space under the selected answer effect. -/
def query {effect : AnswerEffect.{u}}
    (model : ReflectiveQueryModel effect) (space : model.Space)
    (pattern template : model.Atom) : effect.Carrier model.Atom :=
  model.queryFrom (model.occurrences space) pattern template

/-- Query distributes over the answer effect's finite source choice. -/
theorem queryFrom_choice {effect : AnswerEffect.{u}}
    (model : ReflectiveQueryModel effect)
    (first second : effect.Carrier model.Atom)
    (pattern template : model.Atom) :
    model.queryFrom (effect.choice first second) pattern template =
      effect.choice (model.queryFrom first pattern template)
        (model.queryFrom second pattern template) := by
  exact effect.choice_bind first second fun candidate =>
    effect.bind (model.matchAtom pattern candidate) fun binding =>
      effect.pure (model.instantiate binding template)

/-- Transport every answer-producing operation along an answer-effect
morphism.  Atom syntax, spaces, and instantiation remain unchanged. -/
def mapEffect {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    (model : ReflectiveQueryModel source) : ReflectiveQueryModel target where
  Atom := model.Atom
  Space := model.Space
  Binding := model.Binding
  occurrences := fun space => morphism.map (model.occurrences space)
  matchAtom := fun pattern candidate => morphism.map (model.matchAtom pattern candidate)
  instantiate := model.instantiate

/-- Effect morphisms commute with query over explicit occurrences. -/
theorem map_queryFrom {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    (model : ReflectiveQueryModel source)
    (answers : source.Carrier model.Atom)
    (pattern template : model.Atom) :
    morphism.map (model.queryFrom answers pattern template) =
      (model.mapEffect morphism).queryFrom (morphism.map answers)
        pattern template := by
  rw [queryFrom, morphism.map_bind]
  apply congrArg (target.bind (morphism.map answers))
  funext candidate
  rw [morphism.map_bind]
  apply congrArg (target.bind (morphism.map (model.matchAtom pattern candidate)))
  funext binding
  exact morphism.map_pure (model.instantiate binding template)

/-- Effect morphisms commute with reflective space query. -/
theorem map_query {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    (model : ReflectiveQueryModel source) (space : model.Space)
    (pattern template : model.Atom) :
    morphism.map (model.query space pattern template) =
      (model.mapEffect morphism).query space pattern template := by
  exact model.map_queryFrom morphism (model.occurrences space) pattern template

end ReflectiveQueryModel

/-! ## The canonical reflective-query family -/

/-- Ordered query preserves the order in which occurrences and bindings are
enumerated. -/
abbrev OrderedQueryModel := ReflectiveQueryModel listEffect

/-- Occurrence query forgets order while preserving every derivation
occurrence. -/
abbrev OccurrenceQueryModel := ReflectiveQueryModel bagEffect

/-- Support query remembers only whether an answer occurs. -/
noncomputable abbrev SupportQueryModel := ReflectiveQueryModel supportEffect

/-- Ordered query has a compositional occurrence-bag quotient. -/
theorem ordered_query_to_occurrences (model : OrderedQueryModel)
    (space : model.Space) (pattern template : model.Atom) :
    listToBag.map (model.query space pattern template) =
      (model.mapEffect listToBag).query space pattern template :=
  model.map_query listToBag space pattern template

/-- Occurrence query has a compositional finite-support quotient. -/
theorem occurrence_query_to_support (model : OccurrenceQueryModel)
    (space : model.Space) (pattern template : model.Atom) :
    bagToSupport.map (model.query space pattern template) =
      (model.mapEffect bagToSupport).query space pattern template :=
  model.map_query bagToSupport space pattern template

/-- The direct ordered-to-support quotient is the composite of the two
canonical answer-effect morphisms. -/
theorem ordered_query_to_support (model : OrderedQueryModel)
    (space : model.Space) (pattern template : model.Atom) :
    listToSupport.map (model.query space pattern template) =
      (model.mapEffect listToSupport).query space pattern template :=
  model.map_query listToSupport space pattern template

end Mettapedia.Languages.MeTTa.AnswerEffectFamily
