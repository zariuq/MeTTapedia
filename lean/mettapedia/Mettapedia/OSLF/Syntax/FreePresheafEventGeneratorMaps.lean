import Mettapedia.OSLF.Syntax.FreePresheafEventExtension
import Mettapedia.OSLF.Syntax.EventGraphNullaryPresentationFunctor

/-!
# Changing generators in a free event extension

Free adjoining of proof-relevant events is functorial in the generator graph
as well as in the prior graph. A generator translation acts on the new-event
summand and fixes every old event. The two injection equations determine its
action uniquely, so profile changes cannot silently erase or merge the old
history.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FreePresheafEventGeneratorMaps

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
open Mettapedia.OSLF.Binding.EventGraphNullaryPresentationFunctor

universe u v w

variable {C : Type u} [Category.{v} C]
variable {V : C ⥤ Type w}

/-- Apply a translation to the newly adjoined firing occurrences while
leaving the old event graph unchanged. -/
def mapGenerator (prior : Graph V) {first later : Graph V}
    (translation : Hom first later) :
    Hom (graphSum prior first) (graphSum prior later) :=
  graphCopair (graphInl prior later)
    (Hom.comp translation (graphInr prior later))

/-- Existing event occurrences survive a change of generators literally. -/
theorem mapGenerator_old (prior : Graph V)
    {first later : Graph V} (translation : Hom first later) :
    Hom.comp (graphInl prior first) (mapGenerator prior translation) =
      graphInl prior later :=
  graphInl_copair _ _

/-- Each newly adjoined event follows exactly the selected generator map. -/
theorem mapGenerator_new (prior : Graph V)
    {first later : Graph V} (translation : Hom first later) :
    Hom.comp (graphInr prior first) (mapGenerator prior translation) =
      Hom.comp translation (graphInr prior later) :=
  graphInr_copair _ _

/-- The two event injections determine the translated free extension
uniquely. This is the coproduct universal property on full event graphs. -/
theorem mapGenerator_unique (prior : Graph V)
    {first later : Graph V} (translation : Hom first later)
    (candidate : Hom (graphSum prior first) (graphSum prior later))
    (old : Hom.comp (graphInl prior first) candidate =
      graphInl prior later)
    (new : Hom.comp (graphInr prior first) candidate =
      Hom.comp translation (graphInr prior later)) :
    candidate = mapGenerator prior translation :=
  graphCopair_unique _ _ candidate old new

/-- An identity profile translation leaves both old and new events fixed. -/
theorem mapGenerator_id (prior generator : Graph V) :
    mapGenerator prior (Hom.id generator) =
      Hom.id (graphSum prior generator) := by
  apply Hom.ext
  ext X event
  cases event <;> rfl

/-- Consecutive profile translations agree with their composite on every
retained event occurrence. -/
theorem mapGenerator_comp (prior : Graph V)
    {first middle last : Graph V}
    (earlier : Hom first middle) (later : Hom middle last) :
    mapGenerator prior (Hom.comp earlier later) =
      Hom.comp (mapGenerator prior earlier) (mapGenerator prior later) := by
  apply Hom.ext
  ext X event
  cases event <;> rfl

/-- For a fixed prior history, free adjoining is functorial in the authored
generator profile. -/
def generatorFunctor (prior : Graph V) : Graph V ⥤ Graph V where
  obj generator := graphSum prior generator
  map translation := mapGenerator prior translation
  map_id generator := mapGenerator_id prior generator
  map_comp earlier later := mapGenerator_comp prior earlier later

/-- Changing the old graph and changing the authored generator profile
commute. This gives the two-variable coherence needed to interpret a profile
inclusion uniformly over every already recorded history graph. -/
theorem mapGenerator_natural_prior
    {prior next first later : Graph V}
    (oldMap : Hom prior next) (translation : Hom first later) :
    Hom.comp (freeMap (generators := first) oldMap).graphMap
        (mapGenerator next translation) =
      Hom.comp (mapGenerator prior translation)
        (freeMap (generators := later) oldMap).graphMap := by
  apply Hom.ext
  ext X event
  cases event <;> rfl

/-- Adding no prior events cannot hide a genuinely new authored firing. An
unrepresented target generator remains outside the image of the induced free
extension map at the same context. -/
theorem mapGenerator_empty_not_surjective_at
    {first later : Graph V} (translation : Hom first later) (X : C)
    (missing : ¬ Function.Surjective (translation.edgeMap.app X)) :
    ¬ Function.Surjective
      ((mapGenerator (emptyGraph V) translation).edgeMap.app X) := by
  intro surjective
  apply missing
  intro target
  obtain ⟨preimage, imageEq⟩ := surjective (Sum.inr target)
  cases preimage with
  | inl old => exact old.elim
  | inr authored => exact ⟨authored, Sum.inr.inj imageEq⟩

/-- A model of the larger generator profile is also a model of the smaller
profile, by interpreting each smaller event through the profile map. -/
def restrictModels {first later : Graph V}
    (translation : Hom first later) :
    Equipped later ⥤ Equipped first where
  obj model :=
    { graph := model.graph
      generatorMap := Hom.comp translation model.generatorMap }
  map := fun {X Y} mapping =>
    { graphMap := mapping.graphMap
      generator_comm := by
        change Hom.comp (Hom.comp translation X.generatorMap) mapping.graphMap =
          Hom.comp translation Y.generatorMap
        calc
          Hom.comp (Hom.comp translation X.generatorMap) mapping.graphMap =
              Hom.comp translation (Hom.comp X.generatorMap mapping.graphMap) := by
                apply Hom.ext
                simp [Hom.comp, Category.assoc]
          _ = Hom.comp translation Y.generatorMap := by rw [mapping.generator_comm] }
  map_id model := by
    apply EquippedHom.ext
    rfl
  map_comp earlier later := by
    apply EquippedHom.ext
    rfl

/-- A profile translation induces a natural comparison between the two free
event-model functors. Its component acts on each authored generator and fixes
the entire prior event graph. -/
def freeComparison {first later : Graph V}
    (translation : Hom first later) :
    free first ⟶ free later ⋙ restrictModels translation where
  app prior :=
    { graphMap := mapGenerator prior translation
      generator_comm := mapGenerator_new prior translation }
  naturality prior next oldMap := by
    apply EquippedHom.ext
    exact mapGenerator_natural_prior oldMap translation

/-- Restricting a model along an authored profile translation commutes with
the free-event adjunction: the resulting interpretation of every old event is
the same graph map. This is the hom-set compatibility of the free comparison,
not merely naturality of its underlying event maps. -/
theorem freeComparison_adjunction_compatible {first later : Graph V}
    (translation : Hom first later) (prior : Graph V)
    (A : Equipped later) (interpretation : freeObject later prior ⟶ A) :
    freeHomEquiv first prior ((restrictModels translation).obj A)
        ((freeComparison translation).app prior ≫
          (restrictModels translation).map interpretation) =
      freeHomEquiv later prior A interpretation := by
  change Hom.comp (graphInl prior first)
      (Hom.comp (mapGenerator prior translation) interpretation.graphMap) =
    Hom.comp (graphInl prior later) interpretation.graphMap
  calc
    Hom.comp (graphInl prior first)
        (Hom.comp (mapGenerator prior translation) interpretation.graphMap) =
      Hom.comp (Hom.comp (graphInl prior first)
        (mapGenerator prior translation)) interpretation.graphMap := by
          apply Hom.ext
          simp [Hom.comp, Category.assoc]
    _ = Hom.comp (graphInl prior later) interpretation.graphMap := by
      rw [mapGenerator_old]

/-! ## Comparison with freely generated nullary rule trees -/

/-- Under a graph map, reading the root of a translated nullary firing
tree gives exactly the graph-theoretic image of its original event, for any
endpoint-indexed tree. No quotient or choice of a new firing is involved. -/
theorem treeEvent_mapFix {first later : Graph V}
    (translation : Hom first later) {X : C}
    {pair : V.obj X × V.obj X}
    (tree : (rules first).Fix () ⟨X, pair⟩) :
    treeEvent later
        ((presentationMap translation).rules.mapFix () ⟨X, pair⟩ tree) =
      mapEvent translation (treeEvent first tree) := by
  obtain ⟨event, rfl⟩ := (eventFiberEquiv first X pair).surjective tree
  change treeEvent later
      ((presentationMap translation).rules.mapFix () ⟨X, pair⟩
        (eventTree first event)) =
    mapEvent translation (treeEvent first (eventTree first event))
  rw [presentationMap_event]
  rfl

/-- The free event-model map and the free nullary rule-algebra map agree on
every new firing, even with arbitrary prior events present. The old-event
summand is controlled separately by `mapGenerator_old`. -/
theorem mapGenerator_matches_treeEvent (prior : Graph V)
    {first later : Graph V} (translation : Hom first later)
    {X : C} {pair : V.obj X × V.obj X}
    (event : EndpointFiber first X pair) :
    (mapGenerator prior translation).edgeMap.app X (Sum.inr event.1) =
      Sum.inr (treeEvent later
        ((presentationMap translation).rules.mapFix () ⟨X, pair⟩
          (eventTree first event))).1 := by
  rw [treeEvent_mapFix]
  rfl

end Mettapedia.OSLF.Binding.FreePresheafEventGeneratorMaps
