import Mettapedia.OSLF.Syntax.EventGraphNullaryPolynomial
import Mettapedia.OSLF.Syntax.IndexedRulePresentationCategory
import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationCategory
import Mettapedia.OSLF.Syntax.RuleListEventEmbedding

/-!
# Retained event graphs as nullary rule presentations

Over fixed state presheaves, every graph map acts on the individual nullary
constructors of its event polynomial. This action is functorial, so an authored
rule-list inclusion induces a cartesian rule-presentation map and a map of its
firing trees. No image or quotient of the event fibre is taken.

The construction covers rule occurrences after their premises have been
discharged into source firing events. A polynomial for open recursive premises
needs additional premise positions and their binding-context action.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EventGraphNullaryPresentationFunctor

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents

universe u v w

variable {C : Type u} [Category.{v} C] {V : C ⥤ Type w}

/-- The event graph's judgments are context-and-endpoint pairs. -/
def presentation (G : Graph V) : IndexedRulePresentationCategory.Presentation Unit where
  Judgment _ := Judgment (V := V)
  rules := rules G

/-- Map an event while retaining its fixed endpoint judgment. -/
def mapEvent {G H : Graph V} (f : G ⟶ H)
    {X : C} {pair : V.obj X × V.obj X}
    (event : EndpointFiber G X pair) : EndpointFiber H X pair := by
  refine ⟨f.edgeMap.app X event.1, ?_, ?_⟩
  · have h := congrArg
      (fun k : G.edge ⟶ V => k.app X event.1) f.source_comm
    simpa [event.2.1] using h
  · have h := congrArg
      (fun k : G.edge ⟶ V => k.app X event.1) f.target_comm
    simpa [event.2.2] using h

/-- A graph map gives a cartesian map of nullary rule presentations. -/
def presentationMap {G H : Graph V} (f : G ⟶ H) :
    presentation G ⟶ presentation H where
  judgment _ j := j
  rules := {
    onShape := fun _ _ event => mapEvent f event
    onPosition := fun _ _ _ => Equiv.refl Empty
    onNext := by
      intro _ _ _ impossible
      exact impossible.elim
  }

/-- The rule-presentation map reads the same event as its graph map. -/
theorem presentationMap_event {G H : Graph V} (f : G ⟶ H)
    {X : C} {pair : V.obj X × V.obj X}
    (event : EndpointFiber G X pair) :
    (presentationMap f).rules.mapFix () ⟨X, pair⟩ (eventTree G event) =
      eventTree H (mapEvent f event) := by
  dsimp [IndexedRulePolynomialMorphisms.Hom.mapFix,
    EventGraphNullaryPolynomial.eventTree,
    Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate]
  congr 1
  funext impossible
  exact impossible.elim

/-- An edge-injective graph map remains injective on every retained event
fibre at fixed endpoints. -/
theorem mapEvent_injective {G H : Graph V} (f : G ⟶ H)
    (edgeInjective : ∀ X, Function.Injective (f.edgeMap.app X))
    {X : C} {pair : V.obj X × V.obj X} :
    Function.Injective (mapEvent f : EndpointFiber G X pair →
      EndpointFiber H X pair) := by
  intro first second equal
  apply Subtype.ext
  exact edgeInjective X (congrArg Subtype.val equal)

/-- A graph map's naturality is the substitution law for each retained
firing, including substitutions represented by binder-extended contexts. -/
theorem mapEvent_reindex {G H : Graph V} (f : G ⟶ H)
    {X Y : C} (sigma : X ⟶ Y)
    {pair : V.obj X × V.obj X} (event : EndpointFiber G X pair) :
    mapEvent f (reindexEvent G sigma event) =
      reindexEvent H sigma (mapEvent f event) := by
  apply Subtype.ext
  have natural := congrArg
    (fun k : G.edge.obj X ⟶ H.edge.obj Y => k event.1)
    (f.edgeMap.naturality sigma)
  exact natural

/-- Since nullary trees are exactly their event fibres, an injective graph
translation cannot merge distinct complete firing histories. -/
theorem presentationMap_tree_injective {G H : Graph V} (f : G ⟶ H)
    (edgeInjective : ∀ X, Function.Injective (f.edgeMap.app X))
    {X : C} {pair : V.obj X × V.obj X} :
    Function.Injective
      ((presentationMap f).rules.mapFix () ⟨X, pair⟩) := by
  intro first second equal
  obtain ⟨firstEvent, rfl⟩ := (eventFiberEquiv G X pair).surjective first
  obtain ⟨secondEvent, rfl⟩ := (eventFiberEquiv G X pair).surjective second
  change (presentationMap f).rules.mapFix () ⟨X, pair⟩
      (eventTree G firstEvent) =
    (presentationMap f).rules.mapFix () ⟨X, pair⟩
      (eventTree G secondEvent) at equal
  rw [presentationMap_event, presentationMap_event] at equal
  exact congrArg (eventTree G)
    (mapEvent_injective f edgeInjective
      ((eventFiberEquiv H X pair).injective equal))

/-- The polynomial action on complete nullary histories commutes with
context substitution at both endpoints. -/
theorem presentationMap_reindexTree {G H : Graph V} (f : G ⟶ H)
    {X Y : C} (sigma : X ⟶ Y)
    {pair : V.obj X × V.obj X}
    (tree : (rules G).Fix () ⟨X, pair⟩) :
    (presentationMap f).rules.mapFix ()
        ⟨Y, reindexPair sigma pair⟩ (reindexTree G sigma tree) =
      reindexTree H sigma
        ((presentationMap f).rules.mapFix () ⟨X, pair⟩ tree) := by
  obtain ⟨event, rfl⟩ := (eventFiberEquiv G X pair).surjective tree
  change (presentationMap f).rules.mapFix ()
      ⟨Y, reindexPair sigma pair⟩
        (reindexTree G sigma (eventTree G event)) =
    reindexTree H sigma
      ((presentationMap f).rules.mapFix () ⟨X, pair⟩
        (eventTree G event))
  rw [reindexTree_eventTree, presentationMap_event,
    presentationMap_event, reindexTree_eventTree,
    mapEvent_reindex]

/-- Identity on event graphs is identity on nullary presentations. -/
theorem presentationMap_id (G : Graph V) :
    presentationMap (𝟙 G) = 𝟙 (presentation G) := by
  apply IndexedRulePresentationCategory.Presentation.Map.ext
  · rfl
  · apply heq_of_eq
    apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions
    · funext b j event
      apply Subtype.ext
      change ((FreePresheafEventExtension.Hom.id G).edgeMap.app j.fst) event.1 = event.1
      simp [FreePresheafEventExtension.Hom.id]
    · intro b j event
      change Subsingleton Empty
      infer_instance

/-- Composition of graph maps composes their actions on retained events. -/
theorem mapEvent_comp {G H K : Graph V} (f : G ⟶ H) (g : H ⟶ K)
    {X : C} {pair : V.obj X × V.obj X}
    (event : EndpointFiber G X pair) :
    mapEvent (f ≫ g) event = mapEvent g (mapEvent f event) := by
  apply Subtype.ext
  rfl

/-- The nullary-presentation construction preserves graph-map composition. -/
theorem presentationMap_comp {G H K : Graph V} (f : G ⟶ H) (g : H ⟶ K) :
    presentationMap (f ≫ g) = presentationMap f ≫ presentationMap g := by
  apply IndexedRulePresentationCategory.Presentation.Map.ext
  · rfl
  · apply heq_of_eq
    apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions
    · funext b j event
      exact mapEvent_comp f g event
    · intro b j event
      change Subsingleton Empty
      infer_instance

/-- A fixed-state event graph acts functorially on its nullary rule syntax. -/
def functor : Graph V ⥤ IndexedRulePresentationCategory.Presentation Unit where
  obj := presentation
  map := presentationMap
  map_id := presentationMap_id
  map_comp := presentationMap_comp

/-- For any binding signature and equations, authored rule occurrences map
functorially to retained nullary rule presentations at a chosen sort. -/
def authoredRuleFunctor {S : Signature} {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    RuleListEventEmbedding.Catalogue S M ⥤
      IndexedRulePresentationCategory.Presentation Unit :=
  (RuleListEventEmbedding.eventGraphFunctor E sort) ⋙
    (functor (V := termQPresheaf E sort))

/-- Interpreting authored rule occurrences as retained events and then as
their freely generated rule algebras is functorial. The equation theory and
term syntax are fixed; a larger operational catalogue adds constructors. -/
noncomputable def authoredFreeOperationalFunctor
    {S : Signature} {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    RuleListEventEmbedding.Catalogue S M ⥤
      IndexedOperationalPresentationCategory.Equipped Unit :=
  authoredRuleFunctor E sort ⋙
    IndexedOperationalPresentationCategory.freeFunctor

#print axioms presentationMap_event
#print axioms presentationMap_tree_injective
#print axioms presentationMap_reindexTree
#print axioms presentationMap_id
#print axioms presentationMap_comp

end Mettapedia.OSLF.Binding.EventGraphNullaryPresentationFunctor
