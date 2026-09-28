import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalActedFiniteContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFreeGenerators
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFiniteContextChange

/-!
# Changing the binding base of substitution-closed events

A binding-clone map transports the original event judgment, its ordinary-
variable substitution, and the complete authored firing tree. Retaining the
substitution arrow is essential when two program judgments become equal after
the base change while their event positions remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedBaseChange

open Mettapedia.TypeTheory
open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedFree
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedFiniteContext
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFreeGenerators
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextChange
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton (ListContext)

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable {A B : BindingCloneAlgebra.Algebra.{0} S}

/-- Translate both endpoints of a fixed-sort contextual judgment. -/
def pushState (h : FreeBindingClone.Hom A B)
    {sort : S.Srt} (state : State A sort) : State B sort :=
  ⟨state.context, h.raw.map state.source, h.raw.map state.target⟩

/-- A contextual substitution is translated pointwise through the base map.
The endpoint equations follow from the clone substitution law. -/
def pushMap (h : FreeBindingClone.Hom A B)
    {sort : S.Srt} {first second : State A sort}
    (f : first ⟶ second) : pushState h first ⟶ pushState h second where
  environment := fun s v => h.raw.map (f.environment s v)
  sourceEq := by
    change B.substitution.substitute (fun s v => h.raw.map (f.environment s v))
        (h.raw.map first.source) = h.raw.map second.source
    rw [← h.map_substitute, f.sourceEq]
  targetEq := by
    change B.substitution.substitute (fun s v => h.raw.map (f.environment s v))
        (h.raw.map first.target) = h.raw.map second.target
    rw [← h.map_substitute, f.targetEq]

/-- Base change preserves the identity contextual substitution. -/
theorem pushMap_id (h : FreeBindingClone.Hom A B)
    {sort : S.Srt} (state : State A sort) :
    pushMap h (𝟙 state) = 𝟙 (pushState h state) := by
  apply Map.ext B
  funext s v
  exact h.raw.map_variable v

/-- Base change preserves composition of contextual substitutions. -/
theorem pushMap_comp (h : FreeBindingClone.Hom A B)
    {sort : S.Srt} {first middle last : State A sort}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    pushMap h (f ≫ g) = pushMap h f ≫ pushMap h g := by
  apply Map.ext B
  funext s v
  exact h.map_substitute g.environment (f.environment s v)

/-- The contextual judgment map itself is functorial. -/
noncomputable def pushStateFunctor (h : FreeBindingClone.Hom A B)
    (sort : S.Srt) : State A sort ⥤ State B sort where
  obj := pushState h
  map := pushMap h
  map_id := pushMap_id h
  map_comp := pushMap_comp h

/-- Identity binding interpretation leaves contextual judgment transport
unchanged, including the environment on each arrow. -/
theorem pushStateFunctor_id
    (A : BindingCloneAlgebra.Algebra.{0} S) (sort : S.Srt) :
    pushStateFunctor (FreeBindingClone.Hom.id A) sort =
      𝟭 (State A sort) := by
  refine CategoryTheory.Functor.hext (fun state => rfl) ?_
  intro first second arrow
  exact heq_of_eq (by
    apply Map.ext A
    rfl)

/-- Successive binding interpretations compose on full contextual
judgment arrows, not merely on their endpoint pairs. -/
theorem pushStateFunctor_comp
    {C : BindingCloneAlgebra.Algebra.{0} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C) (sort : S.Srt) :
    pushStateFunctor (FreeBindingClone.Hom.comp first second) sort =
      pushStateFunctor first sort ⋙ pushStateFunctor second sort := by
  refine CategoryTheory.Functor.hext (fun state => rfl) ?_
  intro source target arrow
  exact heq_of_eq (by
    apply Map.ext C
    rfl)

/-- Transport an event occurrence without forgetting either its origin or
the substitution arrow through which it is used. -/
noncomputable def pushOrbit
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    {sort : S.Srt} {state : State A sort}
    (event : Orbit A Seed state) :
    Orbit B TargetSeed (pushState h state) where
  original := pushState h event.original
  seed := seedMap sort event.original event.seed
  arrow := pushMap h event.arrow

theorem pushOrbit_unit
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    {sort : S.Srt} {state : State A sort} (seed : Seed sort state) :
    pushOrbit h seedMap (Orbit.unit A Seed seed) =
      Orbit.unit B TargetSeed (seedMap sort state seed) := by
  change Orbit.mk (pushState h state) (seedMap sort state seed)
      (pushMap h (𝟙 state)) =
    Orbit.mk (pushState h state) (seedMap sort state seed)
      (𝟙 (pushState h state))
  rw [pushMap_id]

/-- Base change commutes with a further ordinary-variable substitution of
the same individual firing witness. -/
theorem pushOrbit_map
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    {sort : S.Srt} {first second : State A sort}
    (event : Orbit A Seed first) (f : first ⟶ second) :
    pushOrbit h seedMap (event.map A Seed f) =
      (pushOrbit h seedMap event).map B TargetSeed (pushMap h f) := by
  cases event with
  | mk original seed arrow =>
      change Orbit.mk (pushState h original) (seedMap sort original seed)
          (pushMap h (arrow ≫ f)) =
        Orbit.mk (pushState h original) (seedMap sort original seed)
          (pushMap h arrow ≫ pushMap h f)
      rw [pushMap_comp]

/-- Transport of substitution-closed event generators is natural over the
whole contextual judgment category. This is the leaf-level base-change law
needed by the operational classifier. -/
noncomputable def pushOrbitNat
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    (sort : S.Srt) :
    freeAction A Seed sort ⟶
      pushStateFunctor h sort ⋙ freeAction B TargetSeed sort where
  app state := TypeCat.ofHom (pushOrbit h seedMap)
  naturality := by
    intro first second f
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact pushOrbit_map h seedMap event f

/-- Change the program base of a complete substitution-closed firing tree.
Authored rule nodes and their ordered premise positions use the existing
polynomial presentation map. -/
noncomputable def pushTree
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    (judgment : Judgment A) :
    Tree R A Seed judgment → Tree R B TargetSeed (mapJudgment h judgment) :=
  mapFreeWithEvents R h
    (fun judgment event => by
      have same : pushState h (ofJudgment A judgment) =
          ofJudgment B (mapJudgment h judgment) := rfl
      exact Eq.mp
        (congrArg (fun st : State B judgment.2.1 =>
          Orbit B TargetSeed st) same)
        (pushOrbit h seedMap event))
    judgment

/-- Finite-list base change keeps the position of each original event
variable, even if its program endpoints are identified by the base map. -/
def pushSeed (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A))
    {sort : S.Srt} {state : State A sort}
    (seed : seeds R A Γ sort state) :
    seeds R B (pushContext R h Γ) sort (pushState h state) :=
  pushSlot R h Γ seed

/-- A noninjective program interpretation may merge endpoint judgments,
but it cannot merge distinct original event positions. -/
theorem pushSeed_injective (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A))
    {sort : S.Srt} (state : State A sort) :
    Function.Injective (pushSeed R h Γ (state := state)) :=
  pushSlot_injective R h Γ (state.asJudgment A)

/-- Change the binding base of a finite event context while retaining its
substitution-closed arrow language. -/
noncomputable def pushFiniteTree
    (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) (judgment : Judgment A) :
    IntrinsicScopedConditionalActedFiniteContext.Term R A Γ judgment →
      IntrinsicScopedConditionalActedFiniteContext.Term R B
        (pushContext R h Γ) (mapJudgment h judgment) :=
  pushTree R h (fun _ _ seed => pushSeed R h Γ seed) judgment

/-- Base change of an event leaf maps its original generator and recorded
substitution arrow, without inserting a rule constructor. -/
theorem pushFiniteTree_pure
    (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A))
    (judgment : Judgment A)
    (hole : Holes A (seeds R A Γ) judgment) :
    pushFiniteTree R h Γ judgment
        (IndexedPolynomial.Free.pure (rules R A) hole) =
      IndexedPolynomial.Free.pure (rules R B)
        (Eq.mp (congrArg
          (fun st : State B judgment.2.1 =>
            Orbit B (seeds R B (pushContext R h Γ)) st)
          (show pushState h (ofJudgment A judgment) =
            ofJudgment B (mapJudgment h judgment) from rfl))
          (pushOrbit h (fun _ _ seed => pushSeed R h Γ seed) hole)) := by
  exact mapFreeWithEvents_existing R h _ hole

/-- Every authored constructor keeps its rule identity and ordered premise
positions while its children are translated under their own local binders. -/
theorem pushFiniteTree_node
    (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A))
    {judgment : Judgment A}
    (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).premises.length,
      IntrinsicScopedConditionalActedFiniteContext.Term R A Γ
        (childJudgment R A shape.1 position)) :
    pushFiniteTree R h Γ judgment
        (IndexedPolynomial.Free.node (rules R A) shape children) =
      IndexedPolynomial.Free.node (rules R B)
        ((presentationMap R h).rules.onShape PUnit.unit judgment shape)
        (fun position =>
          ((presentationMap R h).rules.onNext PUnit.unit judgment shape
              position).symm ▸
            pushFiniteTree R h Γ _
              (children (((presentationMap R h).rules.onPosition
                PUnit.unit judgment shape) position))) := by
  exact IndexedRuleFreeTransport.mapFree_node
    (presentationMap R h).rules _ shape children

/-- Translate a simultaneous assignment of event variables through a
binding-clone map. A target slot is read by its original finite-list
position before the assigned tree is translated. -/
noncomputable def pushFiniteArrow
    (h : FreeBindingClone.Hom A B)
    {Γ Δ : ListContext (rules R A)}
    (assignment :
      IntrinsicScopedConditionalActedFiniteContext.Hom R A ⟨Γ⟩ ⟨Δ⟩) :
    IntrinsicScopedConditionalActedFiniteContext.Hom R B
      ⟨pushContext R h Γ⟩ ⟨pushContext R h Δ⟩ :=
  fun _ _ => fun
    | ⟨position, ⟨equal⟩⟩ =>
        equal ▸ pushFiniteTree R h Γ (Δ.label position)
          (assignment _ (ofJudgment A (Δ.label position))
            ⟨position, ⟨rfl⟩⟩)

/-- At each original target position, the translated assignment is exactly
the translation of the original assigned tree. -/
theorem pushFiniteArrow_position
    (h : FreeBindingClone.Hom A B)
    {Γ Δ : ListContext (rules R A)}
    (assignment :
      IntrinsicScopedConditionalActedFiniteContext.Hom R A ⟨Γ⟩ ⟨Δ⟩)
    (position : Fin Δ.length) :
    pushFiniteArrow R h assignment _
        (ofJudgment B (mapJudgment h (Δ.label position)))
        ⟨position, ⟨rfl⟩⟩ =
      pushFiniteTree R h Γ (Δ.label position)
        (assignment _ (ofJudgment A (Δ.label position))
          ⟨position, ⟨rfl⟩⟩) := by
  rfl

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedBaseChange
