import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedBaseChange

/-!
# Base change and substitution of rule-local acted firing trees

Changing the binding model of a firing tree commutes with contextual
substitution: substituting and then translating gives the same tree as
translating and then substituting along the translated environment. Event
leaves compose their recorded substitution arrow; rule nodes substitute their
own local valuation and every premise under its binders.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCoherence

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment castEnv castEnv_heq substJudgment_castEnv mapJudgment_substJudgment
   heq_transport)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedBaseChange
  (pushState pushMap pushMap_comp pushOrbit pushOrbit_map)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedBaseChange
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel

variable {S : Signature}
variable (R : List (LocalRule S))
variable {A B : BindingCloneAlgebra.Algebra.{0} S}

/-! ## Event leaves -/

/-- Two uses of the same original generator are equal when their recorded
substitution arrows have the same environment, even across an equality of
the current states. -/
theorem orbit_heq_of_environment
    {Seed : (sort : S.Srt) → State B sort → Type}
    {sort : S.Srt} {original first second : State B sort}
    (seed : Seed sort original) (same : first = second)
    (f : original ⟶ first) (g : original ⟶ second)
    (environment : HEq f.environment g.environment) :
    HEq (Orbit.mk original seed f : Orbit B Seed first)
      (Orbit.mk original seed g : Orbit B Seed second) := by
  subst same
  have arrows : f = g := Map.ext B (eq_of_heq environment)
  subst arrows
  rfl

/-- Translating a substituted judgment's state is substituting the
translated state along the translated environment. -/
theorem pushState_substitute (h : FreeBindingClone.Hom A B)
    (judgment : Judgment A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ) :
    pushState h (ofJudgment A (substJudgment judgment σ)) =
      ofJudgment B (substJudgment (mapJudgment h judgment)
        (fun t v => h.raw.map (σ t v))) := by
  obtain ⟨Γ, sort, source, target⟩ := judgment
  change (State.mk Δ (h.raw.map (A.substitution.substitute σ source))
      (h.raw.map (A.substitution.substitute σ target)) : State B sort) =
    State.mk Δ
      (B.substitution.substitute (fun t v => h.raw.map (σ t v)) (h.raw.map source))
      (B.substitution.substitute (fun t v => h.raw.map (σ t v)) (h.raw.map target))
  rw [h.map_substitute, h.map_substitute]

/-- Base change of a substituted event use is the substitution of the
base-changed use along the translated environment. -/
theorem pushHole_mapHole
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    (judgment : Judgment A) (hole : Holes A Seed judgment)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier judgment.1 Δ) :
    HEq (pushHole h seedMap (substJudgment judgment σ)
        (IntrinsicScopedConditionalActedFree.mapHole A Seed judgment hole σ))
      (IntrinsicScopedConditionalActedFree.mapHole B TargetSeed (mapJudgment h judgment)
        (pushHole h seedMap judgment hole) (fun t v => h.raw.map (σ t v))) := by
  obtain ⟨original, seed, arrow⟩ := hole
  change HEq
    (Orbit.mk (pushState h original) (seedMap _ original seed)
        (pushMap h (arrow ≫ substitutionArrow A judgment σ)) :
      Orbit B TargetSeed (pushState h (ofJudgment A (substJudgment judgment σ))))
    (Orbit.mk (pushState h original) (seedMap _ original seed)
        (pushMap h arrow ≫ substitutionArrow B (mapJudgment h judgment)
          (fun t v => h.raw.map (σ t v))) :
      Orbit B TargetSeed (ofJudgment B (substJudgment (mapJudgment h judgment)
        (fun t v => h.raw.map (σ t v)))))
  refine orbit_heq_of_environment _ (pushState_substitute h judgment σ) _ _ ?_
  apply heq_of_eq
  funext s v
  exact h.map_substitute σ (arrow.environment s v)

/-! ## Whole trees -/

/-- Base change commutes with transport of a tree along a judgment equality. -/
theorem pushTree_transport
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    {first second : Judgment A} (equal : first = second)
    (tree : Tree R A Seed first) :
    pushTree R h seedMap second (equal ▸ tree) =
      congrArg (mapJudgment h) equal ▸ pushTree R h seedMap first tree := by
  cases equal
  rfl

/-- **Base change commutes with contextual substitution** of rule-local
firing trees with substitution-closed event leaves. -/
theorem pushTree_substitute
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    (judgment : Judgment A) (tree : Tree R A Seed judgment) :
    ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (target : Judgment A) (hs : substJudgment judgment σ = target),
      pushTree R h seedMap target (substitute R A Seed judgment tree σ target hs) =
        substitute R B TargetSeed (mapJudgment h judgment)
          (pushTree R h seedMap judgment tree)
          (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
          ((mapJudgment_substJudgment h judgment σ).symm.trans
            (congrArg (mapJudgment h) hs)) := by
  refine IndexedPolynomial.Fix.eliminate
    ((rules R A).withHoles (fun _ j => Holes A Seed j))
    (fun _ judgment tree => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (target : Judgment A) (hs : substJudgment judgment σ = target),
      pushTree R h seedMap target (substitute R A Seed judgment tree σ target hs) =
        substitute R B TargetSeed (mapJudgment h judgment)
          (pushTree R h seedMap judgment tree)
          (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
          ((mapJudgment_substJudgment h judgment σ).symm.trans
            (congrArg (mapJudgment h) hs)))
    ?_ () judgment tree
  intro base j shape children ih
  cases base
  cases shape with
  | inl hole =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      intro Δ σ target hs
      change pushTree R h seedMap target
          (substitute R A Seed j (IndexedPolynomial.Free.pure (rules R A) hole)
            σ target hs) =
        substitute R B TargetSeed (mapJudgment h j)
          (pushTree R h seedMap j (IndexedPolynomial.Free.pure (rules R A) hole))
          (fun t v => h.raw.map (σ t v)) (mapJudgment h target) _
      refine (congrArg (pushTree R h seedMap target)
        (substitute_pure R A Seed j hole σ target hs)).trans ?_
      refine (pushTree_transport R h seedMap hs _).trans ?_
      refine (congrArg (fun t => congrArg (mapJudgment h) hs ▸ t)
        (pushTree_pure R h seedMap _ _)).trans ?_
      refine (IndexedPolynomial.Free.pure_transport (rules R B)
        (holes := fun _ j => Holes B TargetSeed j) _ _).trans ?_
      refine Eq.trans ?_ (congrArg (fun t => substitute R B TargetSeed (mapJudgment h j) t
        (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
        ((mapJudgment_substJudgment h j σ).symm.trans (congrArg (mapJudgment h) hs)))
        (pushTree_pure R h seedMap j hole)).symm
      refine Eq.trans ?_ (IndexedPolynomial.Free.pure_transport (rules R B)
        (holes := fun _ j => Holes B TargetSeed j)
        ((mapJudgment_substJudgment h j σ).symm.trans (congrArg (mapJudgment h) hs))
        (IntrinsicScopedConditionalActedFree.mapHole B TargetSeed (mapJudgment h j)
          (pushHole h seedMap j hole) (fun t v => h.raw.map (σ t v)))).symm
      exact congrArg (IndexedPolynomial.Free.pure (rules R B))
        (eq_of_heq ((eqRec_heq _ _).trans
          ((pushHole_mapHole h seedMap j hole σ).trans (eqRec_heq _ _).symm)))
  | inr shape =>
      change (position : Fin (R.get shape.1.index).2.premises.length) →
        Tree R A Seed (childJudgment R A shape.1 position) at children
      change ∀ position, ∀ {Δ : Ctx S}
        (σ : Environment S A.substitution.Carrier
          (childJudgment R A shape.1 position).1 Δ)
        (target : Judgment A)
        (hs : substJudgment (childJudgment R A shape.1 position) σ = target),
        pushTree R h seedMap target
            (substitute R A Seed _ (children position) σ target hs) =
          substitute R B TargetSeed (mapJudgment h _)
            (pushTree R h seedMap _ (children position))
            (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
            ((mapJudgment_substJudgment h _ σ).symm.trans
              (congrArg (mapJudgment h) hs)) at ih
      obtain ⟨occurrence, hconc⟩ := shape
      subst hconc
      intro Δ σ target hs
      refine node_congr_instance R B TargetSeed
        (mapInstance_subst_transport R h occurrence σ _) _ _ _ _ ?_
      intro position otherPosition samePosition
      cases samePosition
      refine HEq.trans (heq_transport _ _) ?_
      refine HEq.trans (heq_of_eq (ih position _ _ _)) ?_
      exact substitute_heq R B TargetSeed (mapInstance_child R h occurrence position).symm
        (heq_transport _ _).symm (liftEnvironment_mapInstance R h occurrence σ _ position)
        (childJudgment_mapInstance_subst R h occurrence σ _ position) _ _

/-! ## Functoriality in the binding model -/

/-- The identity binding map fixes every event use. -/
theorem pushHole_id
    {Seed : (sort : S.Srt) → State A sort → Type}
    (judgment : Judgment A) (hole : Holes A Seed judgment) :
    pushHole (FreeBindingClone.Hom.id A) (fun _ _ seed => seed) judgment hole = hole := by
  obtain ⟨original, seed, arrow⟩ := hole
  rfl

/-- The identity binding map fixes every firing tree. -/
theorem pushTree_id
    {Seed : (sort : S.Srt) → State A sort → Type}
    (judgment : Judgment A) (tree : Tree R A Seed judgment) :
    pushTree R (FreeBindingClone.Hom.id A) (fun _ _ seed => seed) judgment tree = tree := by
  exact IndexedRuleFreeTransport.mapFree_id (rules R A) (fun _ j => Holes A Seed j)
    () judgment tree

/-- Two successive binding maps act on firing trees as their composite. -/
theorem pushTree_comp
    {C : BindingCloneAlgebra.Algebra.{0} S}
    {Seed : (sort : S.Srt) → State A sort → Type}
    {MiddleSeed : (sort : S.Srt) → State B sort → Type}
    {TargetSeed : (sort : S.Srt) → State C sort → Type}
    (first : FreeBindingClone.Hom A B) (second : FreeBindingClone.Hom B C)
    (firstSeed : ∀ sort (state : State A sort),
      Seed sort state → MiddleSeed sort (pushState first state))
    (secondSeed : ∀ sort (state : State B sort),
      MiddleSeed sort state → TargetSeed sort (pushState second state))
    (judgment : Judgment A) (tree : Tree R A Seed judgment) :
    pushTree R (FreeBindingClone.Hom.comp first second)
        (fun sort state seed => secondSeed sort (pushState first state)
          (firstSeed sort state seed)) judgment tree =
      pushTree R second secondSeed (mapJudgment first judgment)
        (pushTree R first firstSeed judgment tree) :=
  IndexedRuleFreeTransport.mapFree_comp (presentationMap R first).rules
    (presentationMap R second).rules
    (fun _ j event => pushHole first firstSeed j event)
    (fun _ j event => pushHole second secondSeed j event) () judgment tree

/-! ## Interpretations along a change of binding model -/

/-- Read a natural interpretation of event uses along a base map: a use is
interpreted as its base-changed use. -/
noncomputable def _root_.Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree.NaturalAssignment.pullback
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    {model : SubstitutionModel R B} (assigned : NaturalAssignment R B TargetSeed model) :
    NaturalAssignment R A Seed (model.pullback h) where
  value judgment hole := assigned.value (mapJudgment h judgment) (pushHole h seedMap judgment hole)
  map := by
    intro judgment hole Δ σ target same
    subst same
    refine Eq.trans ?_ (assigned.map (mapJudgment h judgment) (pushHole h seedMap judgment hole)
      (fun t v => h.raw.map (σ t v)) (mapJudgment h (substJudgment judgment σ))
      (mapJudgment_substJudgment h judgment σ).symm)
    exact eq_of_heq ((assigned.value_heq R B TargetSeed (mapJudgment_substJudgment h judgment σ)
      (pushHole_mapHole h seedMap judgment hole σ)).trans (heq_transport _ _).symm)

/-- **Interpreting a base-changed tree is interpreting the tree in the model
read along the base map.** -/
theorem interpret_pushTree
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    {model : SubstitutionModel R B} (assigned : NaturalAssignment R B TargetSeed model)
    (judgment : Judgment A) (tree : Tree R A Seed judgment) :
    interpret R B TargetSeed model assigned (mapJudgment h judgment)
        (pushTree R h seedMap judgment tree) =
      interpret R A Seed (model.pullback h) (assigned.pullback R h seedMap) judgment tree :=
  IndexedRuleFreeSubstitutionNaturality.fold_mapFree (rulesMap R h) model.rules
    (fun _ judgment hole => pushHole h seedMap judgment hole)
    (fun _ judgment hole => assigned.value judgment hole) () judgment tree

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCoherence
