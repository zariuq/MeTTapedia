import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalActedFree
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalSubstitutionModel

/-!
# Rule-local trees with substitution-closed event variables

The selected authored rule determines its own metavariable telescope. Event
leaves retain their origin and ordinary-variable substitution arrow. This
joins the rule-local constructor family with the substitution-closed event
interface without adding assignments to unrelated rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution hiding SubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (JudgmentAction)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open CategoryTheory

variable {S : Signature}
variable (R : List (LocalRule S))
variable (A : BindingCloneAlgebra.Algebra.{0} S)
variable (Seed : (sort : S.Srt) → State A sort → Type)

/-- A retained firing variable may be used after a contextual substitution. -/
abbrev Holes (judgment : Judgment A) : Type :=
  Orbit A Seed (ofJudgment A judgment)

/-- Firing trees whose rule nodes have local parameter telescopes and whose
leaves retain individual substitution-sensitive event generators. -/
abbrev Tree (judgment : Judgment A) : Type :=
  (rules R A).Free (fun _ j => Holes A Seed j) () judgment

/-- A bare event variable has no added rule node or environment change. -/
noncomputable def generator {sort : S.Srt} {state : State A sort}
    (seed : Seed sort state) : Tree R A Seed (state.asJudgment A) :=
  IndexedPolynomial.Free.pure (rules R A)
    ((State.of_as A state).symm ▸ Orbit.unit A Seed seed)

/-- Substitution acts on each local rule occurrence and each retained event
leaf. Under a premise it lifts the environment through that premise's own
binder list. -/
noncomputable def substitute :
    ∀ (judgment : Judgment A), Tree R A Seed judgment →
      ∀ {Δ : Ctx S}
        (σ : Environment S A.substitution.Carrier judgment.1 Δ)
        (target : Judgment A), substJudgment judgment σ = target →
          Tree R A Seed target :=
  IndexedPolynomial.Fix.eliminate
    ((rules R A).withHoles (fun _ j => Holes A Seed j))
    (fun _ judgment _ => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (target : Judgment A), substJudgment judgment σ = target →
        Tree R A Seed target)
    (fun _ judgment shape _children results {_} σ target h =>
      match shape with
      | .inl hole =>
          h ▸ IndexedPolynomial.Free.pure (rules R A)
            (IntrinsicScopedConditionalActedFree.mapHole A Seed judgment hole σ)
      | .inr rule =>
          IndexedPolynomial.Free.node (rules R A)
            (⟨Instance.subst R rule.1 (castEnv rule.2 σ),
              (conclusionJudgment_subst R rule.1 (castEnv rule.2 σ)).trans
                ((substJudgment_castEnv rule.2 σ).trans h)⟩ :
              Shape R A target)
            (fun position => results position
              (A.substitution.liftEnvironment (castEnv rule.2 σ)
                ((R.get rule.1.index).2.premises.get position).binders)
              (childJudgment R A (Instance.subst R rule.1
                (castEnv rule.2 σ)) position)
              (childJudgment_subst R rule.1 (castEnv rule.2 σ)
                position).symm))
    ()

/-- On a variable leaf, the action composes that variable's stored
substitution arrow with the new environment. -/
theorem substitute_pure (judgment : Judgment A)
    (hole : Holes A Seed judgment) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ)
    (target : Judgment A) (h : substJudgment judgment σ = target) :
    substitute R A Seed judgment
        (IndexedPolynomial.Free.pure (rules R A) hole) σ target h =
      h ▸ IndexedPolynomial.Free.pure (rules R A)
        (IntrinsicScopedConditionalActedFree.mapHole A Seed judgment hole σ) := rfl

/-- On an authored rule node, the action substitutes only its selected
rule-local valuation and visits every ordered premise under its binders. -/
theorem substitute_node {judgment : Judgment A}
    (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Tree R A Seed (childJudgment R A shape.1 position))
    {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ)
    (target : Judgment A) (h : substJudgment judgment σ = target) :
    substitute R A Seed judgment
        (IndexedPolynomial.Free.node (rules R A) shape children) σ target h =
      IndexedPolynomial.Free.node (rules R A)
        (⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans h)⟩ :
          Shape R A target)
        (fun position => substitute R A Seed _ (children position)
          (A.substitution.liftEnvironment (castEnv shape.2 σ)
            ((R.get shape.1.index).2.premises.get position).binders)
          (childJudgment R A (Instance.subst R shape.1
            (castEnv shape.2 σ)) position)
          (childJudgment_subst R shape.1 (castEnv shape.2 σ)
            position).symm) := rfl

/-- Equality of rule occurrences and their ordered children determines a
free constructor, independently of endpoint proof witnesses. -/
theorem node_congr_instance
    {target : Judgment A} {first second : Instance R A}
    (same : first = second)
    (firstConclusion : conclusionJudgment R A first = target)
    (secondConclusion : conclusionJudgment R A second = target)
    (firstChildren : ∀ position : Fin (R.get first.index).2.premises.length,
      Tree R A Seed (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).2.premises.length,
      Tree R A Seed (childJudgment R A second position))
    (children : ∀ firstPosition secondPosition,
      HEq firstPosition secondPosition →
        HEq (firstChildren firstPosition) (secondChildren secondPosition)) :
    (IndexedPolynomial.Free.node (rules R A)
        (⟨first, firstConclusion⟩ : Shape R A target) firstChildren :
      Tree R A Seed target) =
      IndexedPolynomial.Free.node (rules R A)
        (⟨second, secondConclusion⟩ : Shape R A target) secondChildren := by
  subst same
  have childrenEq : firstChildren = secondChildren :=
    funext fun position => eq_of_heq (children position position HEq.rfl)
  subst childrenEq
  rfl

/-- Tree substitution respects equal environments and target judgments;
the endpoint equality proofs themselves are irrelevant. -/
theorem substitute_congr
    {judgment : Judgment A} (tree : Tree R A Seed judgment) {Δ : Ctx S}
    {σ₁ σ₂ : Environment S A.substitution.Carrier judgment.1 Δ}
    (sameEnv : σ₁ = σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment judgment σ₁ = target₁)
    (h₂ : substJudgment judgment σ₂ = target₂) :
    HEq (substitute R A Seed judgment tree σ₁ target₁ h₁)
      (substitute R A Seed judgment tree σ₂ target₂ h₂) := by
  subst sameEnv
  subst sameTarget
  rfl

/-- Heterogeneous congruence permits indexed child transports through
binder-local premise judgments. -/
theorem substitute_heq
    {judgment₁ judgment₂ : Judgment A}
    (sameJudgment : judgment₁ = judgment₂)
    {tree₁ : Tree R A Seed judgment₁}
    {tree₂ : Tree R A Seed judgment₂} (sameTree : HEq tree₁ tree₂)
    {Δ : Ctx S}
    {σ₁ : Environment S A.substitution.Carrier judgment₁.1 Δ}
    {σ₂ : Environment S A.substitution.Carrier judgment₂.1 Δ}
    (sameEnv : HEq σ₁ σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment judgment₁ σ₁ = target₁)
    (h₂ : substJudgment judgment₂ σ₂ = target₂) :
    HEq (substitute R A Seed judgment₁ tree₁ σ₁ target₁ h₁)
      (substitute R A Seed judgment₂ tree₂ σ₂ target₂ h₂) := by
  subst sameJudgment
  cases sameTree
  cases sameEnv
  subst sameTarget
  rfl

/-- The identity environment fixes every event leaf and every scoped rule
node of the free tree. -/
theorem substitute_identity (judgment : Judgment A)
    (tree : Tree R A Seed judgment) :
    ∀ (h : substJudgment judgment
        (fun _ v => A.substitution.injectVar v) = judgment),
      substitute R A Seed judgment tree
        (fun _ v => A.substitution.injectVar v) judgment h = tree := by
  refine IndexedPolynomial.Fix.eliminate
    ((rules R A).withHoles (fun _ j => Holes A Seed j))
    (fun _ judgment tree => ∀ (h : substJudgment judgment
        (fun _ v => A.substitution.injectVar v) = judgment),
      substitute R A Seed judgment tree
        (fun _ v => A.substitution.injectVar v) judgment h = tree)
    ?_ () judgment tree
  intro base j shape children ih
  cases base
  cases shape with
  | inl hole =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      intro h
      change substitute R A Seed j
          (IndexedPolynomial.Free.pure (rules R A) hole)
          (fun _ v => A.substitution.injectVar v) j h =
        IndexedPolynomial.Free.pure (rules R A) hole
      rw [substitute_pure, IndexedPolynomial.Free.pure_transport (rules R A),
        IntrinsicScopedConditionalActedFree.mapHole_identity A Seed j hole h]
  | inr shape =>
      change (position : Fin (R.get shape.1.index).2.premises.length) →
        Tree R A Seed (childJudgment R A shape.1 position) at children
      change ∀ position, ∀ (h : substJudgment
          (childJudgment R A shape.1 position)
          (fun _ v => A.substitution.injectVar v) =
          childJudgment R A shape.1 position),
        substitute R A Seed _ (children position)
          (fun _ v => A.substitution.injectVar v) _ h =
          children position at ih
      intro h
      obtain ⟨occurrence, hconc⟩ := shape
      subst hconc
      refine node_congr_instance R A Seed
        (Instance.subst_identity R occurrence) _ _ _ _ ?_
      intro position otherPosition samePosition
      cases samePosition
      have envEq :
          A.substitution.liftEnvironment
              (fun _ v => A.substitution.injectVar v :
                Environment S A.substitution.Carrier
                  occurrence.ambient occurrence.ambient)
              ((R.get occurrence.index).2.premises.get position).binders =
            (fun _ v => A.substitution.injectVar v) :=
        liftEnvironment_injectVar A.substitution _
      have targetEq :
          childJudgment R A
              (Instance.subst R occurrence
                (fun _ v => A.substitution.injectVar v)) position =
            childJudgment R A occurrence position :=
        (childJudgment_subst R occurrence _ position).trans
          ((congrArg
              (substJudgment (childJudgment R A occurrence position))
              (liftEnvironment_injectVar A.substitution _)).trans
            (substJudgment_identity _))
      exact (substitute_congr R A Seed (children position) envEq
        targetEq _ (substJudgment_identity _)).trans
        (heq_of_eq (ih position (substJudgment_identity _)))

/-- Two successive contextual substitutions of a free event/rule tree
agree with one substitution along their composite environment. -/
theorem substitute_comp (judgment : Judgment A)
    (tree : Tree R A Seed judgment) :
    ∀ {Δ Θ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (τ : Environment S A.substitution.Carrier Δ Θ)
      (target : Judgment A)
      (hSecond : substJudgment (substJudgment judgment σ) τ = target)
      (hDirect : substJudgment judgment
        (fun s v => A.substitution.substitute τ (σ s v)) = target),
      substitute R A Seed (substJudgment judgment σ)
          (substitute R A Seed judgment tree σ
            (substJudgment judgment σ) rfl) τ target hSecond =
        substitute R A Seed judgment tree
          (fun s v => A.substitution.substitute τ (σ s v)) target hDirect := by
  refine IndexedPolynomial.Fix.eliminate
    ((rules R A).withHoles (fun _ j => Holes A Seed j))
    (fun _ judgment tree => ∀ {Δ Θ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (τ : Environment S A.substitution.Carrier Δ Θ)
      (target : Judgment A)
      (hSecond : substJudgment (substJudgment judgment σ) τ = target)
      (hDirect : substJudgment judgment
        (fun s v => A.substitution.substitute τ (σ s v)) = target),
      substitute R A Seed (substJudgment judgment σ)
          (substitute R A Seed judgment tree σ
            (substJudgment judgment σ) rfl) τ target hSecond =
        substitute R A Seed judgment tree
          (fun s v => A.substitution.substitute τ (σ s v)) target hDirect)
    ?_ () judgment tree
  intro base j shape children ih
  cases base
  cases shape with
  | inl hole =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      intro Δ Θ σ τ target hSecond hDirect
      change substitute R A Seed (substJudgment j σ)
          (substitute R A Seed j
            (IndexedPolynomial.Free.pure (rules R A) hole)
            σ (substJudgment j σ) rfl) τ target hSecond =
        substitute R A Seed j
          (IndexedPolynomial.Free.pure (rules R A) hole)
          (fun s v => A.substitution.substitute τ (σ s v))
          target hDirect
      rw [substitute_pure]
      change substitute R A Seed (substJudgment j σ)
          (IndexedPolynomial.Free.pure (rules R A)
            (IntrinsicScopedConditionalActedFree.mapHole A Seed j hole σ)) τ target hSecond = _
      rw [substitute_pure R A Seed (substJudgment j σ)
        (IntrinsicScopedConditionalActedFree.mapHole A Seed j hole σ) τ target hSecond]
      rw [substitute_pure R A Seed j hole
        (fun s v => A.substitution.substitute τ (σ s v))
        target hDirect]
      rw [IndexedPolynomial.Free.pure_transport (rules R A), IndexedPolynomial.Free.pure_transport (rules R A)]
      have holeEq : HEq
          (IntrinsicScopedConditionalActedFree.mapHole A Seed (substJudgment j σ)
            (IntrinsicScopedConditionalActedFree.mapHole A Seed j hole σ) τ)
          (IntrinsicScopedConditionalActedFree.mapHole A Seed j hole
            (fun s v => A.substitution.substitute τ (σ s v))) :=
        IntrinsicScopedConditionalActedFree.mapHole_comp_heq A Seed j hole σ τ
      have leftCast : HEq
          (hSecond ▸ IntrinsicScopedConditionalActedFree.mapHole A Seed (substJudgment j σ)
            (IntrinsicScopedConditionalActedFree.mapHole A Seed j hole σ) τ)
          (IntrinsicScopedConditionalActedFree.mapHole A Seed (substJudgment j σ)
            (IntrinsicScopedConditionalActedFree.mapHole A Seed j hole σ) τ) :=
        eqRec_heq hSecond _
      have rightCast : HEq
          (hDirect ▸ IntrinsicScopedConditionalActedFree.mapHole A Seed j hole
            (fun s v => A.substitution.substitute τ (σ s v)))
          (IntrinsicScopedConditionalActedFree.mapHole A Seed j hole
            (fun s v => A.substitution.substitute τ (σ s v))) :=
        eqRec_heq hDirect _
      exact congrArg (IndexedPolynomial.Free.pure (rules R A))
        (eq_of_heq (leftCast.trans (holeEq.trans rightCast.symm)))
  | inr shape =>
      change (position : Fin (R.get shape.1.index).2.premises.length) →
        Tree R A Seed (childJudgment R A shape.1 position) at children
      change ∀ position, ∀ {Δ Θ : Ctx S}
        (σ : Environment S A.substitution.Carrier
          (childJudgment R A shape.1 position).1 Δ)
        (τ : Environment S A.substitution.Carrier Δ Θ)
        (target : Judgment A)
        (hSecond : substJudgment
          (substJudgment (childJudgment R A shape.1 position) σ) τ = target)
        (hDirect : substJudgment (childJudgment R A shape.1 position)
          (fun s v => A.substitution.substitute τ (σ s v)) = target),
        substitute R A Seed
            (substJudgment (childJudgment R A shape.1 position) σ)
            (substitute R A Seed _ (children position) σ _ rfl) τ target
            hSecond =
          substitute R A Seed _ (children position)
            (fun s v => A.substitution.substitute τ (σ s v)) target
            hDirect at ih
      intro Δ Θ σ τ target hSecond hDirect
      obtain ⟨occurrence, hconc⟩ := shape
      subst hconc
      have envEq : ∀ (pf : conclusionJudgment R A
          (Instance.subst R occurrence σ) =
          substJudgment (conclusionJudgment R A occurrence) σ),
          castEnv pf τ = τ :=
        fun pf => eq_of_heq (castEnv_heq pf τ)
      have instanceEq : ∀ (pf : conclusionJudgment R A
          (Instance.subst R occurrence σ) =
          substJudgment (conclusionJudgment R A occurrence) σ),
          Instance.subst R (Instance.subst R occurrence σ)
            (castEnv pf τ) =
          Instance.subst R occurrence
            (fun s v => A.substitution.substitute τ (σ s v)) := by
        intro pf
        rw [envEq pf]
        exact Instance.subst_comp R occurrence σ τ
      refine node_congr_instance R A Seed (instanceEq _) _ _ _ _ ?_
      intro position otherPosition samePosition
      cases samePosition
      have firstChild :
          childJudgment R A (Instance.subst R occurrence σ) position =
          substJudgment (childJudgment R A occurrence position)
            (A.substitution.liftEnvironment σ
              ((R.get occurrence.index).2.premises.get position).binders) :=
        childJudgment_subst R occurrence σ position
      have liftComp :
          (fun s v => A.substitution.substitute
            (A.substitution.liftEnvironment τ
              ((R.get occurrence.index).2.premises.get position).binders)
            (A.substitution.liftEnvironment σ
              ((R.get occurrence.index).2.premises.get position).binders s v)) =
          A.substitution.liftEnvironment
            (fun s v => A.substitution.substitute τ (σ s v))
            ((R.get occurrence.index).2.premises.get position).binders := by
        funext s v
        exact substitute_liftEnvironment A.substitution τ σ _ v
      have directChild :
          substJudgment
            (substJudgment (childJudgment R A occurrence position)
              (A.substitution.liftEnvironment σ
                ((R.get occurrence.index).2.premises.get position).binders))
            (A.substitution.liftEnvironment τ
              ((R.get occurrence.index).2.premises.get position).binders) =
          childJudgment R A
            (Instance.subst R occurrence
              (fun s v => A.substitution.substitute τ (σ s v))) position :=
        (substJudgment_comp _ _ _).trans
          ((congrArg (substJudgment
            (childJudgment R A occurrence position)) liftComp).trans
            (childJudgment_subst R occurrence _ position).symm)
      have directOnce :
          substJudgment (childJudgment R A occurrence position)
            (fun s v => A.substitution.substitute
              (A.substitution.liftEnvironment τ
                ((R.get occurrence.index).2.premises.get position).binders)
              (A.substitution.liftEnvironment σ
                ((R.get occurrence.index).2.premises.get position).binders s v)) =
          childJudgment R A
            (Instance.subst R occurrence
              (fun s v => A.substitution.substitute τ (σ s v))) position :=
        (congrArg (substJudgment
          (childJudgment R A occurrence position)) liftComp).trans
            (childJudgment_subst R occurrence _ position).symm
      refine HEq.trans (substitute_heq R A Seed firstChild
          (substitute_congr R A Seed (children position) rfl firstChild
            _ rfl)
          (heq_of_eq (congrArg
            (fun env => A.substitution.liftEnvironment env
              ((R.get occurrence.index).2.premises.get position).binders)
            (envEq _)))
          (childJudgment_congr R (instanceEq _) position position HEq.rfl)
          _ directChild) ?_
      refine HEq.trans (heq_of_eq (ih position
        (A.substitution.liftEnvironment σ
          ((R.get occurrence.index).2.premises.get position).binders)
        (A.substitution.liftEnvironment τ
          ((R.get occurrence.index).2.premises.get position).binders)
        _ directChild directOnce)) ?_
      exact substitute_congr R A Seed (children position) liftComp rfl _ _


/-- The substitution-closed rule-local trees form an operational model. -/
noncomputable def freeModel : SubstitutionModel.{0, 0} R A where
  carrier := fun judgment => Tree R A Seed judgment
  rules := IndexedPolynomial.Free.algebra (rules R A)
  act := substitute R A Seed
  act_rules := by
    intro judgment shape children Δ σ target h
    rfl
  act_identity := substitute_identity R A Seed
  act_comp := substitute_comp R A Seed

/-- A map on event-variable uses must commute with their stored ordinary-
variable substitution arrows. -/
structure NaturalAssignment (model : SubstitutionModel R A) where
  value : ∀ judgment : Judgment A,
    Holes A Seed judgment → model.carrier judgment
  map : ∀ (judgment : Judgment A) (hole : Holes A Seed judgment)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier judgment.1 Δ)
    (target : Judgment A) (h : substJudgment judgment σ = target),
    h ▸ value (substJudgment judgment σ)
      (IntrinsicScopedConditionalActedFree.mapHole A Seed judgment hole σ) =
        model.act judgment (value judgment hole) σ target h

/-- Fold rule-local firing trees using the target's actual rule actions. -/
noncomputable def interpret
    (model : SubstitutionModel R A)
    (assigned : NaturalAssignment R A Seed model) :
    ∀ judgment : Judgment A,
      Tree R A Seed judgment → model.carrier judgment :=
  IndexedPolynomial.Free.fold (rules R A)
    (fun _ judgment hole => assigned.value judgment hole)
    model.rules ()

theorem interpret_pure
    (model : SubstitutionModel R A)
    (assigned : NaturalAssignment R A Seed model)
    (judgment : Judgment A) (hole : Holes A Seed judgment) :
    interpret R A Seed model assigned judgment
        (IndexedPolynomial.Free.pure (rules R A) hole) =
      assigned.value judgment hole := rfl

theorem interpret_node
    (model : SubstitutionModel R A)
    (assigned : NaturalAssignment R A Seed model)
    {judgment : Judgment A} (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Tree R A Seed (childJudgment R A shape.1 position)) :
    interpret R A Seed model assigned judgment
        (IndexedPolynomial.Free.node (rules R A) shape children) =
      model.rules.act () judgment
        ⟨shape, fun position =>
          interpret R A Seed model assigned _ (children position)⟩ := rfl

private theorem interpret_cast
    (model : SubstitutionModel R A)
    (assigned : NaturalAssignment R A Seed model)
    {first second : Judgment A} (equal : first = second)
    (tree : Tree R A Seed first) :
    interpret R A Seed model assigned second (equal ▸ tree) =
      equal ▸ interpret R A Seed model assigned first tree := by
  cases equal
  rfl

/-- The free-tree interpretation preserves contextual substitution on
individual event leaves and on authored rule constructors. -/
theorem interpret_substitute
    (model : SubstitutionModel R A)
    (assigned : NaturalAssignment R A Seed model)
    (judgment : Judgment A) (tree : Tree R A Seed judgment) :
    ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (target : Judgment A) (h : substJudgment judgment σ = target),
      interpret R A Seed model assigned target
          (substitute R A Seed judgment tree σ target h) =
        model.act judgment
          (interpret R A Seed model assigned judgment tree) σ target h := by
  refine IndexedPolynomial.Fix.eliminate
    ((rules R A).withHoles (fun _ j => Holes A Seed j))
    (fun _ judgment tree => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (target : Judgment A) (h : substJudgment judgment σ = target),
      interpret R A Seed model assigned target
          (substitute R A Seed judgment tree σ target h) =
        model.act judgment
          (interpret R A Seed model assigned judgment tree) σ target h)
    ?_ () judgment tree
  intro base j shape children ih
  cases base
  cases shape with
  | inl hole =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      intro Δ σ target h
      change interpret R A Seed model assigned target
          (substitute R A Seed j
            (IndexedPolynomial.Free.pure (rules R A) hole)
            σ target h) =
        model.act j
          (interpret R A Seed model assigned j
            (IndexedPolynomial.Free.pure (rules R A) hole))
          σ target h
      rw [substitute_pure R A Seed j hole σ target h,
        interpret_cast R A Seed model assigned h,
        interpret_pure, interpret_pure]
      exact assigned.map j hole σ target h
  | inr shape =>
      change (position : Fin (R.get shape.1.index).2.premises.length) →
        Tree R A Seed (childJudgment R A shape.1 position) at children
      change ∀ position, ∀ {Δ : Ctx S}
        (σ : Environment S A.substitution.Carrier
          (childJudgment R A shape.1 position).1 Δ)
        (target : Judgment A)
        (h : substJudgment (childJudgment R A shape.1 position) σ = target),
        interpret R A Seed model assigned target
            (substitute R A Seed _ (children position) σ target h) =
          model.act _
            (interpret R A Seed model assigned _ (children position))
            σ target h at ih
      intro Δ σ target h
      refine Eq.trans ?_ (model.act_rules shape
        (fun position => interpret R A Seed model assigned _
          (children position)) σ target h).symm
      exact congrArg
        (fun values => model.rules.act () target
          ⟨⟨Instance.subst R shape.1 (castEnv shape.2 σ),
            (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
              ((substJudgment_castEnv shape.2 σ).trans h)⟩,
            values⟩)
        (funext fun position => ih position _ _ _)


/-- Each assignment of original event generators extends to a map of
substitution-operational models. Its rule component is the recursive fold. -/
noncomputable def foldHom
    (model : SubstitutionModel R A)
    (assigned : NaturalAssignment R A Seed model) :
    SubstitutionModel.Hom R A (freeModel R A Seed) model where
  evidence := {
    toFun := fun _ judgment tree =>
      interpret R A Seed model assigned judgment tree
    commutes := by
      intro base judgment layer
      cases base
      cases layer with
      | mk shape children =>
          exact interpret_node R A Seed model assigned shape children }
  preserves := fun judgment tree _ σ target h =>
    interpret_substitute R A Seed model assigned judgment tree σ target h


/-- Maps out of the free substitution-operational model are determined by
their values on event leaves; the rule-node cases follow from the hom law. -/
theorem hom_ext_on_leaves
    (model : SubstitutionModel R A)
    (first second : SubstitutionModel.Hom R A (freeModel R A Seed) model)
    (sameLeaves : ∀ judgment (hole : Holes A Seed judgment),
      first.evidence.toFun () judgment
          (IndexedPolynomial.Free.pure (rules R A) hole) =
        second.evidence.toFun () judgment
          (IndexedPolynomial.Free.pure (rules R A) hole)) :
    first = second := by
  apply IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.Hom.ext
  apply IndexedPolynomial.Algebra.Hom.ext
  intro base judgment tree
  cases base
  refine IndexedPolynomial.Fix.eliminate
    ((rules R A).withHoles (fun _ j => Holes A Seed j))
    (fun _ judgment tree =>
      first.evidence.toFun () judgment tree =
        second.evidence.toFun () judgment tree) ?_ () judgment tree
  intro base judgment shape children ih
  cases base
  cases shape with
  | inl hole =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      exact sameLeaves judgment hole
  | inr shape =>
      change (position : Fin (R.get shape.1.index).2.premises.length) →
        Tree R A Seed (childJudgment R A shape.1 position) at children
      change ∀ position,
        first.evidence.toFun () _ (children position) =
          second.evidence.toFun () _ (children position) at ih
      calc
        first.evidence.toFun () judgment
            (IndexedPolynomial.Free.node (rules R A) shape children) =
          model.rules.act () judgment
            ⟨shape, fun position =>
              first.evidence.toFun () _ (children position)⟩ :=
          first.evidence.commutes () judgment ⟨shape, children⟩
        _ = model.rules.act () judgment
            ⟨shape, fun position =>
              second.evidence.toFun () _ (children position)⟩ := by
          congr 1
          congr 1
          funext position
          exact ih position
        _ = second.evidence.toFun () judgment
            (IndexedPolynomial.Free.node (rules R A) shape children) :=
          (second.evidence.commutes () judgment ⟨shape, children⟩).symm


/-- Every substitution-model map restricts to a natural assignment on
individual event-variable uses. -/
noncomputable def assignmentOfHom
    (model : SubstitutionModel R A)
    (hom : SubstitutionModel.Hom R A (freeModel R A Seed) model) :
    NaturalAssignment R A Seed model where
  value judgment hole := hom.evidence.toFun () judgment
    (IndexedPolynomial.Free.pure (rules R A) hole)
  map := by
    intro judgment hole Δ σ target h
    cases h
    have preserved := hom.preserves judgment
      (IndexedPolynomial.Free.pure (rules R A) hole)
      σ (substJudgment judgment σ) rfl
    change hom.evidence.toFun () (substJudgment judgment σ)
        (substitute R A Seed judgment
          (IndexedPolynomial.Free.pure (rules R A) hole)
          σ (substJudgment judgment σ) rfl) = _ at preserved
    rw [substitute_pure R A Seed judgment hole σ
      (substJudgment judgment σ) rfl] at preserved
    exact preserved

/-- Equal uses at equal judgments receive equal values. -/
theorem NaturalAssignment.value_heq {model : SubstitutionModel R A}
    (assignment : NaturalAssignment R A Seed model)
    {first second : Judgment A} (same : first = second)
    {one : Holes A Seed first} {two : Holes A Seed second}
    (sameHole : HEq one two) :
    HEq (assignment.value first one) (assignment.value second two) := by
  subst same
  cases sameHole
  rfl

@[ext] theorem NaturalAssignment.ext
    (model : SubstitutionModel R A)
    {first second : NaturalAssignment R A Seed model}
    (same : ∀ judgment hole,
      first.value judgment hole = second.value judgment hole) :
    first = second := by
  cases first with
  | mk firstValue firstMap =>
    cases second with
    | mk secondValue secondMap =>
      have valueEq : firstValue = secondValue := by
        funext judgment hole
        exact same judgment hole
      subst valueEq
      rfl

/-- For a fixed binding clone, natural interpretations of individual
substituted event variables are equivalent to maps of rule-local operational
models from the free firing trees. -/
noncomputable def freeModelUniversal
    (model : SubstitutionModel R A) :
    NaturalAssignment R A Seed model ≃
      SubstitutionModel.Hom R A (freeModel R A Seed) model where
  toFun := foldHom R A Seed model
  invFun := assignmentOfHom R A Seed model
  left_inv := by
    intro assigned
    apply NaturalAssignment.ext R A Seed model
    intro judgment hole
    exact interpret_pure R A Seed model assigned judgment hole
  right_inv := by
    intro hom
    apply hom_ext_on_leaves R A Seed model
    intro judgment hole
    exact interpret_pure R A Seed model
      (assignmentOfHom R A Seed model hom) judgment hole

/-- Follow an interpretation of event uses by a map of models. -/
noncomputable def NaturalAssignment.mapHom {first second : SubstitutionModel R A}
    (assigned : NaturalAssignment R A Seed first)
    (hom : SubstitutionModel.Hom R A first second) : NaturalAssignment R A Seed second :=
  assignmentOfHom R A Seed second
    (SubstitutionModel.Hom.comp R A (foldHom R A Seed first assigned) hom)

/-- **Maps of models commute with interpreting firing trees.** -/
theorem interpret_mapHom {first second : SubstitutionModel R A}
    (assigned : NaturalAssignment R A Seed first)
    (hom : SubstitutionModel.Hom R A first second)
    (judgment : Judgment A) (tree : Tree R A Seed judgment) :
    interpret R A Seed second (assigned.mapHom R A Seed hom) judgment tree =
      hom.evidence.toFun () judgment (interpret R A Seed first assigned judgment tree) :=
  congrArg (fun composite : SubstitutionModel.Hom R A (freeModel R A Seed) second =>
      composite.evidence.toFun () judgment tree)
    ((freeModelUniversal R A Seed second).right_inv _)

/-- A closed local-rule derivation is a tree with no event-variable leaves. -/
noncomputable def embedClosed (judgment : Judgment A) :
    IntrinsicScopedLocalPolynomial.Tree R A judgment →
      Tree R A Seed judgment :=
  IndexedPolynomial.Fix.fold (rules R A)
    (IndexedPolynomial.Free.algebra (rules R A)).act () judgment

theorem embedClosed_roll {judgment : Judgment A}
    (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      IntrinsicScopedLocalPolynomial.Tree R A
        (childJudgment R A shape.1 position)) :
    embedClosed R A Seed judgment
        (IndexedPolynomial.Fix.roll shape children) =
      IndexedPolynomial.Free.node (rules R A) shape
        (fun position => embedClosed R A Seed _ (children position)) := rfl

/-- The closed-tree embedding preserves the original local rule nodes,
including their binder-local substitution action. -/
theorem embedClosed_substTree (judgment : Judgment A)
    (tree : IntrinsicScopedLocalPolynomial.Tree R A judgment) :
    ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (target : Judgment A) (h : substJudgment judgment σ = target),
      embedClosed R A Seed target
        (IntrinsicScopedLocalPolynomial.substTree R A judgment tree σ target h) =
      substitute R A Seed judgment
        (embedClosed R A Seed judgment tree) σ target h := by
  refine IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ judgment tree => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier judgment.1 Δ)
      (target : Judgment A) (h : substJudgment judgment σ = target),
      embedClosed R A Seed target
        (IntrinsicScopedLocalPolynomial.substTree R A judgment tree σ target h) =
      substitute R A Seed judgment
        (embedClosed R A Seed judgment tree) σ target h) ?_ () judgment tree
  intro base judgment shape children ih
  cases base
  intro Δ σ target h
  exact congrArg
    (fun values => IndexedPolynomial.Free.node (rules R A)
      (⟨Instance.subst R shape.1 (castEnv shape.2 σ),
        (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
          ((substJudgment_castEnv shape.2 σ).trans h)⟩ : Shape R A target)
      values)
    (funext fun position => ih position _ _ _)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree
