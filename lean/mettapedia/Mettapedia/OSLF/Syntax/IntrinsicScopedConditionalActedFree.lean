import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalEventOrbit
import Mettapedia.TypeTheory.IndexedPolynomialFree

/-!
# Free rule trees with substitution-closed event generators

An event leaf records its original judgment and an ordinary-variable
substitution to the judgment where it is used. Rule nodes keep their ordered
premise positions and their binder-local judgments. This is the event syntax
needed for a classifier of substitution-operational models.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedFree

open Mettapedia.TypeTheory
open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable (A : BindingCloneAlgebra.Algebra.{0} S)
variable (Seed : (sort : S.Srt) → State A sort → Type)

/-- Event leaves are the substitution orbits of the original generators. -/
abbrev Holes (judgment : Judgment A) : Type :=
  Orbit A Seed (ofJudgment A judgment)

/-- Rule trees over event variables closed under ordinary substitution. -/
abbrev Tree (judgment : Judgment A) : Type :=
  (rules R A).Free (fun _ j => Holes A Seed j) PUnit.unit judgment

/-- A bare event variable embeds as a leaf at its own judgment. -/
noncomputable def generator {sort : S.Srt} {state : State A sort}
    (seed : Seed sort state) : Tree R A Seed (state.asJudgment A) :=
  IndexedPolynomial.Free.pure (rules R A)
    ((State.of_as A state).symm ▸ Orbit.unit A Seed seed)

/-- Applying a judgment substitution to a leaf composes its recorded
substitution with the new one. -/
noncomputable def mapHole (judgment : Judgment A)
    (hole : Holes A Seed judgment)
    {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ) :
    Holes A Seed (substJudgment judgment σ) :=
  hole.map A Seed (substitutionArrow A judgment σ)

private theorem eqToHom_environment_heq {sort : S.Srt}
    {first second : State A sort} (equal : first = second) :
    HEq (eqToHom equal : first ⟶ second).environment
      (fun _ v => A.substitution.injectVar v :
        Environment S A.substitution.Carrier first.context first.context) := by
  cases equal
  rfl

private theorem orbit_map_eqToHom {sort : S.Srt}
    {first second : State A sort} (equal : first = second)
    (event : Orbit A Seed first) :
    event.map A Seed (eqToHom equal) = equal ▸ event := by
  cases equal
  exact event.map_id A Seed

private theorem cast_heq {Index : Type} {F : Index → Type}
    {first second : Index} (equal : first = second) (value : F first) :
    HEq (equal ▸ value) value := by
  cases equal
  rfl

private theorem ofJudgment_heq {first second : Judgment A}
    (equal : first = second) :
    HEq (ofJudgment A first) (ofJudgment A second) := by
  cases equal
  rfl

private theorem map_heq {sort : S.Srt}
    {first second otherFirst otherSecond : State A sort}
    (sourceEq : first = otherFirst) (targetEq : second = otherSecond)
    {f : first ⟶ second} {g : otherFirst ⟶ otherSecond}
    (sameEnvironment : HEq f.environment g.environment) : HEq f g := by
  subst sourceEq
  subst targetEq
  exact heq_of_eq (Map.ext A (eq_of_heq sameEnvironment))

private theorem orbit_map_heq {sort : S.Srt}
    {first second otherFirst otherSecond : State A sort}
    (sourceEq : first = otherFirst) (targetEq : second = otherSecond)
    {event : Orbit A Seed first} {other : Orbit A Seed otherFirst}
    (sameEvent : HEq event other)
    {f : first ⟶ second} {g : otherFirst ⟶ otherSecond}
    (sameArrow : HEq f g) :
    HEq (event.map A Seed f) (other.map A Seed g) := by
  subst sourceEq
  subst targetEq
  have eventEq := eq_of_heq sameEvent
  have arrowEq := eq_of_heq sameArrow
  subst eventEq
  subst arrowEq
  rfl

/-- A free event leaf acted on by two environments has the same original
generator and composed contextual arrow as one direct action. -/
theorem mapHole_comp_heq (judgment : Judgment A)
    (hole : Holes A Seed judgment)
    {Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ)
    (τ : Environment S A.substitution.Carrier Δ Θ) :
    HEq
      (mapHole A Seed (substJudgment judgment σ)
        (mapHole A Seed judgment hole σ) τ)
      (mapHole A Seed judgment hole
        (fun s v => A.substitution.substitute τ (σ s v))) := by
  let first := substitutionArrow A judgment σ
  let second := substitutionArrow A (substJudgment judgment σ) τ
  let direct := substitutionArrow A judgment
    (fun s v => A.substitution.substitute τ (σ s v))
  have judgmentEq := substJudgment_comp judgment σ τ
  have stateEq : ofJudgment A (substJudgment
      (substJudgment judgment σ) τ) =
      ofJudgment A (substJudgment judgment
        (fun s v => A.substitution.substitute τ (σ s v))) :=
    eq_of_heq (ofJudgment_heq A judgmentEq)
  have idEnv : (eqToHom stateEq).environment =
      (fun _ v => A.substitution.injectVar v :
        Environment S A.substitution.Carrier Θ Θ) :=
    eq_of_heq (eqToHom_environment_heq A stateEq)
  have arrows : (first ≫ second) ≫ eqToHom stateEq = direct := by
    apply Map.ext A
    funext s v
    change A.substitution.substitute
      (eqToHom stateEq).environment
      (A.substitution.substitute τ (σ s v)) =
      A.substitution.substitute τ (σ s v)
    rw [idEnv]
    exact A.substitution.substitute_identity _
  change HEq ((hole.map A Seed first).map A Seed second)
    (hole.map A Seed direct)
  have transported : stateEq ▸
      ((hole.map A Seed first).map A Seed second) =
      hole.map A Seed direct := by
    calc
      stateEq ▸ ((hole.map A Seed first).map A Seed second) =
          ((hole.map A Seed first).map A Seed second).map A Seed
            (eqToHom stateEq) :=
        (orbit_map_eqToHom A Seed stateEq _).symm
      _ = hole.map A Seed ((first ≫ second) ≫ eqToHom stateEq) := by
        rw [Orbit.map_comp A Seed hole first second,
          Orbit.map_comp A Seed hole (first ≫ second)
            (eqToHom stateEq)]
      _ = hole.map A Seed direct := by rw [arrows]
  exact (cast_heq stateEq
    ((hole.map A Seed first).map A Seed second)).symm.trans
      (heq_of_eq transported)

/-- A substituted event leaf returns to itself under the identity
environment, including its generator identity and recorded arrow. -/
theorem mapHole_identity (judgment : Judgment A)
    (hole : Holes A Seed judgment)
    (h : substJudgment judgment
      (fun _ v => A.substitution.injectVar v) = judgment) :
    h ▸ mapHole A Seed judgment hole
      (fun _ v => A.substitution.injectVar v) = hole := by
  have stateEq : ofJudgment A judgment =
      ofJudgment A (substJudgment judgment
        (fun _ v => A.substitution.injectVar v)) := by
    rcases judgment with ⟨Γ, sort, source, target⟩
    change (⟨Γ, source, target⟩ : State A sort) =
      ⟨Γ, A.substitution.substitute
        (fun _ v => A.substitution.injectVar v) source,
        A.substitution.substitute
          (fun _ v => A.substitution.injectVar v) target⟩
    rw [A.substitution.substitute_identity,
      A.substitution.substitute_identity]
  have hArr : substitutionArrow A judgment
      (fun _ v => A.substitution.injectVar v) =
      eqToHom stateEq := by
    apply Map.ext A
    exact eq_of_heq
      (eqToHom_environment_heq A stateEq).symm
  change Orbit A Seed (ofJudgment A judgment) at hole
  change h ▸ (hole.map A Seed
      (substitutionArrow A judgment
        (fun _ v => A.substitution.injectVar v))) = hole
  rw [hArr, orbit_map_eqToHom A Seed stateEq]
  let mapped0 : Orbit A Seed (ofJudgment A (substJudgment judgment
      (fun _ v => A.substitution.injectVar v))) := stateEq ▸ hole
  let mapped : Holes A Seed (substJudgment judgment
      (fun _ v => A.substitution.injectVar v)) := mapped0
  have firstStep : HEq (h ▸ mapped) mapped :=
    heq_transport (F := fun j => Holes A Seed j) h mapped
  have secondStep : HEq mapped hole := by
    change HEq (stateEq ▸ hole) hole
    exact cast_heq stateEq hole
  exact eq_of_heq (firstStep.trans secondStep)

/-- Substitution of complete free trees acts on rule occurrences and on
individual event leaves. It lifts under each premise's local binders. -/
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
            (mapHole A Seed judgment hole σ)
      | .inr rule =>
          IndexedPolynomial.Free.node (rules R A)
            (⟨Instance.subst R rule.1 (castEnv rule.2 σ),
              (conclusionJudgment_subst R rule.1 (castEnv rule.2 σ)).trans
                ((substJudgment_castEnv rule.2 σ).trans h)⟩ :
              Shape R A target)
            (fun position => results position
              (A.substitution.liftEnvironment (castEnv rule.2 σ)
                ((R.get rule.1.index).premises.get position).binders)
              (childJudgment R A (Instance.subst R rule.1
                (castEnv rule.2 σ)) position)
              (childJudgment_subst R rule.1 (castEnv rule.2 σ)
                position).symm))
    PUnit.unit

/-- On an event variable, tree substitution is the free action on that
individual generator, not a reconstruction from its endpoints. -/
theorem substitute_pure (judgment : Judgment A)
    (hole : Holes A Seed judgment) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ)
    (target : Judgment A) (h : substJudgment judgment σ = target) :
    substitute R A Seed judgment
        (IndexedPolynomial.Free.pure (rules R A) hole) σ target h =
      h ▸ IndexedPolynomial.Free.pure (rules R A)
        (mapHole A Seed judgment hole σ) := rfl

/-- On a rule constructor, tree substitution acts on the occurrence and
recursively on every ordered premise under its local binder context. -/
theorem substitute_node {judgment : Judgment A}
    (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).premises.length,
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
            ((R.get shape.1.index).premises.get position).binders)
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
    (firstChildren : ∀ position : Fin (R.get first.index).premises.length,
      Tree R A Seed (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).premises.length,
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

private theorem pure_cast {first second : Judgment A}
    (equal : first = second) (hole : Holes A Seed first) :
    equal ▸ (IndexedPolynomial.Free.pure (rules R A) hole :
      Tree R A Seed first) =
      IndexedPolynomial.Free.pure (rules R A) (equal ▸ hole) := by
  cases equal
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
    ?_ PUnit.unit judgment tree
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
      rw [substitute_pure, pure_cast,
        mapHole_identity A Seed j hole h]
  | inr shape =>
      change (position : Fin (R.get shape.1.index).premises.length) →
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
              ((R.get occurrence.index).premises.get position).binders =
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
    ?_ PUnit.unit judgment tree
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
            (mapHole A Seed j hole σ)) τ target hSecond = _
      rw [substitute_pure R A Seed (substJudgment j σ)
        (mapHole A Seed j hole σ) τ target hSecond]
      rw [substitute_pure R A Seed j hole
        (fun s v => A.substitution.substitute τ (σ s v))
        target hDirect]
      rw [pure_cast, pure_cast]
      have holeEq : HEq
          (mapHole A Seed (substJudgment j σ)
            (mapHole A Seed j hole σ) τ)
          (mapHole A Seed j hole
            (fun s v => A.substitution.substitute τ (σ s v))) :=
        mapHole_comp_heq A Seed j hole σ τ
      have leftCast : HEq
          (hSecond ▸ mapHole A Seed (substJudgment j σ)
            (mapHole A Seed j hole σ) τ)
          (mapHole A Seed (substJudgment j σ)
            (mapHole A Seed j hole σ) τ) :=
        cast_heq hSecond _
      have rightCast : HEq
          (hDirect ▸ mapHole A Seed j hole
            (fun s v => A.substitution.substitute τ (σ s v)))
          (mapHole A Seed j hole
            (fun s v => A.substitution.substitute τ (σ s v))) :=
        cast_heq hDirect _
      exact congrArg (IndexedPolynomial.Free.pure (rules R A))
        (eq_of_heq (leftCast.trans (holeEq.trans rightCast.symm)))
  | inr shape =>
      change (position : Fin (R.get shape.1.index).premises.length) →
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
              ((R.get occurrence.index).premises.get position).binders) :=
        childJudgment_subst R occurrence σ position
      have liftComp :
          (fun s v => A.substitution.substitute
            (A.substitution.liftEnvironment τ
              ((R.get occurrence.index).premises.get position).binders)
            (A.substitution.liftEnvironment σ
              ((R.get occurrence.index).premises.get position).binders s v)) =
          A.substitution.liftEnvironment
            (fun s v => A.substitution.substitute τ (σ s v))
            ((R.get occurrence.index).premises.get position).binders := by
        funext s v
        exact substitute_liftEnvironment A.substitution τ σ _ v
      have directChild :
          substJudgment
            (substJudgment (childJudgment R A occurrence position)
              (A.substitution.liftEnvironment σ
                ((R.get occurrence.index).premises.get position).binders))
            (A.substitution.liftEnvironment τ
              ((R.get occurrence.index).premises.get position).binders) =
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
                ((R.get occurrence.index).premises.get position).binders)
              (A.substitution.liftEnvironment σ
                ((R.get occurrence.index).premises.get position).binders s v)) =
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
              ((R.get occurrence.index).premises.get position).binders)
            (envEq _)))
          (childJudgment_congr R (instanceEq _) position position HEq.rfl)
          _ directChild) ?_
      refine HEq.trans (heq_of_eq (ih position
        (A.substitution.liftEnvironment σ
          ((R.get occurrence.index).premises.get position).binders)
        (A.substitution.liftEnvironment τ
          ((R.get occurrence.index).premises.get position).binders)
        _ directChild directOnce)) ?_
      exact substitute_congr R A Seed (children position) liftComp rfl _ _

/-- Free rule trees over substitution orbits form an actual operational
model: the action is defined on both generators and rule constructors. -/
noncomputable def freeModel : SubstitutionModel R A where
  evidence := {
    carrier := fun _ judgment => Tree R A Seed judgment
    rules := IndexedPolynomial.Free.algebra (rules R A) }
  act := substitute R A Seed
  act_rules := by
    intro judgment shape children Δ σ target h
    rfl
  act_identity := substitute_identity R A Seed
  act_comp := substitute_comp R A Seed

/-- An orbit element is a single event leaf in the corresponding fixed-sort
judgment, including the harmless state-packaging equality. -/
noncomputable def pureAt {sort : S.Srt} {state : State A sort}
    (event : Orbit A Seed state) : Tree R A Seed (state.asJudgment A) :=
  IndexedPolynomial.Free.pure (rules R A)
    ((State.of_as A state).symm ▸ event)

/-- The tree action on a single event leaf is exactly the free orbit action.
This is the one-leaf substitution law needed in the classifier. -/
theorem substitute_pureAt {sort : S.Srt}
    {first second : State A sort} (f : first ⟶ second)
    (event : Orbit A Seed first) :
    substitute R A Seed (first.asJudgment A) (pureAt R A Seed event)
        f.environment (second.asJudgment A)
        (Map.as_substitution A f) =
      pureAt R A Seed (event.map A Seed f) := by
  let j₀ := first.asJudgment A
  let j₁ := second.asJudgment A
  let e₀ := State.of_as A first
  let e₁ := State.of_as A second
  let event₀ : Holes A Seed j₀ :=
    Eq.mp (congrArg (fun st : State A sort => Orbit A Seed st) e₀.symm)
      event
  let event₁ : Holes A Seed j₁ :=
    Eq.mp (congrArg (fun st : State A sort => Orbit A Seed st) e₁.symm)
      (event.map A Seed f)
  let f₀ := substitutionArrow A j₀ f.environment
  let h := Map.as_substitution A f
  have targetEq : ofJudgment A (substJudgment j₀ f.environment) =
      second :=
    (eq_of_heq (ofJudgment_heq A
      (first := substJudgment j₀ f.environment)
      (second := second.asJudgment A) h)).trans e₁
  have arrowEq : HEq f₀ f :=
    map_heq A e₀ targetEq HEq.rfl
  have leafEq : HEq
      (event₀.map A Seed f₀)
      (event.map A Seed f) :=
    orbit_map_heq A Seed e₀ targetEq
      (cast_heq e₀.symm event) arrowEq
  change substitute R A Seed j₀
      (IndexedPolynomial.Free.pure (rules R A)
        event₀) f.environment j₁ h =
    IndexedPolynomial.Free.pure (rules R A)
      event₁
  rw [substitute_pure R A Seed j₀ event₀ f.environment j₁ h,
    pure_cast]
  apply congrArg (IndexedPolynomial.Free.pure (rules R A))
  have castLeft : HEq
      (h ▸ mapHole A Seed j₀ event₀ f.environment)
      (mapHole A Seed j₀ event₀ f.environment) :=
    cast_heq h _
  have castRight : HEq event₁ (event.map A Seed f) :=
    cast_heq e₁.symm (event.map A Seed f)
  exact eq_of_heq
    (castLeft.trans (leafEq.trans castRight.symm))

/-- The syntactic use of an event variable is natural in contextual
substitution; naturality is the proved one-leaf action equation. -/
noncomputable def pureOrbitNat (sort : S.Srt) :
    freeAction A Seed sort ⟶ modelAction A (freeModel R A Seed) sort where
  app state := TypeCat.ofHom (pureAt R A Seed)
  naturality := by
    intro first second f
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact (substitute_pureAt R A Seed f event).symm

/-- Every operational-model map induces a natural map on the evidence
action over each contextual judgment category. -/
noncomputable def modelActionHom
    {X Y : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R X Y) (sort : S.Srt) :
    modelAction A X sort ⟶ modelAction A Y sort where
  app state := TypeCat.ofHom (h.evidence.toFun () (state.asJudgment A))
  naturality := by
    intro first second f
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext evidence
    exact (h.preserves (first.asJudgment A) evidence
      f.environment (second.asJudgment A)
      (Map.as_substitution A f))

/-- The interpretation of a complete free event tree applies the target's
actual action to substituted generators and its actual authored action to
rule constructors. -/
def decodeHole
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    (judgment : Judgment A) (hole : Holes A Seed judgment) :
    model.evidence.carrier () judgment :=
  (State.as_of A judgment) ▸
    hole.interpret A Seed model (assigned judgment.2.1)

/-- Decoding a substituted event variable applies the target model's
substitution action to the decoded original witness. -/
theorem decodeHole_map
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    (judgment : Judgment A) (hole : Holes A Seed judgment)
    {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ)
    (target : Judgment A) (h : substJudgment judgment σ = target) :
    h ▸ decodeHole R A Seed model assigned
      (substJudgment judgment σ) (mapHole A Seed judgment hole σ) =
    model.act judgment (decodeHole R A Seed model assigned judgment hole)
      σ target h := by
  let first := ofJudgment A judgment
  let second := ofJudgment A (substJudgment judgment σ)
  let f := substitutionArrow A judgment σ
  let original := hole.interpret A Seed model (assigned judgment.2.1)
  have orbitLaw := Orbit.interpret_map A Seed model
    (assigned judgment.2.1) hole f
  have sourceEq : first.asJudgment A = judgment := State.as_of A judgment
  have targetEq : second.asJudgment A = substJudgment judgment σ :=
    State.as_of A (substJudgment judgment σ)
  have casts : HEq
      (h ▸ decodeHole R A Seed model assigned
        (substJudgment judgment σ) (mapHole A Seed judgment hole σ))
      ((mapHole A Seed judgment hole σ).interpret A Seed model
        (assigned judgment.2.1)) :=
    (cast_heq h _).trans (cast_heq targetEq _)
  have acted : HEq
      (model.act (first.asJudgment A) original f.environment
        (second.asJudgment A) (Map.as_substitution A f))
      (model.act judgment
        (decodeHole R A Seed model assigned judgment hole)
        σ target h) :=
    SubstitutionModel.act_heq R model sourceEq
      (cast_heq sourceEq original).symm HEq.rfl
      (targetEq.trans h) (Map.as_substitution A f) h
  exact eq_of_heq (casts.trans ((heq_of_eq orbitLaw).trans acted))

noncomputable def interpret
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A)) :
    ∀ judgment : Judgment A,
      Tree R A Seed judgment → model.evidence.carrier () judgment :=
  IndexedPolynomial.Free.fold (rules R A)
    (fun _ judgment hole => decodeHole R A Seed model assigned judgment hole)
    model.evidence.rules PUnit.unit

theorem interpret_pure
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    (judgment : Judgment A) (hole : Holes A Seed judgment) :
    interpret R A Seed model assigned judgment
        (IndexedPolynomial.Free.pure (rules R A) hole) =
      decodeHole R A Seed model assigned judgment hole := rfl

private theorem orbit_interpret_cast
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    {sort : S.Srt} {first second : State A sort}
    (equal : first = second) (event : Orbit A Seed first) :
    HEq ((equal ▸ event).interpret A Seed model (assigned sort))
      (event.interpret A Seed model (assigned sort)) := by
  cases equal
  rfl

/-- A freshly named event variable evaluates to exactly its assigned
witness; the fixed-sort packaging introduces no additional event. -/
theorem interpret_generator
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    {sort : S.Srt} {state : State A sort}
    (seed : Seed sort state) :
    interpret R A Seed model assigned (state.asJudgment A)
      (generator R A Seed seed) = assigned sort state seed := by
  unfold generator
  rw [interpret_pure]
  let e := (State.of_as A state).symm
  have firstCast : HEq
      (decodeHole R A Seed model assigned (state.asJudgment A)
        (e ▸ Orbit.unit A Seed seed))
      ((e ▸ Orbit.unit A Seed seed).interpret A Seed model
        (assigned sort)) :=
    cast_heq (State.as_of A (state.asJudgment A)) _
  have secondCast : HEq
      ((e ▸ Orbit.unit A Seed seed).interpret A Seed model
        (assigned sort))
      ((Orbit.unit A Seed seed).interpret A Seed model
        (assigned sort)) :=
    orbit_interpret_cast R A Seed model assigned e _
  exact eq_of_heq ((firstCast.trans secondCast).trans
    (heq_of_eq (Orbit.interpret_unit A Seed model
      (assigned sort) seed)))

theorem interpret_node
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    {judgment : Judgment A}
    (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).premises.length,
      Tree R A Seed (childJudgment R A shape.1 position)) :
    interpret R A Seed model assigned judgment
        (IndexedPolynomial.Free.node (rules R A) shape children) =
      model.evidence.rules.act () judgment
        ⟨shape, fun position =>
          interpret R A Seed model assigned _ (children position)⟩ := rfl

private theorem interpret_cast
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
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
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
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
    ?_ PUnit.unit judgment tree
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
      exact decodeHole_map R A Seed model assigned j hole σ target h
  | inr shape =>
      change (position : Fin (R.get shape.1.index).premises.length) →
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
        (fun values => model.evidence.rules.act () target
          ⟨⟨Instance.subst R shape.1 (castEnv shape.2 σ),
            (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
              ((substJudgment_castEnv shape.2 σ).trans h)⟩,
            values⟩)
        (funext fun position => ih position _ _ _)

/-- Each assignment of original event generators extends to a map of
substitution-operational models. Its rule component is the recursive fold. -/
noncomputable def foldHom
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A)) :
    SubstitutionModel.Hom R (freeModel R A Seed) model where
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

/-- The extension evaluates each named generator to its original assigned
evidence, before any rule or contextual substitution is applied. -/
theorem foldHom_generator
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    {sort : S.Srt} {state : State A sort} (seed : Seed sort state) :
    (foldHom R A Seed model assigned).evidence.toFun ()
        (state.asJudgment A) (generator R A Seed seed) =
      assigned sort state seed :=
  interpret_generator R A Seed model assigned seed

/-- Read the original event-generator assignment underlying a model map. -/
noncomputable def assignmentOfHom
    (model : SubstitutionModel R A)
    (h : SubstitutionModel.Hom R (freeModel R A Seed) model) :
    ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A) :=
  fun _ state seed => h.evidence.toFun () (state.asJudgment A)
    (generator R A Seed seed)

/-- A model map must interpret every substituted event leaf by acting on
its assigned original generator. This follows from naturality of the free
orbit and the model map, so no per-leaf preservation assumption is added. -/
theorem hom_pureAt
    (model : SubstitutionModel R A)
    (h : SubstitutionModel.Hom R (freeModel R A Seed) model)
    {sort : S.Srt} {state : State A sort}
    (event : Orbit A Seed state) :
    h.evidence.toFun () (state.asJudgment A) (pureAt R A Seed event) =
      event.interpret A Seed model
        (assignmentOfHom R A Seed model h sort) := by
  let η : freeAction A Seed sort ⟶ modelAction A model sort :=
    pureOrbitNat R A Seed sort ≫ modelActionHom R A h sort
  have assignedEq : generatorAssignment A Seed model sort η =
      assignmentOfHom R A Seed model h sort := by
    funext original seed
    rfl
  have uniqueness :=
    freeActionInterpretation_generatorAssignment A Seed model sort η
  have valueEq := congrArg (fun θ : freeAction A Seed sort ⟶
      modelAction A model sort => θ.app state event) uniqueness
  change event.interpret A Seed model
      (generatorAssignment A Seed model sort η) =
    h.evidence.toFun () (state.asJudgment A)
      (pureAt R A Seed event) at valueEq
  rw [assignedEq] at valueEq
  exact valueEq.symm

/-- Returning from the fixed-sort packaging identifies the syntactic orbit
leaf with the corresponding judgment-indexed free leaf. -/
theorem pureAt_onJudgment (judgment : Judgment A)
    (hole : Holes A Seed judgment) :
    (State.as_of A judgment) ▸
        pureAt R A Seed hole =
      IndexedPolynomial.Free.pure (rules R A) hole := by
  let state := ofJudgment A judgment
  let firstCast := (State.of_as A state).symm
  let secondCast := State.as_of A judgment
  let mapped : Holes A Seed (state.asJudgment A) :=
    Eq.mp (congrArg (fun st : State A judgment.2.1 => Orbit A Seed st)
      firstCast) hole
  change secondCast ▸
      (IndexedPolynomial.Free.pure (rules R A) mapped :
        Tree R A Seed (state.asJudgment A)) =
    IndexedPolynomial.Free.pure (rules R A) hole
  rw [pure_cast R A Seed secondCast mapped]
  apply congrArg (IndexedPolynomial.Free.pure (rules R A))
  have castOne : HEq (secondCast ▸ mapped) mapped :=
    cast_heq secondCast mapped
  have castTwo : HEq mapped hole :=
    cast_heq firstCast hole
  exact eq_of_heq (castOne.trans castTwo)

private theorem hom_transport
    (model : SubstitutionModel R A)
    (h : SubstitutionModel.Hom R (freeModel R A Seed) model)
    {first second : Judgment A} (equal : first = second)
    (tree : Tree R A Seed first) :
    h.evidence.toFun () second (equal ▸ tree) =
      equal ▸ h.evidence.toFun () first tree := by
  cases equal
  rfl

/-- A lawful map's value at every event leaf is forced by its values on
bare generators and the target's actual substitution action. -/
theorem hom_leaf_eq_decode
    (model : SubstitutionModel R A)
    (h : SubstitutionModel.Hom R (freeModel R A Seed) model)
    (judgment : Judgment A) (hole : Holes A Seed judgment) :
    h.evidence.toFun () judgment
        (IndexedPolynomial.Free.pure (rules R A) hole) =
      decodeHole R A Seed model
        (assignmentOfHom R A Seed model h) judgment hole := by
  let state := ofJudgment A judgment
  let equal := State.as_of A judgment
  rw [← pureAt_onJudgment R A Seed judgment hole]
  rw [hom_transport R A Seed model h equal
    (pureAt R A Seed hole)]
  rw [hom_pureAt R A Seed model h hole]
  rfl

/-- Maps out of the free substitution-operational model are determined by
their values on event leaves; the rule-node cases follow from the hom law. -/
theorem hom_ext_on_leaves
    (model : SubstitutionModel R A)
    (first second : SubstitutionModel.Hom R (freeModel R A Seed) model)
    (sameLeaves : ∀ judgment (hole : Holes A Seed judgment),
      first.evidence.toFun () judgment
          (IndexedPolynomial.Free.pure (rules R A) hole) =
        second.evidence.toFun () judgment
          (IndexedPolynomial.Free.pure (rules R A) hole)) :
    first = second := by
  apply SubstitutionModel.Hom.ext
  apply IndexedPolynomial.Algebra.Hom.ext
  intro base judgment tree
  cases base
  refine IndexedPolynomial.Fix.eliminate
    ((rules R A).withHoles (fun _ j => Holes A Seed j))
    (fun _ judgment tree =>
      first.evidence.toFun () judgment tree =
        second.evidence.toFun () judgment tree) ?_ PUnit.unit judgment tree
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
      change (position : Fin (R.get shape.1.index).premises.length) →
        Tree R A Seed (childJudgment R A shape.1 position) at children
      change ∀ position,
        first.evidence.toFun () _ (children position) =
          second.evidence.toFun () _ (children position) at ih
      calc
        first.evidence.toFun () judgment
            (IndexedPolynomial.Free.node (rules R A) shape children) =
          model.evidence.rules.act () judgment
            ⟨shape, fun position =>
              first.evidence.toFun () _ (children position)⟩ :=
          first.evidence.commutes () judgment ⟨shape, children⟩
        _ = model.evidence.rules.act () judgment
            ⟨shape, fun position =>
              second.evidence.toFun () _ (children position)⟩ := by
          congr 1
          congr 1
          funext position
          exact ih position
        _ = second.evidence.toFun () judgment
            (IndexedPolynomial.Free.node (rules R A) shape children) :=
          (second.evidence.commutes () judgment ⟨shape, children⟩).symm

/-- Extending and then restricting a generator assignment is the identity. -/
theorem assignmentOfHom_foldHom
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A)) :
    assignmentOfHom R A Seed model (foldHom R A Seed model assigned) =
      assigned := by
  funext sort state seed
  exact foldHom_generator R A Seed model assigned seed

/-- A lawful operational-model map is the unique extension of its values
on the original event generators. -/
theorem foldHom_assignmentOfHom
    (model : SubstitutionModel R A)
    (h : SubstitutionModel.Hom R (freeModel R A Seed) model) :
    foldHom R A Seed model (assignmentOfHom R A Seed model h) = h := by
  apply hom_ext_on_leaves R A Seed model
  intro judgment hole
  change interpret R A Seed model
      (assignmentOfHom R A Seed model h) judgment
      (IndexedPolynomial.Free.pure (rules R A) hole) =
    h.evidence.toFun () judgment
      (IndexedPolynomial.Free.pure (rules R A) hole)
  rw [interpret_pure]
  exact (hom_leaf_eq_decode R A Seed model h judgment hole).symm

/-- Universal property of free scoped firing trees with event substitution:
assigning bare generators is equivalent to a map of models preserving every
rule constructor and the substitution action on every firing witness. -/
noncomputable def freeModelUniversal
    (model : SubstitutionModel R A) :
    (∀ sort (state : State A sort),
      Seed sort state → model.evidence.carrier () (state.asJudgment A)) ≃
      SubstitutionModel.Hom R (freeModel R A Seed) model where
  toFun := foldHom R A Seed model
  invFun := assignmentOfHom R A Seed model
  left_inv := assignmentOfHom_foldHom R A Seed model
  right_inv := foldHom_assignmentOfHom R A Seed model

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedFree
