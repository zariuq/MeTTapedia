import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalSubstitution

/-!
# Contextual substitution of rule-local firing histories

The indexed-polynomial eliminator applies the local occurrence action to
all nodes. Every recursive call lifts the environment beneath that premise's
binders. Constructor identities, premise addresses, and child histories are
retained. The action obeys the identity and composition laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment castEnv castEnv_heq substJudgment_castEnv
   substJudgment_identity substJudgment_comp liftEnvironment_injectVar
   substitute_liftEnvironment mapJudgment_substJudgment heq_transport)

universe u v

variable {S : Signature} (R : List (LocalRule S))

/-- Contextual substitution of a complete firing tree. The result is
indexed by the substituted endpoints, so source and target commute with the
action by construction. Every rule occurrence is substituted, every premise
child is substituted beneath its own binders, and premise positions are kept. -/
noncomputable def substTree (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (j : Judgment A), Tree R A j →
      ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
        (target : Judgment A), substJudgment j σ = target → Tree R A target :=
  Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j _ => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A), substJudgment j σ = target → Tree R A target)
    (fun _ _ shape _children results {_} σ target h =>
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans h)⟩ :
          Shape R A target)
        (fun position => results position
          (A.substitution.liftEnvironment (castEnv shape.2 σ)
            ((R.get shape.1.index).2.premises.get position).binders)
          (childJudgment R A (Instance.subst R shape.1 (castEnv shape.2 σ))
            position)
          (childJudgment_subst R shape.1 (castEnv shape.2 σ) position).symm))
    ()

/-- The action on one constructor layer. -/
theorem substTree_roll (A : BindingCloneAlgebra.Algebra.{u} S)
    {j : Judgment A} (shape : Shape R A j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Tree R A (childJudgment R A shape.1 position))
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (h : substJudgment j σ = target) :
    substTree R A j (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll shape children)
        σ target h =
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans h)⟩ :
          Shape R A target)
        (fun (position : Fin (R.get shape.1.index).2.premises.length) =>
          substTree R A _ (children position)
          (A.substitution.liftEnvironment (castEnv shape.2 σ)
            ((R.get shape.1.index).2.premises.get position).binders)
          (childJudgment R A (Instance.subst R shape.1 (castEnv shape.2 σ))
            position)
          (childJudgment_subst R shape.1 (castEnv shape.2 σ) position).symm) :=
  rfl

/-- Equal occurrences with heterogeneously equal children build equal
constructor layers. -/
theorem roll_congr_instance {A : BindingCloneAlgebra.Algebra.{u} S}
    {target : Judgment A} {first second : Instance R A}
    (same : first = second)
    (firstConclusion : conclusionJudgment R A first = target)
    (secondConclusion : conclusionJudgment R A second = target)
    (firstChildren : ∀ position : Fin (R.get first.index).2.premises.length,
      Tree R A (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).2.premises.length,
      Tree R A (childJudgment R A second position))
    (children : ∀ firstPosition secondPosition,
      HEq firstPosition secondPosition →
        HEq (firstChildren firstPosition) (secondChildren secondPosition)) :
    (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨first, firstConclusion⟩ : Shape R A target) firstChildren :
      Tree R A target) =
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (⟨second, secondConclusion⟩ : Shape R A target) secondChildren := by
  subst same
  have childrenEq : firstChildren = secondChildren :=
    funext fun position => eq_of_heq (children position position HEq.rfl)
  subst childrenEq
  rfl

theorem childJudgment_congr {A : BindingCloneAlgebra.Algebra.{u} S}
    {first second : Instance R A} (same : first = second)
    (firstPosition : Fin (R.get first.index).2.premises.length)
    (secondPosition : Fin (R.get second.index).2.premises.length)
    (samePosition : HEq firstPosition secondPosition) :
    childJudgment R A first firstPosition =
      childJudgment R A second secondPosition := by
  subst same
  cases samePosition
  rfl

theorem substTree_congr (A : BindingCloneAlgebra.Algebra.{u} S)
    {j : Judgment A} (tree : Tree R A j) {Δ : Ctx S}
    {σ₁ σ₂ : Environment S A.substitution.Carrier j.1 Δ} (sameEnv : σ₁ = σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j σ₁ = target₁) (h₂ : substJudgment j σ₂ = target₂) :
    HEq (substTree R A j tree σ₁ target₁ h₁)
      (substTree R A j tree σ₂ target₂ h₂) := by
  subst sameEnv
  subst sameTarget
  rfl

theorem substTree_heq (A : BindingCloneAlgebra.Algebra.{u} S)
    {j₁ j₂ : Judgment A} (sameJudgment : j₁ = j₂)
    {tree₁ : Tree R A j₁} {tree₂ : Tree R A j₂} (sameTree : HEq tree₁ tree₂)
    {Δ : Ctx S} {σ₁ : Environment S A.substitution.Carrier j₁.1 Δ}
    {σ₂ : Environment S A.substitution.Carrier j₂.1 Δ} (sameEnv : HEq σ₁ σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j₁ σ₁ = target₁) (h₂ : substJudgment j₂ σ₂ = target₂) :
    HEq (substTree R A j₁ tree₁ σ₁ target₁ h₁)
      (substTree R A j₂ tree₂ σ₂ target₂ h₂) := by
  subst sameJudgment
  cases sameTree
  cases sameEnv
  subst sameTarget
  rfl

/-- The identity substitution fixes every firing tree. -/
theorem substTree_identity (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) (tree : Tree R A j) :
    ∀ (h : substJudgment j (fun _ v => A.substitution.injectVar v) = j),
      substTree R A j tree (fun _ v => A.substitution.injectVar v) j h =
        tree := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j tree => ∀ (h : substJudgment j
        (fun _ v => A.substitution.injectVar v) = j),
      substTree R A j tree (fun _ v => A.substitution.injectVar v) j h = tree)
    ?_ () j tree
  intro base j shape children ih
  cases base
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  intro h
  refine roll_congr_instance R (Instance.subst_identity R occurrence) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  have envEq :
      A.substitution.liftEnvironment
          (fun _ v => A.substitution.injectVar v :
            Environment S A.substitution.Carrier occurrence.ambient
              occurrence.ambient)
          ((R.get occurrence.index).2.premises.get position).binders =
        (fun _ v => A.substitution.injectVar v) :=
    liftEnvironment_injectVar A.substitution _
  have targetEq :
      childJudgment R A
          (Instance.subst R occurrence (fun _ v => A.substitution.injectVar v))
          position =
        childJudgment R A occurrence position :=
    (childJudgment_subst R occurrence _ position).trans
      ((congrArg (substJudgment (childJudgment R A occurrence position))
        (liftEnvironment_injectVar A.substitution _)).trans
        (substJudgment_identity _))
  exact (substTree_congr R A (children position) envEq targetEq _
    (substJudgment_identity _)).trans
    (heq_of_eq (ih position (substJudgment_identity _)))

/-- Substituting twice is substituting once along the composite. -/
theorem substTree_comp (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) (tree : Tree R A j) :
    ∀ {Δ Θ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (τ : Environment S A.substitution.Carrier Δ Θ) (target : Judgment A)
      (hSecond : substJudgment (substJudgment j σ) τ = target)
      (hDirect : substJudgment j
        (fun t v => A.substitution.substitute τ (σ t v)) = target),
      substTree R A (substJudgment j σ)
          (substTree R A j tree σ (substJudgment j σ) rfl) τ target hSecond =
        substTree R A j tree
          (fun t v => A.substitution.substitute τ (σ t v)) target hDirect := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j tree => ∀ {Δ Θ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (τ : Environment S A.substitution.Carrier Δ Θ) (target : Judgment A)
      (hSecond : substJudgment (substJudgment j σ) τ = target)
      (hDirect : substJudgment j
        (fun t v => A.substitution.substitute τ (σ t v)) = target),
      substTree R A (substJudgment j σ)
          (substTree R A j tree σ (substJudgment j σ) rfl) τ target hSecond =
        substTree R A j tree
          (fun t v => A.substitution.substitute τ (σ t v)) target hDirect)
    ?_ () j tree
  intro base j shape children ih
  cases base
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  intro Δ Θ σ τ target hSecond hDirect
  have envEq : ∀ (pf : conclusionJudgment R A (Instance.subst R occurrence σ) =
      substJudgment (conclusionJudgment R A occurrence) σ),
      castEnv pf τ = τ :=
    fun pf => eq_of_heq (castEnv_heq pf τ)
  have instanceEq : ∀ (pf : conclusionJudgment R A (Instance.subst R occurrence σ) =
      substJudgment (conclusionJudgment R A occurrence) σ),
      Instance.subst R (Instance.subst R occurrence σ) (castEnv pf τ) =
        Instance.subst R occurrence
          (fun t v => A.substitution.substitute τ (σ t v)) := by
    intro pf
    rw [envEq pf]
    exact Instance.subst_comp R occurrence σ τ
  refine roll_congr_instance R (instanceEq _) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  have firstChild :
      childJudgment R A (Instance.subst R occurrence σ) position =
        substJudgment (childJudgment R A occurrence position)
          (A.substitution.liftEnvironment σ
            ((R.get occurrence.index).2.premises.get position).binders) :=
    childJudgment_subst R occurrence σ position
  have liftComp :
      (fun t v => A.substitution.substitute
        (A.substitution.liftEnvironment τ
          ((R.get occurrence.index).2.premises.get position).binders)
        (A.substitution.liftEnvironment σ
          ((R.get occurrence.index).2.premises.get position).binders t v)) =
        A.substitution.liftEnvironment
          (fun t v => A.substitution.substitute τ (σ t v))
          ((R.get occurrence.index).2.premises.get position).binders := by
    funext t v
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
            (fun t v => A.substitution.substitute τ (σ t v))) position :=
    (substJudgment_comp _ _ _).trans
      ((congrArg (substJudgment (childJudgment R A occurrence position))
        liftComp).trans (childJudgment_subst R occurrence _ position).symm)
  have directOnce :
      substJudgment (childJudgment R A occurrence position)
          (fun t v => A.substitution.substitute
            (A.substitution.liftEnvironment τ
              ((R.get occurrence.index).2.premises.get position).binders)
            (A.substitution.liftEnvironment σ
              ((R.get occurrence.index).2.premises.get position).binders t v)) =
        childJudgment R A
          (Instance.subst R occurrence
            (fun t v => A.substitution.substitute τ (σ t v))) position :=
    (congrArg (substJudgment (childJudgment R A occurrence position))
      liftComp).trans (childJudgment_subst R occurrence _ position).symm
  refine HEq.trans (substTree_heq R A firstChild
      (substTree_congr R A (children position) rfl firstChild _ rfl)
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
  exact substTree_congr R A (children position) liftComp rfl _ _

section OccurrenceBaseChange

variable {A : BindingCloneAlgebra.Algebra.{u} S} {B : BindingCloneAlgebra.Algebra.{v} S}
variable (h : FreeBindingClone.Hom A B)
variable (occurrence : Instance R A) {Δ : Ctx S}
variable (σ : Environment S A.substitution.Carrier (conclusionJudgment R A occurrence).1 Δ)
variable (pf : conclusionJudgment R B (mapInstance R h occurrence) =
  mapJudgment h (conclusionJudgment R A occurrence))

/-- Base change of a substituted occurrence substitutes the base-changed
occurrence along the translated environment, through any identification of
the two conclusions. -/
theorem mapInstance_subst_transport :
    mapInstance R h (Instance.subst R occurrence σ) =
      Instance.subst R (mapInstance R h occurrence)
        (castEnv pf fun t v => h.raw.map (σ t v)) :=
  (mapInstance_subst R h occurrence σ).trans
    (congrArg (Instance.subst R (mapInstance R h occurrence))
      (eq_of_heq (castEnv_heq pf _)).symm)

/-- Beneath a premise's binders, translating the lifted environment is
lifting the translated environment. -/
theorem liftEnvironment_mapInstance
    (position : Fin (R.get occurrence.index).2.premises.length) :
    HEq (fun t v => h.raw.map (A.substitution.liftEnvironment σ
          ((R.get occurrence.index).2.premises.get position).binders t v))
      (B.substitution.liftEnvironment (castEnv pf fun t v => h.raw.map (σ t v))
        ((R.get occurrence.index).2.premises.get position).binders) :=
  heq_of_eq ((SemanticContextualMetavariables.liftEnvironment_map h σ _).trans
    (congrArg (fun env => B.substitution.liftEnvironment env
      ((R.get occurrence.index).2.premises.get position).binders)
      (eq_of_heq (castEnv_heq pf _)).symm))

/-- The premise judgments of a substituted occurrence correspond under base
change. -/
theorem childJudgment_mapInstance_subst
    (position : Fin (R.get occurrence.index).2.premises.length) :
    mapJudgment h (childJudgment R A (Instance.subst R occurrence σ) position) =
      childJudgment R B (Instance.subst R (mapInstance R h occurrence)
        (castEnv pf fun t v => h.raw.map (σ t v))) position :=
  (mapInstance_child R h (Instance.subst R occurrence σ) position).symm.trans
    (childJudgment_congr R (mapInstance_subst_transport R h occurrence σ pf)
      position position HEq.rfl)

end OccurrenceBaseChange

/-- Interpreting a firing history commutes with contextual substitution,
including each premise's distinct binder extension. -/
theorem mapTree_substTree {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (j : Judgment A) (tree : Tree R A j) :
    ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (hs : substJudgment j σ = target),
      mapTree R h target (substTree R A j tree σ target hs) =
        substTree R B (mapJudgment h j) (mapTree R h j tree)
          (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
          ((mapJudgment_substJudgment h j σ).symm.trans
            (congrArg (mapJudgment h) hs)) := by
  refine IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j tree => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (hs : substJudgment j σ = target),
      mapTree R h target (substTree R A j tree σ target hs) =
        substTree R B (mapJudgment h j) (mapTree R h j tree)
          (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
          ((mapJudgment_substJudgment h j σ).symm.trans
            (congrArg (mapJudgment h) hs)))
    ?_ () j tree
  intro base j shape children ih
  cases base
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  intro Δ σ target hs
  refine roll_congr_instance R (mapInstance_subst_transport R h occurrence σ _) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  refine HEq.trans (heq_transport _ _) ?_
  refine HEq.trans (heq_of_eq (ih position _ _ _)) ?_
  exact substTree_heq R B (mapInstance_child R h occurrence position).symm
    (heq_transport _ _).symm (liftEnvironment_mapInstance R h occurrence σ _ position)
    (childJudgment_mapInstance_subst R h occurrence σ _ position) _ _

#print axioms substTree
#print axioms substTree_identity
#print axioms substTree_comp
#print axioms mapTree_substTree

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
