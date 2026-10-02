import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalSubstitutionModel
import Mettapedia.TypeTheory.IndexedPolynomialFree

/-!
# Laws along a map from a substitution model

Evidence may carry a substitution action and rule actions without any laws
assumed. Along a map of binding clones, a family of maps from a substitution
model into such evidence that commutes with both actions carries the model's
laws to its image: acting on image evidence along image environments fixes it
under the identity, composes, and passes beneath image rule nodes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment castEnv castEnv_heq substJudgment_castEnv heq_transport
   mapJudgment_substJudgment substJudgment_identity substJudgment_comp)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (ActionOn)

universe u v w w'

variable {S : Signature}

/-! ## Congruence of actions without laws -/

section Congruence

variable {A : BindingCloneAlgebra.Algebra.{u} S} {carrier : Judgment A → Type w}

/-- Transporting indices and proof witnesses does not change an action. -/
theorem actionOn_heq (act : ActionOn A carrier)
    {j₁ j₂ : Judgment A} (sameJudgment : j₁ = j₂)
    {value₁ : carrier j₁} {value₂ : carrier j₂} (sameValue : HEq value₁ value₂) {Δ : Ctx S}
    {σ₁ : Environment S A.substitution.Carrier j₁.1 Δ}
    {σ₂ : Environment S A.substitution.Carrier j₂.1 Δ} (sameEnv : HEq σ₁ σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j₁ σ₁ = target₁) (h₂ : substJudgment j₂ σ₂ = target₂) :
    HEq (act j₁ value₁ σ₁ target₁ h₁) (act j₂ value₂ σ₂ target₂ h₂) := by
  subst sameJudgment
  cases sameValue
  cases sameEnv
  subst sameTarget
  rfl

/-- A rule action at equal judgments is determined by the occurrence and the
premise inputs, compared position by position. -/
theorem rulesAct_heq (R : List (LocalRule S))
    (rulesAlgebra : (rules R A).Algebra (fun _ judgment => carrier judgment))
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    {first second : Instance R A} (same : first = second)
    (firstConclusion : conclusionJudgment R A first = target₁)
    (secondConclusion : conclusionJudgment R A second = target₂)
    (firstChildren : ∀ position : Fin (R.get first.index).2.premises.length,
      carrier (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).2.premises.length,
      carrier (childJudgment R A second position))
    (sameChildren : ∀ firstPosition secondPosition, HEq firstPosition secondPosition →
      HEq (firstChildren firstPosition) (secondChildren secondPosition)) :
    HEq (rulesAlgebra.act () target₁ ⟨⟨first, firstConclusion⟩, firstChildren⟩)
      (rulesAlgebra.act () target₂ ⟨⟨second, secondConclusion⟩, secondChildren⟩) := by
  subst sameTarget
  exact heq_of_eq (rulesAct_congr_instance A rulesAlgebra same _ _ _ _ sameChildren)

/-- Substituted judgments agree for equal judgments and environments. -/
theorem substJudgment_congr {j j' : Judgment A} (same : j = j') {Δ : Ctx S}
    {σ : Environment S A.substitution.Carrier j.1 Δ}
    {σ' : Environment S A.substitution.Carrier j'.1 Δ} (sameEnv : HEq σ σ') :
    substJudgment j σ = substJudgment j' σ' := by
  subst same
  cases sameEnv
  rfl

/-- Substituting equal occurrences along equal environments gives equal
occurrences. -/
theorem instanceSubst_congr (R : List (LocalRule S)) {first second : Instance R A}
    (same : first = second) {Δ : Ctx S}
    {σ₁ : Environment S A.substitution.Carrier first.ambient Δ}
    {σ₂ : Environment S A.substitution.Carrier second.ambient Δ} (sameEnv : HEq σ₁ σ₂) :
    Instance.subst R first σ₁ = Instance.subst R second σ₂ := by
  subst same
  cases sameEnv
  rfl

end Congruence

/-- Rule actions read along a clone map act at the image occurrence on the
premise inputs. -/
theorem pullback_rulesMap_act {R : List (LocalRule S)} {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} (h : FreeBindingClone.Hom A B)
    {carrier : Judgment B → Type w}
    (rulesAlgebra : (rules R B).Algebra (fun _ judgment => carrier judgment))
    {j : Judgment A} (shape : (rules R A).Shape () j)
    (children : ∀ position : (rules R A).Position shape,
      carrier (mapJudgment h ((rules R A).next shape position))) :
    (IndexedRuleAlgebraPullback.pullback (rulesMap R h) rulesAlgebra).act () j ⟨shape, children⟩ =
      rulesAlgebra.act () (mapJudgment h j) ⟨mapShape R h shape, fun position =>
        ((mapInstance_child R h shape.1 position).symm ▸ children position :
          carrier (childJudgment R B (mapInstance R h shape.1) position))⟩ :=
  rfl

/-- Rule actions read along a clone map act at the image occurrence on any
premises heterogeneously equal to the given ones. -/
theorem pullback_rulesMap_act_heq {R : List (LocalRule S)} {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} (h : FreeBindingClone.Hom A B)
    {carrier : Judgment B → Type w}
    (rulesAlgebra : (rules R B).Algebra (fun _ judgment => carrier judgment))
    {j : Judgment A} (shape : (rules R A).Shape () j)
    (children : ∀ position : (rules R A).Position shape,
      carrier (mapJudgment h ((rules R A).next shape position)))
    (children' : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      carrier (childJudgment R B (mapInstance R h shape.1) position))
    (same : ∀ position, HEq (children' position) (children position)) :
    (IndexedRuleAlgebraPullback.pullback (rulesMap R h) rulesAlgebra).act () j ⟨shape, children⟩ =
      rulesAlgebra.act () (mapJudgment h j) ⟨mapShape R h shape, children'⟩ := by
  have equal : children' = fun position =>
      ((mapInstance_child R h shape.1 position).symm ▸ children position :
        carrier (childJudgment R B (mapInstance R h shape.1) position)) :=
    funext fun position => eq_of_heq ((same position).trans (heq_transport _ _).symm)
  subst equal
  exact pullback_rulesMap_act h rulesAlgebra shape children

/-- Rule actions read along a clone map, on premises mapped into the target
evidence, act at the image occurrence on the mapped premises. -/
theorem pullback_rulesMap_act_map {R : List (LocalRule S)} {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} (h : FreeBindingClone.Hom A B)
    {source : Judgment A → Type w'} {carrier : Judgment B → Type w}
    (rulesAlgebra : (rules R B).Algebra (fun _ judgment => carrier judgment))
    (map : ∀ j, source j → carrier (mapJudgment h j))
    {j : Judgment A} (shape : (rules R A).Shape () j)
    (children : ∀ position : (rules R A).Position shape, source ((rules R A).next shape position)) :
    (IndexedRuleAlgebraPullback.pullback (rulesMap R h) rulesAlgebra).act () j
        (IndexedPolynomial.Extension.map _ (fun _ j value => map j value) ⟨shape, children⟩) =
      rulesAlgebra.act () (mapJudgment h j) ⟨mapShape R h shape, fun position =>
        ((mapInstance_child R h shape.1 position).symm ▸ map _ (children position) :
          carrier (childJudgment R B (mapInstance R h shape.1) position))⟩ :=
  rfl

/-- **Folds of rule trees into rule actions read along a clone map** are
determined by their leaves and by their nodes at the image occurrences. -/
theorem fold_unique_rulesMap {R : List (LocalRule S)} {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} (h : FreeBindingClone.Hom A B)
    {holes : Unit → Judgment A → Type w'} {carrier : Judgment B → Type w}
    (rulesAlgebra : (rules R B).Algebra (fun _ judgment => carrier judgment))
    (interpret : ∀ j, holes () j → carrier (mapJudgment h j))
    (candidate : ∀ j, (rules R A).Free holes () j → carrier (mapJudgment h j))
    (onPure : ∀ j (hole : holes () j),
      candidate j (IndexedPolynomial.Free.pure (rules R A) hole) = interpret j hole)
    (onNode : ∀ j (shape : Shape R A j)
      (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
        (rules R A).Free holes () (childJudgment R A shape.1 position)),
      candidate j (IndexedPolynomial.Free.node (rules R A) shape children) =
        rulesAlgebra.act () (mapJudgment h j) ⟨mapShape R h shape, fun position =>
          ((mapInstance_child R h shape.1 position).symm ▸ candidate _ (children position) :
            carrier (childJudgment R B (mapInstance R h shape.1) position))⟩)
    (j : Judgment A) (tree : (rules R A).Free holes () j) :
    candidate j tree = IndexedPolynomial.Free.fold (rules R A) (fun _ j hole => interpret j hole)
      (IndexedRuleAlgebraPullback.pullback (rulesMap R h) rulesAlgebra) () j tree :=
  IndexedPolynomial.Free.fold_unique (rules R A) _ _ (fun _ j tree => candidate j tree)
    (fun _ j hole => onPure j hole)
    (fun _ j shape children => (onNode j shape children).trans
      (pullback_rulesMap_act h rulesAlgebra shape _).symm) () j tree

/-! ## Maps commuting with the actions -/

section Along

variable {R : List (LocalRule S)}
variable {A : BindingCloneAlgebra.Algebra.{u} S} {B : BindingCloneAlgebra.Algebra.{v} S}
variable (h : FreeBindingClone.Hom A B) (model : SubstitutionModel.{u, w} R A)
variable {carrier : Judgment B → Type w'} (act : ActionOn B carrier)
variable (rulesAlgebra : (rules R B).Algebra (fun _ judgment => carrier judgment))
variable (image : ∀ j : Judgment A, model.carrier j → carrier (mapJudgment h j))

/-- The map takes the model's substitution to the action along the clone map,
at each substituted judgment. -/
def ActsAlong : Prop :=
  ∀ (j : Judgment A) (value : model.carrier j) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier j.1 Δ),
    image (substJudgment j σ) (model.act j value σ (substJudgment j σ) rfl) =
      act (mapJudgment h j) (image j value) (fun t v => h.raw.map (σ t v))
        (mapJudgment h (substJudgment j σ)) (mapJudgment_substJudgment h j σ).symm

/-- The map takes the model's rule actions to the rule actions at the image
occurrences. -/
def RulesAlong : Prop :=
  ∀ (j : Judgment A) (shape : Shape R A j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      model.carrier (childJudgment R A shape.1 position)),
    image j (model.rules.act () j ⟨shape, children⟩) =
      rulesAlgebra.act () (mapJudgment h j) ⟨mapShape R h shape, fun position =>
        ((mapInstance_child R h shape.1 position).symm ▸ image _ (children position) :
          carrier (childJudgment R B (mapInstance R h shape.1) position))⟩

variable {h model act rulesAlgebra image}

theorem image_heq {j₁ j₂ : Judgment A} (same : j₁ = j₂) {value₁ : model.carrier j₁}
    {value₂ : model.carrier j₂} (sameValue : HEq value₁ value₂) :
    HEq (image j₁ value₁) (image j₂ value₂) := by
  subst same
  cases sameValue
  rfl

/-- The map at any target judgment, through the substituted one. -/
theorem ActsAlong.at_target (acts : ActsAlong h model act image) (j : Judgment A)
    (value : model.carrier j) {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (same : substJudgment j σ = target) (target' : Judgment B)
    (same' : substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v)) = target') :
    HEq (image target (model.act j value σ target same))
      (act (mapJudgment h j) (image j value) (fun t v => h.raw.map (σ t v)) target' same') := by
  subst same
  refine (heq_of_eq (acts j value σ)).trans ?_
  exact actionOn_heq act rfl HEq.rfl HEq.rfl
    ((mapJudgment_substJudgment h j σ).trans same') _ _

/-- **Image evidence is fixed by the identity environment.** -/
theorem identity_along (acts : ActsAlong h model act image) (j : Judgment A)
    (value : model.carrier j)
    (same : substJudgment (mapJudgment h j) (fun _ v => B.substitution.injectVar v) =
      mapJudgment h j) :
    act (mapJudgment h j) (image j value) (fun _ v => B.substitution.injectVar v)
      (mapJudgment h j) same = image j value := by
  have environment : (fun _ v => h.raw.map (A.substitution.injectVar v) :
      Environment S B.substitution.Carrier (mapJudgment h j).1 (mapJudgment h j).1) =
      fun _ v => B.substitution.injectVar v :=
    funext fun _ => funext fun v => h.raw.map_variable v
  have moved := acts.at_target j value (fun _ v => A.substitution.injectVar v) j
    (substJudgment_identity j) (mapJudgment h j)
    ((congrArg (substJudgment (mapJudgment h j)) environment).trans same)
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq (congrArg (image j)
    (model.act_identity j value (substJudgment_identity j)))).symm.trans moved).symm)
  exact actionOn_heq act rfl HEq.rfl (heq_of_eq environment).symm rfl _ _

/-- **Acting on image evidence twice is acting along the composite.** -/
theorem comp_along (acts : ActsAlong h model act image) (j : Judgment A)
    (value : model.carrier j) {Δ Θ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (τ : Environment S A.substitution.Carrier Δ Θ) (target : Judgment B)
    (second : substJudgment (substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v)))
      (fun t v => h.raw.map (τ t v)) = target)
    (direct : substJudgment (mapJudgment h j)
      (fun t v => B.substitution.substitute (fun r w => h.raw.map (τ r w)) (h.raw.map (σ t v))) =
        target) :
    act (substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v)))
        (act (mapJudgment h j) (image j value) (fun t v => h.raw.map (σ t v))
          (substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v))) rfl)
        (fun t v => h.raw.map (τ t v)) target second =
      act (mapJudgment h j) (image j value)
        (fun t v => B.substitution.substitute (fun r w => h.raw.map (τ r w)) (h.raw.map (σ t v)))
        target direct := by
  have middle : mapJudgment h (substJudgment j σ) =
      substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v)) :=
    mapJudgment_substJudgment h j σ
  have environment : (fun t v => h.raw.map (A.substitution.substitute τ (σ t v)) :
      Environment S B.substitution.Carrier (mapJudgment h j).1 Θ) =
      fun t v => B.substitution.substitute (fun r w => h.raw.map (τ r w)) (h.raw.map (σ t v)) :=
    funext fun t => funext fun v => h.map_substitute τ (σ t v)
  have composite : substJudgment (mapJudgment h j)
      (fun t v => h.raw.map (A.substitution.substitute τ (σ t v))) = target :=
    (congrArg (substJudgment (mapJudgment h j)) environment).trans direct
  have atTarget : mapJudgment h (substJudgment (substJudgment j σ) τ) = target :=
    (congrArg (mapJudgment h) (substJudgment_comp j σ τ)).trans
      ((mapJudgment_substJudgment h j _).trans composite)
  have inner := acts.at_target j value σ (substJudgment j σ) rfl
    (substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v))) rfl
  have outer := acts.at_target (substJudgment j σ) (model.act j value σ (substJudgment j σ) rfl) τ
    (substJudgment (substJudgment j σ) τ) rfl target
    ((mapJudgment_substJudgment h (substJudgment j σ) τ).symm.trans atTarget)
  have composed := model.act_comp j value σ τ (substJudgment (substJudgment j σ) τ) rfl
    (substJudgment_comp j σ τ).symm
  have direct' := acts.at_target j value (fun t v => A.substitution.substitute τ (σ t v))
    (substJudgment (substJudgment j σ) τ) (substJudgment_comp j σ τ).symm target composite
  refine eq_of_heq (HEq.trans ?_ ((outer.symm.trans (heq_of_eq (congrArg
    (image (substJudgment (substJudgment j σ) τ)) composed))).trans
      (direct'.trans (actionOn_heq act rfl HEq.rfl (heq_of_eq environment) rfl _ _))))
  exact actionOn_heq act middle.symm inner.symm HEq.rfl rfl _ _

/-- **Substitution passes beneath image rule nodes.** -/
theorem rules_along (acts : ActsAlong h model act image)
    (rulesAlong : RulesAlong h model rulesAlgebra image) (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      model.carrier (childJudgment R A occurrence position))
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier occurrence.ambient Δ)
    (target : Judgment B)
    (same : substJudgment (mapJudgment h (conclusionJudgment R A occurrence))
      (fun t v => h.raw.map (σ t v)) = target) :
    act (mapJudgment h (conclusionJudgment R A occurrence))
        (rulesAlgebra.act () (mapJudgment h (conclusionJudgment R A occurrence))
          ⟨mapShape R h ⟨occurrence, rfl⟩, fun position =>
            ((mapInstance_child R h occurrence position).symm ▸ image _ (children position) :
              carrier (childJudgment R B (mapInstance R h occurrence) position))⟩)
        (fun t v => h.raw.map (σ t v)) target same =
      rulesAlgebra.act () target
        ⟨⟨Instance.subst R (mapInstance R h occurrence)
            (castEnv (mapShape R h ⟨occurrence, rfl⟩).2 (fun t v => h.raw.map (σ t v))),
          (conclusionJudgment_subst R (mapInstance R h occurrence)
            (castEnv (mapShape R h ⟨occurrence, rfl⟩).2 (fun t v => h.raw.map (σ t v)))).trans
            ((substJudgment_castEnv _ _).trans same)⟩,
          fun position => act _ ((mapInstance_child R h occurrence position).symm ▸
              image _ (children position) :
                carrier (childJudgment R B (mapInstance R h occurrence) position))
            (B.substitution.liftEnvironment
              (castEnv (mapShape R h ⟨occurrence, rfl⟩).2 (fun t v => h.raw.map (σ t v)))
              ((R.get occurrence.index).2.premises.get position).binders)
            (childJudgment R B (Instance.subst R (mapInstance R h occurrence)
              (castEnv (mapShape R h ⟨occurrence, rfl⟩).2 (fun t v => h.raw.map (σ t v))))
                position)
            (childJudgment_subst R (mapInstance R h occurrence)
              (castEnv (mapShape R h ⟨occurrence, rfl⟩).2 (fun t v => h.raw.map (σ t v)))
              position).symm⟩ := by
  let node := model.rules.act () (conclusionJudgment R A occurrence) ⟨⟨occurrence, rfl⟩, children⟩
  have atNode : image _ node = rulesAlgebra.act () (mapJudgment h (conclusionJudgment R A occurrence))
      ⟨mapShape R h ⟨occurrence, rfl⟩, fun position =>
        ((mapInstance_child R h occurrence position).symm ▸ image _ (children position) :
          carrier (childJudgment R B (mapInstance R h occurrence) position))⟩ :=
    rulesAlong _ ⟨occurrence, rfl⟩ children
  have substituted := acts.at_target _ node σ _ rfl target same
  have beneath := congrArg (image _) (model.act_rules ⟨occurrence, rfl⟩ children σ _ rfl)
  refine eq_of_heq ((actionOn_heq act rfl (heq_of_eq atNode).symm HEq.rfl rfl _ same).trans
    (substituted.symm.trans ((heq_of_eq (beneath.trans (rulesAlong _ _ _))).trans ?_)))
  refine rulesAct_heq R rulesAlgebra
    ((mapJudgment_substJudgment h (conclusionJudgment R A occurrence) σ).trans same)
    (mapInstance_subst_transport R h occurrence σ _) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  refine (heq_transport _ _).trans ?_
  refine (acts.at_target (childJudgment R A occurrence position) (children position)
    (A.substitution.liftEnvironment σ ((R.get occurrence.index).2.premises.get position).binders)
    (childJudgment R A (Instance.subst R occurrence σ) position)
    (childJudgment_subst R occurrence σ position).symm _
    ((mapJudgment_substJudgment h _ _).symm.trans
      (congrArg (mapJudgment h) (childJudgment_subst R occurrence σ position).symm))).trans ?_
  exact actionOn_heq act (mapInstance_child R h occurrence position).symm
    (heq_transport _ _).symm (liftEnvironment_mapInstance R h occurrence σ _ position)
    (childJudgment_mapInstance_subst R h occurrence σ _ position) _ _

/-- **Substitution passes beneath a rule node whose occurrence, premises and
environment are read from images.** This is the rule law at such inputs. -/
theorem rulesLaw_along (acts : ActsAlong h model act image)
    (rulesAlong : RulesAlong h model rulesAlgebra image) (source : Instance R A)
    (sourceChildren : ∀ position : Fin (R.get source.index).2.premises.length,
      model.carrier (childJudgment R A source position))
    {Δ : Ctx S} (sourceEnv : Environment S A.substitution.Carrier source.ambient Δ)
    {j : Judgment B} (shape : Shape R B j) (reading : mapInstance R h source = shape.1)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      carrier (childJudgment R B shape.1 position))
    (sameChildren : ∀ position position', HEq position position' →
      HEq (children position) (image _ (sourceChildren position')))
    (σ : Environment S B.substitution.Carrier j.1 Δ)
    (sameEnv : HEq (fun t v => h.raw.map (sourceEnv t v)) σ)
    (target : Judgment B) (same : substJudgment j σ = target) :
    act j (rulesAlgebra.act () j ⟨shape, children⟩) σ target same =
      rulesAlgebra.act () target
        ⟨⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans same)⟩,
          fun position => act _ (children position)
            (B.substitution.liftEnvironment (castEnv shape.2 σ)
              ((R.get shape.1.index).2.premises.get position).binders)
            (childJudgment R B (Instance.subst R shape.1 (castEnv shape.2 σ)) position)
            (childJudgment_subst R shape.1 (castEnv shape.2 σ) position).symm⟩ := by
  obtain ⟨occurrence, conclusion⟩ := shape
  subst conclusion
  subst reading
  have environment : (fun t v => h.raw.map (sourceEnv t v)) = σ := eq_of_heq sameEnv
  subst environment
  have judgmentEq := mapInstance_conclusion R h source
  have law := rules_along acts rulesAlong source sourceChildren sourceEnv target
    ((substJudgment_congr judgmentEq.symm HEq.rfl).trans same)
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq law).trans ?_))
  · refine actionOn_heq act judgmentEq ?_ HEq.rfl rfl same _
    refine rulesAct_heq R rulesAlgebra judgmentEq rfl _ _ _ _ ?_
    intro position position' samePosition
    exact (sameChildren position position' samePosition).trans (heq_transport _ _).symm
  · have environment : castEnv (mapShape R h ⟨source, rfl⟩).2 (fun t v => h.raw.map (sourceEnv t v)) =
        castEnv (rfl : conclusionJudgment R B (mapInstance R h source) =
          conclusionJudgment R B (mapInstance R h source))
          (fun t v => h.raw.map (sourceEnv t v)) :=
      eq_of_heq ((castEnv_heq _ _).trans (castEnv_heq (rfl : conclusionJudgment R B
        (mapInstance R h source) = conclusionJudgment R B (mapInstance R h source))
          (fun t v => h.raw.map (sourceEnv t v))).symm)
    have occurrenceEq := instanceSubst_congr R rfl (heq_of_eq environment)
    refine rulesAct_heq R rulesAlgebra rfl occurrenceEq _ _ _ _ ?_
    intro position position' samePosition
    cases samePosition
    refine actionOn_heq act rfl ((heq_transport _ _).trans
      (sameChildren position position HEq.rfl).symm) ?_
      (childJudgment_congr R occurrenceEq position position HEq.rfl) _ _
    exact heq_of_eq (congrArg (fun environment => B.substitution.liftEnvironment environment
      ((R.get source.index).2.premises.get position).binders) environment)

end Along

/-- **A family of maps commuting with both actions along a clone map is a map
into the target model read along the clone map.** -/
theorem isHom_of_along {R : List (LocalRule S)} {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} {h : FreeBindingClone.Hom A B}
    {model : SubstitutionModel.{u, w} R A} {target : SubstitutionModel.{v, w'} R B}
    {image : ∀ j : Judgment A, model.carrier j → target.carrier (mapJudgment h j)}
    (acts : ActsAlong h model target.act image) (rulesAlong : RulesAlong h model target.rules image) :
    SubstitutionModel.IsHom R A model (target.pullback h) image where
  rules j layer := by
    obtain ⟨shape, children⟩ := layer
    exact (rulesAlong j shape children).trans
      (pullback_rulesMap_act h target.rules shape (fun position => image _ (children position))).symm
  act j value _ σ targetJudgment same :=
    eq_of_heq (acts.at_target j value σ targetJudgment same _ _)


end Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
