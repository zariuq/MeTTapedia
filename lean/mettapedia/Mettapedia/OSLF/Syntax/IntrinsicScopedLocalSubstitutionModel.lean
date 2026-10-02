import Mettapedia.OSLF.Syntax.IntrinsicScopedJudgmentAction
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraPullback

/-!
# Substitution models of a rule-local presentation

Over a binding algebra, a substitution model carries a contextual
substitution action on judgment-indexed evidence and an action of every
rule-local constructor, with substitution passing beneath rule nodes and under
each premise's binders. Its evidence may live in any universe. Maps preserve
both the rule actions and the substitution action.

A model can be read along a binding-clone map: evidence at a judgment is
evidence at its image.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment castEnv castEnv_heq substJudgment_castEnv heq_transport
   mapJudgment_substJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (JudgmentAction ActionOn)

universe u w w₁ w₂ w₃ w₄

variable {S : Signature}
variable (R : List (LocalRule S))
variable (A : BindingCloneAlgebra.Algebra.{u} S)

/-- Substitution passes beneath every rule node, under each premise's own
binders. -/
abbrev RulesLaw {carrier : Judgment A → Type w} (act : ActionOn A carrier)
    (rulesAlgebra : (rules R A).Algebra (fun _ judgment => carrier judgment)) : Prop :=
  ∀ {j : Judgment A} (shape : Shape R A j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      carrier (childJudgment R A shape.1 position))
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (h : substJudgment j σ = target),
    act j (rulesAlgebra.act () j ⟨shape, children⟩) σ target h =
      rulesAlgebra.act () target
        ⟨⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans h)⟩,
          fun position => act _ (children position)
            (A.substitution.liftEnvironment (castEnv shape.2 σ)
              ((R.get shape.1.index).2.premises.get position).binders)
            (childJudgment R A (Instance.subst R shape.1 (castEnv shape.2 σ))
              position)
            (childJudgment_subst R shape.1 (castEnv shape.2 σ) position).symm⟩

/-- A rule-local operational model interprets each declaration using only
its own metavariable telescope. Its evidence carries contextual substitution,
which passes beneath rule nodes and under each premise's binders. -/
structure SubstitutionModel extends toAction : JudgmentAction.{u, w} A where
  rules : (rules R A).Algebra (fun _ judgment => carrier judgment)
  act_rules : RulesLaw R A act rules

/-- Maps preserve rule actions and contextual substitution on every event. -/
structure SubstitutionModel.Hom
    (X : SubstitutionModel.{u, w₁} R A) (Y : SubstitutionModel.{u, w₂} R A) where
  evidence : IndexedPolynomial.Algebra.Hom X.rules Y.rules
  preserves : ∀ (j : Judgment A) (value : X.carrier j)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (h : substJudgment j σ = target),
    evidence.toFun () target (X.act j value σ target h) =
      Y.act j (evidence.toFun () j value) σ target h

@[ext] theorem SubstitutionModel.Hom.ext
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{u, w₂} R A}
    {f g : SubstitutionModel.Hom R A X Y}
    (same : f.evidence = g.evidence) : f = g := by
  cases f
  cases g
  cases same
  rfl

def SubstitutionModel.Hom.id (model : SubstitutionModel.{u, w} R A) :
    SubstitutionModel.Hom R A model model where
  evidence := IndexedPolynomial.Algebra.Hom.id model.rules
  preserves := by
    intro judgment value Δ σ target h
    rfl

def SubstitutionModel.Hom.comp
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{u, w₂} R A}
    {Z : SubstitutionModel.{u, w₃} R A}
    (first : SubstitutionModel.Hom R A X Y)
    (second : SubstitutionModel.Hom R A Y Z) :
    SubstitutionModel.Hom R A X Z where
  evidence := IndexedPolynomial.Algebra.Hom.comp first.evidence second.evidence
  preserves := by
    intro judgment value Δ σ target h
    change second.evidence.toFun () target
        (first.evidence.toFun () target (X.act judgment value σ target h)) =
      Z.act judgment
        (second.evidence.toFun () judgment
          (first.evidence.toFun () judgment value)) σ target h
    rw [first.preserves, second.preserves]

theorem SubstitutionModel.Hom.id_comp
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{u, w₂} R A}
    (f : SubstitutionModel.Hom R A X Y) :
    SubstitutionModel.Hom.comp R A
      (SubstitutionModel.Hom.id R A X) f = f := by
  apply SubstitutionModel.Hom.ext
  exact IndexedPolynomial.Algebra.Hom.id_comp f.evidence

theorem SubstitutionModel.Hom.comp_id
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{u, w₂} R A}
    (f : SubstitutionModel.Hom R A X Y) :
    SubstitutionModel.Hom.comp R A f
      (SubstitutionModel.Hom.id R A Y) = f := by
  apply SubstitutionModel.Hom.ext
  exact IndexedPolynomial.Algebra.Hom.comp_id f.evidence

theorem SubstitutionModel.Hom.assoc
    {W : SubstitutionModel.{u, w₁} R A} {X : SubstitutionModel.{u, w₂} R A}
    {Y : SubstitutionModel.{u, w₃} R A} {Z : SubstitutionModel.{u, w₄} R A}
    (f : SubstitutionModel.Hom R A W X)
    (g : SubstitutionModel.Hom R A X Y)
    (h : SubstitutionModel.Hom R A Y Z) :
    SubstitutionModel.Hom.comp R A
      (SubstitutionModel.Hom.comp R A f g) h =
    SubstitutionModel.Hom.comp R A f
      (SubstitutionModel.Hom.comp R A g h) := by
  apply SubstitutionModel.Hom.ext
  exact IndexedPolynomial.Algebra.Hom.comp_assoc f.evidence g.evidence h.evidence

/-- A family of maps of evidence commuting with the rule actions and with
substitution. -/
structure SubstitutionModel.IsHom
    (X : SubstitutionModel.{u, w₁} R A) (Y : SubstitutionModel.{u, w₂} R A)
    (toFun : ∀ j : Judgment A, X.carrier j → Y.carrier j) : Prop where
  rules : ∀ (j : Judgment A)
    (layer : (IntrinsicScopedLocalPolynomial.rules R A).Extension
      (fun _ judgment => X.carrier judgment) () j),
    toFun j (X.rules.act () j layer) =
      Y.rules.act () j (IndexedPolynomial.Extension.map _ (fun _ j => toFun j) layer)
  act : ∀ (j : Judgment A) (value : X.carrier j)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (h : substJudgment j σ = target),
    toFun target (X.act j value σ target h) = Y.act j (toFun j value) σ target h

/-- The map of models with a given underlying map of evidence. -/
def SubstitutionModel.Hom.ofIsHom
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{u, w₂} R A}
    (toFun : ∀ j : Judgment A, X.carrier j → Y.carrier j)
    (isHom : SubstitutionModel.IsHom R A X Y toFun) :
    SubstitutionModel.Hom R A X Y where
  evidence :=
    { toFun := fun _ j => toFun j
      commutes := fun base j layer => by
        cases base
        exact isHom.rules j layer }
  preserves := isHom.act

theorem SubstitutionModel.Hom.isHom
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{u, w₂} R A}
    (hom : SubstitutionModel.Hom R A X Y) :
    SubstitutionModel.IsHom R A X Y (fun j => hom.evidence.toFun () j) where
  rules j layer := hom.evidence.commutes () j layer
  act := hom.preserves

/-- Being a map of models depends only on the values of the evidence map. -/
theorem SubstitutionModel.IsHom.congr
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{u, w₂} R A}
    {first second : ∀ j : Judgment A, X.carrier j → Y.carrier j}
    (same : ∀ j value, first j value = second j value)
    (isHom : SubstitutionModel.IsHom R A X Y first) :
    SubstitutionModel.IsHom R A X Y second := by
  have equal : first = second := funext fun j => funext fun value => same j value
  subst equal
  exact isHom

instance : CategoryTheory.Category (SubstitutionModel.{u, w} R A) where
  Hom := SubstitutionModel.Hom R A
  id := SubstitutionModel.Hom.id R A
  comp := SubstitutionModel.Hom.comp R A
  id_comp := SubstitutionModel.Hom.id_comp R A
  comp_id := SubstitutionModel.Hom.comp_id R A
  assoc := SubstitutionModel.Hom.assoc R A


/-- Models with the same action and the same rule actions are equal. -/
theorem SubstitutionModel.ext {first second : SubstitutionModel.{u, w} R A}
    (action : first.toAction = second.toAction) (sameRules : HEq first.rules second.rules) :
    first = second := by
  obtain ⟨firstAction, firstRules, _⟩ := first
  obtain ⟨secondAction, secondRules, _⟩ := second
  cases action
  cases sameRules
  rfl

/-! ## Reading a model along a binding-clone map -/

section Pullback

universe v v'

variable {R}

/-- A rule action is determined by the occurrence and the premise inputs,
compared position by position. -/
theorem rulesAct_congr_instance {carrier : Judgment A → Type w}
    (rulesAlgebra : (rules R A).Algebra (fun _ judgment => carrier judgment))
    {target : Judgment A} {first second : Instance R A} (same : first = second)
    (firstConclusion : conclusionJudgment R A first = target)
    (secondConclusion : conclusionJudgment R A second = target)
    (firstChildren : ∀ position : Fin (R.get first.index).2.premises.length,
      carrier (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).2.premises.length,
      carrier (childJudgment R A second position))
    (sameChildren : ∀ firstPosition secondPosition, HEq firstPosition secondPosition →
      HEq (firstChildren firstPosition) (secondChildren secondPosition)) :
    rulesAlgebra.act () target ⟨⟨first, firstConclusion⟩, firstChildren⟩ =
      rulesAlgebra.act () target ⟨⟨second, secondConclusion⟩, secondChildren⟩ := by
  subst same
  have children : firstChildren = secondChildren :=
    funext fun position => eq_of_heq (sameChildren position position HEq.rfl)
  subst children
  rfl

variable {A} {B : BindingCloneAlgebra.Algebra.{v} S}

/-- Read a substitution model along a binding-clone map. -/
noncomputable def SubstitutionModel.pullback (h : FreeBindingClone.Hom A B)
    (model : SubstitutionModel.{v, w} R B) : SubstitutionModel.{u, w} R A where
  toAction := model.toAction.pullback h
  rules := IndexedRuleAlgebraPullback.pullback (rulesMap R h) model.rules
  act_rules := by
    intro judgment shape children Δ σ target same
    obtain ⟨occurrence, conclusion⟩ := shape
    subst conclusion
    refine (model.act_rules (mapShape R h ⟨occurrence, rfl⟩)
      (fun position => (mapInstance_child R h occurrence position).symm ▸
        children position) _ _ _).trans ?_
    refine rulesAct_congr_instance B model.rules
      (mapInstance_subst_transport R h occurrence σ _).symm _ _ _ _ ?_
    intro position otherPosition samePosition
    cases samePosition
    refine HEq.trans ?_ (heq_transport _ _).symm
    exact model.toAction.act_heq (mapInstance_child R h occurrence position)
      (heq_transport _ _) (liftEnvironment_mapInstance R h occurrence σ _ position).symm
      (childJudgment_mapInstance_subst R h occurrence σ _ position).symm _ _

/-- Reading along a composite map is reading along each map in turn. -/
theorem SubstitutionModel.pullback_comp {C : BindingCloneAlgebra.Algebra.{v} S}
    {B : BindingCloneAlgebra.Algebra.{v'} S} (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C) (model : SubstitutionModel.{v, w} R C) :
    SubstitutionModel.pullback (FreeBindingClone.Hom.comp first second) model =
      SubstitutionModel.pullback first (SubstitutionModel.pullback second model) :=
  SubstitutionModel.ext R A rfl (heq_of_eq (IndexedRuleAlgebraPullback.pullback_comp
    (rulesMap R first) (rulesMap R second) model.rules))

/-- The rule actions read along a composite map are those read along each
map in turn. -/
theorem SubstitutionModel.pullback_comp_rules_act {C : BindingCloneAlgebra.Algebra.{v} S}
    {B : BindingCloneAlgebra.Algebra.{v'} S} (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C) (model : SubstitutionModel.{v, w} R C)
    (j : Judgment A)
    (layer : (IntrinsicScopedLocalPolynomial.rules R A).Extension
      (fun _ judgment => model.carrier (mapJudgment second (mapJudgment first judgment))) () j) :
    (SubstitutionModel.pullback (FreeBindingClone.Hom.comp first second) model).rules.act () j
        layer =
      (SubstitutionModel.pullback first (SubstitutionModel.pullback second model)).rules.act () j
        layer :=
  congrArg (fun algebra => algebra.act () j layer)
    (IndexedRuleAlgebraPullback.pullback_comp (rulesMap R first) (rulesMap R second) model.rules)

/-- Read a map of models along a binding-clone map. -/
noncomputable def SubstitutionModel.Hom.pullback (h : FreeBindingClone.Hom A B)
    {first : SubstitutionModel.{v, w₁} R B} {second : SubstitutionModel.{v, w₂} R B}
    (hom : SubstitutionModel.Hom R B first second) :
    SubstitutionModel.Hom R A (first.pullback h) (second.pullback h) where
  evidence := IndexedRuleAlgebraPullback.pullbackHom (rulesMap R h) hom.evidence
  preserves := fun j value _ σ target same =>
    hom.preserves (mapJudgment h j) value (fun t w => h.raw.map (σ t w)) (mapJudgment h target)
      ((mapJudgment_substJudgment h j σ).symm.trans (congrArg (mapJudgment h) same))

/-- Maps into models read along clone maps compose to a map into the model
read along the composite. -/
theorem SubstitutionModel.IsHom.comp_pullback {C : BindingCloneAlgebra.Algebra.{v'} S}
    {X : SubstitutionModel.{u, w₁} R A} {Y : SubstitutionModel.{v, w₂} R B}
    {W : SubstitutionModel.{v', w₃} R C}
    (first : FreeBindingClone.Hom A B) (second : FreeBindingClone.Hom B C)
    {F : ∀ j : Judgment A, X.carrier j → Y.carrier (mapJudgment first j)}
    {G : ∀ j : Judgment B, Y.carrier j → W.carrier (mapJudgment second j)}
    (isF : SubstitutionModel.IsHom R A X (Y.pullback first) F)
    (isG : SubstitutionModel.IsHom R B Y (W.pullback second) G) :
    SubstitutionModel.IsHom R A X (W.pullback (FreeBindingClone.Hom.comp first second))
      (fun j value => G (mapJudgment first j) (F j value)) := by
  have both := (SubstitutionModel.Hom.comp R A (SubstitutionModel.Hom.ofIsHom R A F isF)
    (SubstitutionModel.Hom.pullback first
      (SubstitutionModel.Hom.ofIsHom R B (X := Y) (Y := W.pullback second) G isG))).isHom
  exact
    { rules := fun j layer => (both.rules j layer).trans
        (SubstitutionModel.pullback_comp_rules_act first second W j _).symm
      act := both.act }

end Pullback

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
