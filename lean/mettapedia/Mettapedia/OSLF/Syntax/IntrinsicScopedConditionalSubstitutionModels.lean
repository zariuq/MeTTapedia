import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitution
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraCategory

/-!
# Operational models carrying the contextual substitution action

Over one binding clone, a substitution model interprets every intrinsic
scoped conditional rule and also lets contextual substitutions act on its
evidence. The action satisfies the identity and composition laws and
commutes with every rule constructor, substituting each premise beneath its
own binders. Its maps preserve both the rule constructors and the action.

The free firing trees with `substTree` form such a model, and the fold into
any substitution model preserves the action. Hence the free model is initial
among substitution models: firing evidence and term substitution are
interpreted together, uniquely.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

open CategoryTheory CategoryTheory.Limits
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial

universe u

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- A proof-relevant interpretation of the intrinsic conditional rules over
one binding clone, with a contextual substitution action on its evidence. -/
structure SubstitutionModel (A : BindingCloneAlgebra.Algebra.{u} S) where
  evidence : OperationalRuleModels.Model (rules R A)
  act : ∀ (j : Judgment A), evidence.carrier () j →
    ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A), substJudgment j σ = target →
        evidence.carrier () target
  act_rules : ∀ {j : Judgment A} (shape : Shape R A j)
    (children : ∀ position : Fin (R.get shape.1.index).premises.length,
      evidence.carrier () (childJudgment R A shape.1 position))
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (h : substJudgment j σ = target),
    act j (evidence.rules.act () j ⟨shape, children⟩) σ target h =
      evidence.rules.act () target
        ⟨⟨Instance.subst R shape.1 (castEnv shape.2 σ),
          (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
            ((substJudgment_castEnv shape.2 σ).trans h)⟩,
          fun position => act _ (children position)
            (A.substitution.liftEnvironment (castEnv shape.2 σ)
              ((R.get shape.1.index).premises.get position).binders)
            (childJudgment R A (Instance.subst R shape.1 (castEnv shape.2 σ))
              position)
            (childJudgment_subst R shape.1 (castEnv shape.2 σ) position).symm⟩
  act_identity : ∀ (j : Judgment A) (value : evidence.carrier () j)
    (h : substJudgment j (fun _ v => A.substitution.injectVar v) = j),
    act j value (fun _ v => A.substitution.injectVar v) j h = value
  act_comp : ∀ (j : Judgment A) (value : evidence.carrier () j) {Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier j.1 Δ)
    (τ : Environment S A.substitution.Carrier Δ Θ) (target : Judgment A)
    (hSecond : substJudgment (substJudgment j σ) τ = target)
    (hDirect : substJudgment j
      (fun t v => A.substitution.substitute τ (σ t v)) = target),
    act (substJudgment j σ) (act j value σ (substJudgment j σ) rfl) τ target
        hSecond =
      act j value (fun t v => A.substitution.substitute τ (σ t v)) target
        hDirect

namespace SubstitutionModel

variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- A map of substitution models preserves the rule constructors and the
contextual substitution action. -/
structure Hom (X Y : SubstitutionModel R A) where
  evidence : X.evidence ⟶ Y.evidence
  preserves : ∀ (j : Judgment A) (value : X.evidence.carrier () j)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (h : substJudgment j σ = target),
    evidence.toFun () target (X.act j value σ target h) =
      Y.act j (evidence.toFun () j value) σ target h

variable {R}

@[ext] theorem Hom.ext {X Y : SubstitutionModel R A} {f g : Hom R X Y}
    (same : f.evidence = g.evidence) : f = g := by
  cases f
  cases g
  cases same
  rfl

def Hom.id (X : SubstitutionModel R A) : Hom R X X where
  evidence := 𝟙 X.evidence
  preserves := by
    intro j value Δ σ target h
    rfl

def Hom.comp {X Y Z : SubstitutionModel R A}
    (f : Hom R X Y) (g : Hom R Y Z) : Hom R X Z where
  evidence := f.evidence ≫ g.evidence
  preserves := by
    intro j value Δ σ target h
    change g.evidence.toFun () target
        (f.evidence.toFun () target (X.act j value σ target h)) =
      Z.act j (g.evidence.toFun () j (f.evidence.toFun () j value)) σ target h
    rw [f.preserves, g.preserves]

instance category : Category (SubstitutionModel R A) where
  Hom := Hom R
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro X Y f
    apply Hom.ext
    exact Category.id_comp f.evidence
  comp_id := by
    intro X Y f
    apply Hom.ext
    exact Category.comp_id f.evidence
  assoc := by
    intro W X Y Z f g h
    apply Hom.ext
    exact Category.assoc f.evidence g.evidence h.evidence

variable (R)

/-- Free firing trees with their substitution action. -/
noncomputable def free (A : BindingCloneAlgebra.Algebra.{u} S) :
    SubstitutionModel R A where
  evidence := OperationalRuleModels.free (rules R A)
  act := substTree R A
  act_rules := by
    intro j shape children Δ σ target h
    rfl
  act_identity := substTree_identity R A
  act_comp := substTree_comp R A

/-- The fold into a substitution model preserves the substitution action. -/
theorem fold_substTree (Y : SubstitutionModel R A) (j : Judgment A)
    (tree : Tree R A j) :
    ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (h : substJudgment j σ = target),
      IndexedPolynomial.Fix.fold (rules R A) Y.evidence.rules.act () target
          (substTree R A j tree σ target h) =
        Y.act j (IndexedPolynomial.Fix.fold (rules R A) Y.evidence.rules.act
          () j tree) σ target h := by
  refine IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j tree => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (h : substJudgment j σ = target),
      IndexedPolynomial.Fix.fold (rules R A) Y.evidence.rules.act () target
          (substTree R A j tree σ target h) =
        Y.act j (IndexedPolynomial.Fix.fold (rules R A) Y.evidence.rules.act
          () j tree) σ target h)
    ?_ () j tree
  intro base j shape children ih
  cases base
  intro Δ σ target h
  refine Eq.trans ?_ (Y.act_rules shape
    (fun position => IndexedPolynomial.Fix.fold (rules R A)
      Y.evidence.rules.act () _ (children position)) σ target h).symm
  exact congrArg
    (fun values => Y.evidence.rules.act () target
      ⟨⟨Instance.subst R shape.1 (castEnv shape.2 σ),
        (conclusionJudgment_subst R shape.1 (castEnv shape.2 σ)).trans
          ((substJudgment_castEnv shape.2 σ).trans h)⟩, values⟩)
    (funext fun position => ih position _ _ _)

/-- The fold, as a map of substitution models. -/
noncomputable def foldHom (Y : SubstitutionModel R A) :
    Hom R (free R A) Y where
  evidence := IndexedPolynomial.Algebra.foldHom Y.evidence.rules
  preserves := fun j value _ σ target h => fold_substTree R Y j value σ target h

/-- Free firing trees are initial among models whose evidence carries the
contextual substitution action: rule actions and substitution are
interpreted together and uniquely. -/
noncomputable def freeIsInitial (A : BindingCloneAlgebra.Algebra.{u} S) :
    IsInitial (free R A) :=
  IsInitial.ofUniqueHom (fun Y => foldHom R Y) (fun Y f => by
    apply Hom.ext
    apply IndexedPolynomial.Algebra.Hom.ext
    intro base index tree
    exact IndexedPolynomial.Algebra.hom_eq_fold Y.evidence.rules f.evidence
      base index tree)

end SubstitutionModel

/-! ## Varying the binding-equation base -/

section BaseChange

open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (mapJudgment)

variable {A B : BindingCloneAlgebra.Algebra.{u} S}

/-- A base map commutes with substituting a rule occurrence. -/
theorem mapInstance_subst (h : FreeBindingClone.Hom A B)
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    mapInstance R h (Instance.subst R occurrence σ) =
      Instance.subst R (mapInstance R h occurrence)
        (fun t v => h.raw.map (σ t v)) := by
  obtain ⟨index, ambient, valuation, close⟩ := occurrence
  have valuationEq :
      mapValuation h (substValuation A σ valuation) =
        substValuation B (fun t v => h.raw.map (σ t v))
          (mapValuation h valuation) := by
    funext k
    change h.raw.map (A.substitution.substitute
        (A.substitution.liftEnvironment σ (M.get k).1) (valuation k)) =
      B.substitution.substitute
        (B.substitution.liftEnvironment (fun t v => h.raw.map (σ t v))
          (M.get k).1) (h.raw.map (valuation k))
    rw [h.map_substitute, liftEnvironment_map h σ (M.get k).1]
  have closeEq :
      (fun t v => h.raw.map (A.substitution.substitute σ (close t v))) =
        (fun t v => B.substitution.substitute (fun r w => h.raw.map (σ r w))
          (h.raw.map (close t v))) := by
    funext t v
    exact h.map_substitute σ (close t v)
  change (⟨index, Δ, mapValuation h (substValuation A σ valuation),
      fun t v => h.raw.map (A.substitution.substitute σ (close t v))⟩ :
        Instance R B) =
    ⟨index, Δ,
      substValuation B (fun t v => h.raw.map (σ t v)) (mapValuation h valuation),
      fun t v => B.substitution.substitute (fun r w => h.raw.map (σ r w))
        (h.raw.map (close t v))⟩
  rw [valuationEq, closeEq]

/-- A base map commutes with substituting a judgment. -/
theorem mapJudgment_substJudgment (h : FreeBindingClone.Hom A B)
    (j : Judgment A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier j.1 Δ) :
    mapJudgment h (substJudgment j σ) =
      substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v)) := by
  obtain ⟨Γ, sort, source, target⟩ := j
  change (⟨Δ, sort, h.raw.map (A.substitution.substitute σ source),
      h.raw.map (A.substitution.substitute σ target)⟩ : Judgment B) =
    ⟨Δ, sort,
      B.substitution.substitute (fun t v => h.raw.map (σ t v)) (h.raw.map source),
      B.substitution.substitute (fun t v => h.raw.map (σ t v)) (h.raw.map target)⟩
  rw [h.map_substitute, h.map_substitute]

theorem SubstitutionModel.act_heq (Y : SubstitutionModel R B)
    {j₁ j₂ : Judgment B} (sameJudgment : j₁ = j₂)
    {value₁ : Y.evidence.carrier () j₁} {value₂ : Y.evidence.carrier () j₂}
    (sameValue : HEq value₁ value₂) {Δ : Ctx S}
    {σ₁ : Environment S B.substitution.Carrier j₁.1 Δ}
    {σ₂ : Environment S B.substitution.Carrier j₂.1 Δ} (sameEnv : HEq σ₁ σ₂)
    {target₁ target₂ : Judgment B} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j₁ σ₁ = target₁) (h₂ : substJudgment j₂ σ₂ = target₂) :
    HEq (Y.act j₁ value₁ σ₁ target₁ h₁) (Y.act j₂ value₂ σ₂ target₂ h₂) := by
  subst sameJudgment
  cases sameValue
  cases sameEnv
  subst sameTarget
  rfl

theorem rulesAct_congr_instance
    (Y : OperationalRuleModels.Model (rules R B)) {target : Judgment B}
    {first second : Instance R B} (same : first = second)
    (firstConclusion : conclusionJudgment R B first = target)
    (secondConclusion : conclusionJudgment R B second = target)
    (firstChildren : ∀ position : Fin (R.get first.index).premises.length,
      Y.carrier () (childJudgment R B first position))
    (secondChildren : ∀ position : Fin (R.get second.index).premises.length,
      Y.carrier () (childJudgment R B second position))
    (children : ∀ firstPosition secondPosition,
      HEq firstPosition secondPosition →
        HEq (firstChildren firstPosition) (secondChildren secondPosition)) :
    Y.rules.act () target ⟨⟨first, firstConclusion⟩, firstChildren⟩ =
      Y.rules.act () target ⟨⟨second, secondConclusion⟩, secondChildren⟩ := by
  subst same
  have childrenEq : firstChildren = secondChildren :=
    funext fun position => eq_of_heq (children position position HEq.rfl)
  subst childrenEq
  rfl

/-- A value transported along an equality of judgments is heterogeneously
equal to the original value. -/
theorem heq_transport {F : Judgment B → Type*} {j₁ j₂ : Judgment B}
    (same : j₁ = j₂) (value : F j₁) : HEq (same ▸ value : F j₂) value := by
  subst same
  rfl

open Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback (relativeFold) in
/-- Interpreting a firing tree in another base preserves the substitution
action: the substituted tree is interpreted as the substituted
interpretation, with the substitution mapped along the base map. -/
theorem relativeFold_substTree (h : FreeBindingClone.Hom A B)
    (Y : SubstitutionModel R B) (j : Judgment A) (tree : Tree R A j) :
    ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (hs : substJudgment j σ = target),
      relativeFold (presentationMap R h).rules Y.evidence.rules () target
          (substTree R A j tree σ target hs) =
        Y.act (mapJudgment h j)
          (relativeFold (presentationMap R h).rules Y.evidence.rules () j tree)
          (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
          ((mapJudgment_substJudgment h j σ).symm.trans
            (congrArg (mapJudgment h) hs)) := by
  refine IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j tree => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (hs : substJudgment j σ = target),
      relativeFold (presentationMap R h).rules Y.evidence.rules () target
          (substTree R A j tree σ target hs) =
        Y.act (mapJudgment h j)
          (relativeFold (presentationMap R h).rules Y.evidence.rules () j tree)
          (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
          ((mapJudgment_substJudgment h j σ).symm.trans
            (congrArg (mapJudgment h) hs)))
    ?_ () j tree
  intro base j shape children ih
  cases base
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  intro Δ σ target hs
  have envEq : ∀ (pf : conclusionJudgment R B (mapInstance R h occurrence) =
      mapJudgment h (conclusionJudgment R A occurrence)),
      castEnv pf (fun t v => h.raw.map (σ t v)) =
        (fun t v => h.raw.map (σ t v)) :=
    fun pf => eq_of_heq (castEnv_heq pf _)
  have instanceEq : ∀ (pf : conclusionJudgment R B (mapInstance R h occurrence) =
      mapJudgment h (conclusionJudgment R A occurrence)),
      mapInstance R h (Instance.subst R occurrence σ) =
        Instance.subst R (mapInstance R h occurrence)
          (castEnv pf (fun t v => h.raw.map (σ t v))) := by
    intro pf
    rw [envEq pf]
    exact mapInstance_subst R h occurrence σ
  refine Eq.trans ?_ (Y.act_rules
    (mapShape R h ⟨occurrence, rfl⟩)
    (fun position => (mapInstance_child R h occurrence position).symm ▸
      relativeFold (presentationMap R h).rules Y.evidence.rules () _
        (children position))
    (fun t v => h.raw.map (σ t v)) (mapJudgment h target) _).symm
  refine rulesAct_congr_instance R Y.evidence (instanceEq _) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  refine HEq.trans (heq_transport _ _) ?_
  refine HEq.trans (heq_of_eq (ih position _ _ _)) ?_
  refine SubstitutionModel.act_heq R Y
    (mapInstance_child R h occurrence position).symm
    (heq_transport _ _).symm ?_ ?_ _ _
  · exact heq_of_eq ((liftEnvironment_map h σ _).trans
      (congrArg (fun env => B.substitution.liftEnvironment env
        ((R.get occurrence.index).premises.get position).binders)
        (envEq _).symm))
  · exact (mapInstance_child R h (Instance.subst R occurrence σ) position).symm.trans
      (childJudgment_congr R (instanceEq _) position position HEq.rfl)

end BaseChange

/-! ## Substitution operational models over binding-equation models -/

section Presented

open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (mapJudgment)
open Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback (pullback relativeFold)

variable (E : List (EqAxiom S M))

/-- A model of the authored equations together with a substitution model of
the intrinsic conditional rules over it. -/
structure SubstitutionOperationalModel where
  base : FreeBindingEquationModel.Model.{0} E
  model : SubstitutionModel R base.algebra

namespace SubstitutionOperationalModel

variable {R E}

/-- A map interprets the base model, every rule constructor with each of
its premises, and the contextual substitution action. -/
structure Hom (X Y : SubstitutionOperationalModel R E) where
  base : FreeBindingClone.Hom X.base.algebra Y.base.algebra
  evidence : IndexedPolynomial.Algebra.Hom X.model.evidence.rules
    (pullback (presentationMap R base).rules Y.model.evidence.rules)
  preserves : ∀ (j : Judgment X.base.algebra)
    (value : X.model.evidence.carrier () j) {Δ : Ctx S}
    (σ : Environment S X.base.algebra.substitution.Carrier j.1 Δ)
    (target : Judgment X.base.algebra) (hs : substJudgment j σ = target),
    evidence.toFun () target (X.model.act j value σ target hs) =
      Y.model.act (mapJudgment base j) (evidence.toFun () j value)
        (fun t v => base.raw.map (σ t v)) (mapJudgment base target)
        ((mapJudgment_substJudgment base j σ).symm.trans
          (congrArg (mapJudgment base) hs))

theorem Hom.ext {X Y : SubstitutionOperationalModel R E} {f g : Hom X Y}
    (sameBase : f.base = g.base)
    (sameEvidence : ∀ j value,
      HEq (f.evidence.toFun () j value) (g.evidence.toFun () j value)) :
    f = g := by
  obtain ⟨fBase, fEvidence, fPreserves⟩ := f
  obtain ⟨gBase, gEvidence, gPreserves⟩ := g
  change fBase = gBase at sameBase
  subst sameBase
  have evidenceEq : fEvidence = gEvidence :=
    IndexedPolynomial.Algebra.Hom.ext _ _ (fun base index value => by
      cases base
      exact eq_of_heq (sameEvidence index value))
  subst evidenceEq
  rfl

def Hom.id (X : SubstitutionOperationalModel R E) : Hom X X where
  base := FreeBindingClone.Hom.id X.base.algebra
  evidence :=
    { toFun := fun _ _ value => value
      commutes := by
        intro base index layer
        rfl }
  preserves := by
    intro j value Δ σ target hs
    rfl

set_option maxHeartbeats 1000000 in
def Hom.comp {X Y Z : SubstitutionOperationalModel R E}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := FreeBindingClone.Hom.comp f.base g.base
  evidence :=
    { toFun := fun _ j value =>
        g.evidence.toFun () (mapJudgment f.base j) (f.evidence.toFun () j value)
      commutes := by
        intro base index layer
        let composite : IndexedPolynomial.Algebra.Hom X.model.evidence.rules
            (pullback (presentationMap R f.base).rules
              (pullback (presentationMap R g.base).rules
                Z.model.evidence.rules)) :=
          IndexedPolynomial.Algebra.Hom.comp f.evidence
            (IndexedRuleAlgebraPullback.pullbackHom
              (presentationMap R f.base).rules g.evidence)
        have h := composite.commutes base index layer
        change composite.toFun base index
            (X.model.evidence.rules.act base index layer) =
          (pullback
            (IndexedRulePolynomialMorphisms.Hom.comp
              (presentationMap R f.base).rules
              (presentationMap R g.base).rules)
            Z.model.evidence.rules).act base index
            (IndexedPolynomial.Extension.map (rules R X.base.algebra)
              composite.toFun layer)
        have actEq := congrArg IndexedPolynomial.Algebra.act
          (IndexedRuleAlgebraPullback.pullback_comp
            (presentationMap R f.base).rules (presentationMap R g.base).rules
            Z.model.evidence.rules)
        exact h.trans (congrFun (congrFun (congrFun actEq base) index)
          (IndexedPolynomial.Extension.map (rules R X.base.algebra)
            composite.toFun layer)).symm }
  preserves := by
    intro j value Δ σ target hs
    exact (congrArg (g.evidence.toFun () (mapJudgment f.base target))
      (f.preserves j value σ target hs)).trans
      (g.preserves (mapJudgment f.base j) (f.evidence.toFun () j value)
        (fun t v => f.base.raw.map (σ t v)) (mapJudgment f.base target) _)

instance category : Category (SubstitutionOperationalModel R E) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro X Y f
    exact Hom.ext (FreeBindingClone.Hom.ext
      (FreeBindingTerms.Hom.ext (fun _ => rfl))) (fun _ _ => HEq.rfl)
  comp_id := by
    intro X Y f
    exact Hom.ext (FreeBindingClone.Hom.ext
      (FreeBindingTerms.Hom.ext (fun _ => rfl))) (fun _ _ => HEq.rfl)
  assoc := by
    intro W X Y Z f g h
    exact Hom.ext (FreeBindingClone.Hom.ext
      (FreeBindingTerms.Hom.ext (fun _ => rfl))) (fun _ _ => HEq.rfl)

variable (R)

/-- Free firing trees with their substitution action over a base model. -/
noncomputable def free (X : FreeBindingEquationModel.Model.{0} E) :
    SubstitutionOperationalModel R E :=
  ⟨X, SubstitutionModel.free R X.algebra⟩

/-- The interpretation of free firing trees along a base map preserves the
substitution action. -/
noncomputable def lift (X : FreeBindingEquationModel.Model.{0} E)
    (Y : SubstitutionOperationalModel R E)
    (baseMap : FreeBindingClone.Hom X.algebra Y.base.algebra) :
    Hom (free R X) Y where
  base := baseMap
  evidence := IndexedPolynomial.Algebra.foldHom
    (pullback (presentationMap R baseMap).rules Y.model.evidence.rules)
  preserves := fun j value _ σ target hs =>
    relativeFold_substTree R baseMap Y.model j value σ target hs

/-- A map out of free firing trees is determined by its base map. -/
theorem lift_unique {X : FreeBindingEquationModel.Model.{0} E}
    {Y : SubstitutionOperationalModel R E} (f : Hom (free R X) Y) :
    f = lift R X Y f.base :=
  Hom.ext rfl (fun j tree => heq_of_eq
    (IndexedPolynomial.Algebra.hom_eq_fold _ f.evidence () j tree))

/-- Maps out of the free substitution operational model correspond exactly
to base maps. -/
noncomputable def freeHomEquiv (X : FreeBindingEquationModel.Model.{0} E)
    (Y : SubstitutionOperationalModel R E) :
    Hom (free R X) Y ≃ FreeBindingClone.Hom X.algebra Y.base.algebra where
  toFun f := f.base
  invFun := lift R X Y
  left_inv f := (lift_unique R f).symm
  right_inv _ := rfl

variable (E) in
/-- The free substitution operational model over the equation quotient. -/
noncomputable def presented : SubstitutionOperationalModel R E :=
  free R (FreeBindingEquationModel.presented E)

variable (E) in
/-- The equation quotient with its free firing trees and their substitution
action is initial among substitution operational models: one interpretation
of the authored operations, equations, binders, rule actions and
substitution extends uniquely. -/
noncomputable def presentedIsInitial : IsInitial (presented R E) :=
  IsInitial.ofUniqueHom
    (fun Y => lift R _ Y ((FreeBindingEquationModel.presentedIsInitial E).to Y.base))
    (fun Y f => (lift_unique R f).trans (congrArg (lift R _ Y)
      ((FreeBindingEquationModel.presentedIsInitial E).hom_ext _ _)))

end SubstitutionOperationalModel

end Presented

/-! ## The one-step relation is the image of the event endpoints -/

section Reduction

variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- Reduction at a judgment: some firing tree has exactly these endpoints.
The event trees themselves are retained separately; this is their image. -/
def Reduces (j : Judgment A) : Prop :=
  Nonempty (Tree R A j)

/-- A relation on judgments is closed under the rules when every rule
occurrence whose premise children hold yields its conclusion. -/
def RuleClosed (relation : Judgment A → Prop) : Prop :=
  ∀ (occurrence : Instance R A),
    (∀ position : Fin (R.get occurrence.index).premises.length,
      relation (childJudgment R A occurrence position)) →
      relation (conclusionJudgment R A occurrence)

theorem reduces_ruleClosed : RuleClosed R (Reduces R (A := A)) := by
  intro occurrence premises
  exact ⟨IndexedPolynomial.Fix.roll
    (⟨occurrence, rfl⟩ : Shape R A (conclusionJudgment R A occurrence))
    (fun position => Classical.choice (premises position))⟩

/-- Reduction is the least rule-closed relation. -/
theorem reduces_least (relation : Judgment A → Prop)
    (closed : RuleClosed R relation) (j : Judgment A) :
    Reduces R j → relation j := by
  rintro ⟨tree⟩
  refine IndexedPolynomial.Fix.eliminate (rules R A)
    (fun _ j _ => relation j) ?_ () j tree
  intro base j shape children premises
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  exact closed occurrence premises

/-- Reduction is stable under every contextual substitution. -/
theorem reduces_substitute {j : Judgment A} (reduces : Reduces R j)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ) :
    Reduces R (substJudgment j σ) := by
  obtain ⟨tree⟩ := reduces
  exact ⟨substTree R A j tree σ _ rfl⟩

open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (mapJudgment) in
/-- Reduction is transported along every binding-clone morphism, in
particular onto an equation quotient. -/
theorem reduces_map {B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) {j : Judgment A} (reduces : Reduces R j) :
    Reduces R (mapJudgment h j) :=
  reduces_least R (fun j => Reduces R (mapJudgment h j))
    (fun occurrence premises =>
      (congrArg (Reduces R) (mapInstance_conclusion R h occurrence)).mp
        (reduces_ruleClosed R (mapInstance R h occurrence)
          (fun position =>
            (congrArg (Reduces R) (mapInstance_child R h occurrence position)).mpr
              (premises position))))
    j reduces

/-- An authored presentation with no operational rules has no firing trees,
even after closing under contextual substitution. -/
theorem no_rules_no_reduction (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) :
    ¬ Reduces ([] : List (Rule S M)) j := by
  intro firing
  have closed : RuleClosed ([] : List (Rule S M)) (A := A) (fun _ => False) := by
    intro occurrence _
    exact occurrence.index.elim0
  exact (reduces_least ([] : List (Rule S M)) (A := A)
    (fun _ => False) closed j) firing

end Reduction

#print axioms SubstitutionModel.free
#print axioms SubstitutionModel.fold_substTree
#print axioms SubstitutionModel.freeIsInitial
#print axioms relativeFold_substTree
#print axioms SubstitutionOperationalModel.freeHomEquiv
#print axioms SubstitutionOperationalModel.presentedIsInitial
#print axioms reduces_ruleClosed
#print axioms reduces_least
#print axioms reduces_substitute
#print axioms reduces_map

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
