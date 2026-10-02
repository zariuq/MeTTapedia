import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalSubstitution

/-!
# Shared telescopes as an unpruned rule-local presentation

Every authored shared rule is paired with its complete original telescope.
The adapter retains the declaration address, ambient scope, every assignment
value, ordinary environment and ordered binder-local premise. It performs no
unused-metavariable pruning.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalPolynomialComparison

open Mettapedia.TypeTheory
open BindingSubstitutionAlgebra
open AuthoredPositionedRulePolynomial (Judgment)

universe u v
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))

/-- The existing declarations with their full original telescope retained. -/
def localRules : List (IntrinsicScopedLocalPolynomial.LocalRule S) := R.map (fun rule => ⟨M, rule⟩)

def localIndex (i : Fin R.length) : Fin (localRules R).length :=
  ⟨i.val, by simp [localRules]⟩

def sharedIndex (i : Fin (localRules R).length) : Fin R.length :=
  ⟨i.val, by simpa only [localRules, List.length_map] using i.isLt⟩

@[simp] theorem sharedIndex_localIndex (i : Fin R.length) :
    sharedIndex R (localIndex R i) = i := by apply Fin.ext; rfl

@[simp] theorem localIndex_sharedIndex (i : Fin (localRules R).length) :
    localIndex R (sharedIndex R i) = i := by apply Fin.ext; rfl

@[simp] theorem get_localIndex (i : Fin R.length) :
    (localRules R).get (localIndex R i) = ⟨M, R.get i⟩ := by
  simp [localRules, localIndex]

@[simp] theorem get_sharedIndex (i : Fin (localRules R).length) :
    (localRules R).get i = ⟨M, R.get (sharedIndex R i)⟩ := by
  have compared := get_localIndex R (sharedIndex R i)
  rw [localIndex_sharedIndex] at compared
  exact compared

/-- Convert an actual shared occurrence, retaining every assignment value. -/
def toLocalInstance {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) : IntrinsicScopedLocalPolynomial.Instance (localRules R) A where
  index := localIndex R occurrence.index
  ambient := occurrence.ambient
  valuation := cast (congrArg (fun declaration : IntrinsicScopedLocalPolynomial.LocalRule S =>
    SemanticContextualMetavariables.Valuation (M := declaration.1) A occurrence.ambient)
    (get_localIndex R occurrence.index).symm) occurrence.valuation
  close := cast (congrArg (fun declaration : IntrinsicScopedLocalPolynomial.LocalRule S =>
    Environment S A.substitution.Carrier declaration.2.conclusion.ctx occurrence.ambient)
    (get_localIndex R occurrence.index).symm) occurrence.close

/-- Recover all original shared data from the unpruned local occurrence. -/
def toSharedInstance {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedLocalPolynomial.Instance (localRules R) A) : IntrinsicScopedConditionalPolynomial.Instance R A where
  index := sharedIndex R occurrence.index
  ambient := occurrence.ambient
  valuation := cast (congrArg (fun declaration : IntrinsicScopedLocalPolynomial.LocalRule S =>
    SemanticContextualMetavariables.Valuation (M := declaration.1) A occurrence.ambient)
    (get_sharedIndex R occurrence.index)) occurrence.valuation
  close := cast (congrArg (fun declaration : IntrinsicScopedLocalPolynomial.LocalRule S =>
    Environment S A.substitution.Carrier declaration.2.conclusion.ctx occurrence.ambient)
    (get_sharedIndex R occurrence.index)) occurrence.close

@[simp] theorem toShared_toLocal {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) :
    toSharedInstance R (toLocalInstance R occurrence) = occurrence := by
  cases occurrence
  simp only [toSharedInstance, toLocalInstance]
  congr 1 <;> apply eq_of_heq <;> exact (cast_heq _ _).trans (cast_heq _ _)

@[simp] theorem toLocal_toShared {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedLocalPolynomial.Instance (localRules R) A) :
    toLocalInstance R (toSharedInstance R occurrence) = occurrence := by
  cases occurrence
  simp only [toSharedInstance, toLocalInstance]
  congr 1 <;> apply eq_of_heq <;> exact (cast_heq _ _).trans (cast_heq _ _)

/-- The actual occurrence equivalence is valid because the telescope is unpruned. -/
def instanceEquiv (A : BindingCloneAlgebra.Algebra.{u} S) :
    IntrinsicScopedConditionalPolynomial.Instance R A ≃ IntrinsicScopedLocalPolynomial.Instance (localRules R) A where
  toFun := toLocalInstance R
  invFun := toSharedInstance R
  left_inv := toShared_toLocal R
  right_inv := toLocal_toShared R

private theorem conclusion_transport (A : BindingCloneAlgebra.Algebra.{u} S)
    {declaration declaration' : IntrinsicScopedLocalPolynomial.LocalRule S}
    (same : declaration = declaration') (ambient : Ctx S)
    (valuation : SemanticContextualMetavariables.Valuation (M := declaration.1) A ambient)
    (close : Environment S A.substitution.Carrier declaration.2.conclusion.ctx ambient) :
    IntrinsicScopedConditionalPolynomial.conclusionJudgment [declaration'.2] A
      ⟨0, ambient,
        cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
          SemanticContextualMetavariables.Valuation (M := d.1) A ambient) same) valuation,
        cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
          Environment S A.substitution.Carrier d.2.conclusion.ctx ambient) same) close⟩ =
    IntrinsicScopedConditionalPolynomial.conclusionJudgment [declaration.2] A
      ⟨0, ambient, valuation, close⟩ := by
  cases same
  rfl

/-- Both interpretations use the same schema, values and ordinary environment. -/
theorem toLocal_conclusion {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment (localRules R) A (toLocalInstance R occurrence) =
      IntrinsicScopedConditionalPolynomial.conclusionJudgment R A occurrence :=
  conclusion_transport A (get_localIndex R occurrence.index).symm
    occurrence.ambient occurrence.valuation occurrence.close

/-- The original shared conclusion is recovered from every unpruned local occurrence. -/
theorem toShared_conclusion {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedLocalPolynomial.Instance (localRules R) A) :
    IntrinsicScopedConditionalPolynomial.conclusionJudgment R A (toSharedInstance R occurrence) =
      IntrinsicScopedLocalPolynomial.conclusionJudgment (localRules R) A occurrence := by
  have compared := toLocal_conclusion R (toSharedInstance R occurrence)
  rw [toLocal_toShared] at compared
  exact compared.symm

/-- The premise address is unchanged; only its length proof is transported. -/
def toLocalPosition {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A)
    (position : Fin (R.get occurrence.index).premises.length) :
    Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length :=
  Fin.cast (congrArg (fun declaration : IntrinsicScopedLocalPolynomial.LocalRule S =>
    declaration.2.premises.length) (get_localIndex R occurrence.index).symm) position

def toSharedPosition {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A)
    (position : Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length) :
    Fin (R.get occurrence.index).premises.length :=
  Fin.cast (congrArg (fun declaration : IntrinsicScopedLocalPolynomial.LocalRule S =>
    declaration.2.premises.length) (get_localIndex R occurrence.index)) position

@[simp] theorem toLocalPosition_val {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A)
    (position : Fin (R.get occurrence.index).premises.length) :
    (toLocalPosition R occurrence position).val = position.val := rfl

@[simp] theorem toSharedPosition_val {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A)
    (position : Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length) :
    (toSharedPosition R occurrence position).val = position.val := rfl

/-- The cartesian premise map preserves each ordered address, including duplicates. -/
def positionEquiv {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) :
    Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length ≃
      Fin (R.get occurrence.index).premises.length where
  toFun := toSharedPosition R occurrence
  invFun := toLocalPosition R occurrence
  left_inv := fun _ => Fin.ext rfl
  right_inv := fun _ => Fin.ext rfl

private theorem child_transport (A : BindingCloneAlgebra.Algebra.{u} S)
    {declaration declaration' : IntrinsicScopedLocalPolynomial.LocalRule S}
    (same : declaration = declaration') (ambient : Ctx S)
    (valuation : SemanticContextualMetavariables.Valuation (M := declaration.1) A ambient)
    (close : Environment S A.substitution.Carrier declaration.2.conclusion.ctx ambient)
    (position : Fin declaration.2.premises.length) :
    IntrinsicScopedConditionalPolynomial.childJudgment [declaration'.2] A
      ⟨0, ambient,
        cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
          SemanticContextualMetavariables.Valuation (M := d.1) A ambient) same) valuation,
        cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
          Environment S A.substitution.Carrier d.2.conclusion.ctx ambient) same) close⟩
      (Fin.cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
        d.2.premises.length) same) position) =
    IntrinsicScopedConditionalPolynomial.childJudgment [declaration.2] A
      ⟨0, ambient, valuation, close⟩ position := by
  cases same
  rfl

/-- The complete interpreted premise, including its binder context, is preserved. -/
theorem toLocal_child {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A)
    (position : Fin (R.get occurrence.index).premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment (localRules R) A (toLocalInstance R occurrence)
      (toLocalPosition R occurrence position) =
      IntrinsicScopedConditionalPolynomial.childJudgment R A occurrence position :=
  child_transport A (get_localIndex R occurrence.index).symm
    occurrence.ambient occurrence.valuation occurrence.close position

/-- A selected local premise recovers the same shared binder-local judgment. -/
theorem toLocal_child_positionEquiv {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A)
    (position : Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment (localRules R) A (toLocalInstance R occurrence)
      position = IntrinsicScopedConditionalPolynomial.childJudgment R A occurrence
        ((positionEquiv R occurrence) position) := by
  have compared := toLocal_child R occurrence ((positionEquiv R occurrence) position)
  have same : toLocalPosition R occurrence ((positionEquiv R occurrence) position) = position :=
    (positionEquiv R occurrence).left_inv position
  rw [same] at compared
  exact compared

/-- The adapter sends every actual constructor at its existing judgment index. -/
def toLocalShape {A : BindingCloneAlgebra.Algebra.{u} S} {j : Judgment A}
    (shape : IntrinsicScopedConditionalPolynomial.Shape R A j) :
    IntrinsicScopedLocalPolynomial.Shape (localRules R) A j :=
  ⟨toLocalInstance R shape.1, (toLocal_conclusion R shape.1).trans shape.2⟩

def toSharedShape {A : BindingCloneAlgebra.Algebra.{u} S} {j : Judgment A}
    (shape : IntrinsicScopedLocalPolynomial.Shape (localRules R) A j) :
    IntrinsicScopedConditionalPolynomial.Shape R A j :=
  ⟨toSharedInstance R shape.1, (toShared_conclusion R shape.1).trans shape.2⟩

@[simp] theorem toSharedShape_toLocalShape {A : BindingCloneAlgebra.Algebra.{u} S} {j : Judgment A}
    (shape : IntrinsicScopedConditionalPolynomial.Shape R A j) :
    toSharedShape R (toLocalShape R shape) = shape := by
  apply Subtype.ext
  exact toShared_toLocal R shape.1

@[simp] theorem toLocalShape_toSharedShape {A : BindingCloneAlgebra.Algebra.{u} S} {j : Judgment A}
    (shape : IntrinsicScopedLocalPolynomial.Shape (localRules R) A j) :
    toLocalShape R (toSharedShape R shape) = shape := by
  apply Subtype.ext
  exact toLocal_toShared R shape.1

/-- The genuine cartesian rule map retains all ordered recursive premises. -/
def toLocalPolynomial (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedRulePolynomialMorphisms.Hom (IntrinsicScopedConditionalPolynomial.rules R A)
      (IntrinsicScopedLocalPolynomial.rules (localRules R) A) (fun _ j => j) where
  onShape := fun _ _ => toLocalShape R
  onPosition := fun _ _ shape => positionEquiv R shape.1
  onNext := fun _ _ shape position => toLocal_child_positionEquiv R shape.1 position

/-- The inverse also retains the authored premise address. -/
def inversePositionEquiv {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedLocalPolynomial.Instance (localRules R) A) :
    Fin (R.get (toSharedInstance R occurrence).index).premises.length ≃
      Fin ((localRules R).get occurrence.index).2.premises.length where
  toFun := Fin.cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
    d.2.premises.length) (get_sharedIndex R occurrence.index).symm)
  invFun := Fin.cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
    d.2.premises.length) (get_sharedIndex R occurrence.index))
  left_inv := fun _ => Fin.ext rfl
  right_inv := fun _ => Fin.ext rfl

/-- Inverse interpretation preserves the whole premise under its own binders. -/
theorem toShared_child {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedLocalPolynomial.Instance (localRules R) A)
    (position : Fin (R.get (toSharedInstance R occurrence).index).premises.length) :
    IntrinsicScopedConditionalPolynomial.childJudgment R A (toSharedInstance R occurrence) position =
    IntrinsicScopedLocalPolynomial.childJudgment (localRules R) A occurrence
      ((inversePositionEquiv R occurrence) position) := by
  have compared := child_transport A (get_sharedIndex R occurrence.index)
    occurrence.ambient occurrence.valuation occurrence.close
      ((inversePositionEquiv R occurrence) position)
  convert compared using 1 <;> rfl

/-- The reverse cartesian map recovers all constructors and recursive addresses. -/
def toSharedPolynomial (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedRulePolynomialMorphisms.Hom (IntrinsicScopedLocalPolynomial.rules (localRules R) A)
      (IntrinsicScopedConditionalPolynomial.rules R A) (fun _ j => j) where
  onShape := fun _ _ => toSharedShape R
  onPosition := fun _ _ shape => inversePositionEquiv R shape.1
  onNext := fun _ _ shape position => toShared_child R shape.1 position

private theorem finEquiv_heq {n n' m : Nat} (same : n = n')
    (first : Fin n ≃ Fin m) (second : Fin n' ≃ Fin m)
    (addresses : ∀ (a : Fin n), (first a).val = (second (Fin.cast same a)).val) :
    HEq first second := by
  cases same
  apply heq_of_eq
  apply Equiv.ext
  intro a
  exact Fin.ext (addresses a)

private theorem polynomial_ext
    {Base : Type*} {I J : Base → Type*}
    {P : IndexedPolynomial Base I} {Q : IndexedPolynomial Base J}
    {f : ∀ b, I b → J b}
    (first second : IndexedRulePolynomialMorphisms.Hom P Q f)
    (shapes : first.onShape = second.onShape)
    (positions : ∀ b j shape, HEq (first.onPosition b j shape) (second.onPosition b j shape)) :
    first = second := by
  cases first with
  | mk firstShape firstPosition firstNext =>
    cases second with
    | mk secondShape secondPosition secondNext =>
      cases shapes
      have same : firstPosition = secondPosition := by
        funext b j shape
        exact eq_of_heq (positions b j shape)
      cases same
      rfl

/-- Shared constructors and every premise address are recovered by the round trip. -/
theorem toLocalPolynomial_toSharedPolynomial (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedRulePolynomialMorphisms.Hom.comp (toLocalPolynomial R A) (toSharedPolynomial R A) =
      IndexedRulePolynomialMorphisms.Hom.id (IntrinsicScopedConditionalPolynomial.rules R A) := by
  apply polynomial_ext
  · funext b j shape
    exact toSharedShape_toLocalShape R shape
  · intro b j shape
    apply finEquiv_heq
      (congrArg (fun s : IntrinsicScopedConditionalPolynomial.Shape R A j =>
        (R.get s.1.index).premises.length) (toSharedShape_toLocalShape R shape))
    intro address
    rfl

/-- The local round trip retains every constructor and ordered address. -/
theorem toSharedPolynomial_toLocalPolynomial (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedRulePolynomialMorphisms.Hom.comp (toSharedPolynomial R A) (toLocalPolynomial R A) =
      IndexedRulePolynomialMorphisms.Hom.id (IntrinsicScopedLocalPolynomial.rules (localRules R) A) := by
  apply polynomial_ext
  · funext b j shape
    exact toLocalShape_toSharedShape R shape
  · intro b j shape
    apply finEquiv_heq
      (congrArg (fun s : IntrinsicScopedLocalPolynomial.Shape (localRules R) A j =>
        ((localRules R).get s.1.index).2.premises.length) (toLocalShape_toSharedShape R shape))
    intro address
    rfl

private theorem valuation_subst_transport (A : BindingCloneAlgebra.Algebra.{u} S)
    {declaration declaration' : IntrinsicScopedLocalPolynomial.LocalRule S}
    (same : declaration = declaration') {Γ Δ : Ctx S}
    (valuation : SemanticContextualMetavariables.Valuation (M := declaration.1) A Γ)
    (σ : Environment S A.substitution.Carrier Γ Δ) :
    cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
      SemanticContextualMetavariables.Valuation (M := d.1) A Δ) same)
        (IntrinsicScopedConditionalSubstitution.substValuation A σ valuation) =
    IntrinsicScopedConditionalSubstitution.substValuation A σ
      (cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
        SemanticContextualMetavariables.Valuation (M := d.1) A Γ) same) valuation) := by
  cases same
  rfl

private theorem close_subst_transport (A : BindingCloneAlgebra.Algebra.{u} S)
    {declaration declaration' : IntrinsicScopedLocalPolynomial.LocalRule S}
    (same : declaration = declaration') {Γ Δ : Ctx S}
    (close : Environment S A.substitution.Carrier declaration.2.conclusion.ctx Γ)
    (σ : Environment S A.substitution.Carrier Γ Δ) :
    cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
      Environment S A.substitution.Carrier d.2.conclusion.ctx Δ) same)
        (fun t var => A.substitution.substitute σ (close t var)) =
    (fun t var => A.substitution.substitute σ
      ((cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
        Environment S A.substitution.Carrier d.2.conclusion.ctx Γ) same) close) t var)) := by
  cases same
  rfl

/-- Ambient substitution uses exactly the same contextual values and ordinary environment. -/
theorem toLocal_subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    toLocalInstance R (IntrinsicScopedConditionalSubstitution.Instance.subst R occurrence σ) =
      IntrinsicScopedLocalPolynomial.Instance.subst (localRules R) (toLocalInstance R occurrence) σ := by
  cases occurrence with
  | mk index ambient valuation close =>
    dsimp only [toLocalInstance, IntrinsicScopedConditionalSubstitution.Instance.subst,
      IntrinsicScopedLocalPolynomial.Instance.subst]
    congr 1
    · exact valuation_subst_transport A (get_localIndex R index).symm valuation σ
    · exact close_subst_transport A (get_localIndex R index).symm close σ

private theorem valuation_map_transport {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} (h : FreeBindingClone.Hom A B)
    {declaration declaration' : IntrinsicScopedLocalPolynomial.LocalRule S}
    (same : declaration = declaration') {Γ : Ctx S}
    (valuation : SemanticContextualMetavariables.Valuation (M := declaration.1) A Γ) :
    cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
      SemanticContextualMetavariables.Valuation (M := d.1) B Γ) same)
        (SemanticContextualMetavariables.mapValuation h valuation) =
    SemanticContextualMetavariables.mapValuation h
      (cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
        SemanticContextualMetavariables.Valuation (M := d.1) A Γ) same) valuation) := by
  cases same
  rfl

private theorem close_map_transport {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} (h : FreeBindingClone.Hom A B)
    {declaration declaration' : IntrinsicScopedLocalPolynomial.LocalRule S}
    (same : declaration = declaration') {Γ : Ctx S}
    (close : Environment S A.substitution.Carrier declaration.2.conclusion.ctx Γ) :
    cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
      Environment S B.substitution.Carrier d.2.conclusion.ctx Γ) same)
        (fun t var => h.raw.map (close t var)) =
    (fun t var => h.raw.map
      ((cast (congrArg (fun d : IntrinsicScopedLocalPolynomial.LocalRule S =>
        Environment S A.substitution.Carrier d.2.conclusion.ctx Γ) same) close) t var)) := by
  cases same
  rfl

/-- Clone interpretation commutes with the unpruned occurrence adapter. -/
theorem toLocal_mapInstance {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} (h : FreeBindingClone.Hom A B)
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) :
    toLocalInstance R (IntrinsicScopedConditionalPolynomial.mapInstance R h occurrence) =
      IntrinsicScopedLocalPolynomial.mapInstance (localRules R) h (toLocalInstance R occurrence) := by
  cases occurrence with
  | mk index ambient valuation close =>
    dsimp only [toLocalInstance, IntrinsicScopedConditionalPolynomial.mapInstance,
      IntrinsicScopedLocalPolynomial.mapInstance]
    congr 1
    · exact valuation_map_transport h (get_localIndex R index).symm valuation
    · exact close_map_transport h (get_localIndex R index).symm close

private theorem binders_transport
    {declaration declaration' : IntrinsicScopedLocalPolynomial.LocalRule S}
    (same : declaration = declaration')
    (position : Fin declaration.2.premises.length) :
    (declaration'.2.premises.get (Fin.cast (congrArg
      (fun d : IntrinsicScopedLocalPolynomial.LocalRule S => d.2.premises.length) same) position)).binders =
      (declaration.2.premises.get position).binders := by
  cases same
  rfl

/-- Each authored premise retains its binder list as well as its list address. -/
theorem toLocal_binders {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A)
    (position : Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length) :
    (((localRules R).get (toLocalInstance R occurrence).index).2.premises.get position).binders =
      ((R.get occurrence.index).premises.get ((positionEquiv R occurrence) position)).binders := by
  have compared := binders_transport (get_localIndex R occurrence.index).symm
    ((positionEquiv R occurrence) position)
  convert compared using 1
  congr 2

/-- The cartesian comparison is natural under every genuine clone interpretation. -/
theorem toLocalPolynomial_map {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) :
    IndexedRulePolynomialMorphisms.Hom.comp
      (IntrinsicScopedConditionalPolynomial.presentationMap R h).rules (toLocalPolynomial R B) =
    IndexedRulePolynomialMorphisms.Hom.comp (toLocalPolynomial R A)
      (IntrinsicScopedLocalPolynomial.presentationMap (localRules R) h).rules := by
  apply polynomial_ext
  · funext b j shape
    apply Subtype.ext
    exact toLocal_mapInstance R h shape.1
  · intro b j shape
    apply heq_of_eq
    apply Equiv.ext
    intro address
    exact Fin.ext rfl

end Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalPolynomialComparison
