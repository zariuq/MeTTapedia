import Mettapedia.OSLF.Syntax.CategoricalBindingModel
import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison

/-!
# Binding programs in the clone presheaf category

The actual clone programs supply a categorical binding model. Ordered context
products represent simultaneous assignments, and the chosen function objects
are the presheaf exponentials representing contextual bodies.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafPrograms

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf
open MultiBinderPresheaf BindingFunctionArgumentComparison

universe u
variable {S : Signature}

/-- The target retains every clone substitution as a change of stage. -/
abbrev target (A : BindingCloneAlgebra.Algebra.{u} S) := Base A ⥤ Type u

/-- An ordered product of program sections is a simultaneous assignment. -/
def contextAtEquiv (A : BindingCloneAlgebra.Algebra.{u} S) :
    (Γ : Ctx S) → (X : Base A) →
      (CategoricalBindingModel.contextOf (programs A) Γ).obj X ≃
        (binders A Γ).obj X
  | [], _ => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | s :: Γ, X => {
      toFun := fun x => Fin.cons (x.1 (0 : Fin 1)) (contextAtEquiv A Γ X x.2)
      invFun := fun f =>
        ((programsAtEquiv A s X).symm (f (0 : Fin (Γ.length + 1))),
          (contextAtEquiv A Γ X).symm (fun i => f i.succ))
      left_inv := fun x => by
        apply Prod.ext
        · exact (programsAtEquiv A s X).symm_apply_apply x.1
        · exact (contextAtEquiv A Γ X).symm_apply_apply x.2
      right_inv := fun f => by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun ((contextAtEquiv A Γ X).apply_symm_apply
            (fun j => f j.succ)) j }

theorem contextAtEquiv_natural (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (Γ : Ctx S) {X Y : Base A} (f : X ⟶ Y)
      (x : (CategoricalBindingModel.contextOf (programs A) Γ).obj X),
      contextAtEquiv A Γ Y
          ((CategoricalBindingModel.contextOf (programs A) Γ).map f x) =
        (binders A Γ).map f (contextAtEquiv A Γ X x)
  | [], _, _, _, _ => by funext i; exact Fin.elim0 i
  | s :: Γ, X, Y, f, x => by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (contextAtEquiv_natural A Γ f x.2) j

/-- Ordered context products and whole-context representables coincide
naturally, with every coordinate retained. -/
def contextIso (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) :
    CategoricalBindingModel.contextOf (programs A) Γ ≅ binders A Γ :=
  NatIso.ofComponents (fun X => (contextAtEquiv A Γ X).toIso)
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro x
      exact contextAtEquiv_natural A Γ f x)

/-- Each typed variable projection reads its corresponding assignment. -/
theorem context_projection (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) (X : Base A)
      (x : (CategoricalBindingModel.contextOf (programs A) Γ).obj X),
      programsAtEquiv A s X
          ((CategoricalBindingModel.projectVar (programs A) v).app X x) =
        fromPositions Γ (contextAtEquiv A Γ X x) s v
  | _, _, .zero, _, _ => rfl
  | _, _, .succ v, X, x => context_projection A v X x.2

/-- The represented binder projection injects every prefix variable into
the combined binder and ambient context. -/
theorem fromPositions_fst (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ Δ : Ctx S) {s : S.Srt} (v : Var Γ s) :
    fromPositions Γ
        (fstProjection A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone Γ)
          (ContextObject.ofList A.substitution.toClone Δ)) s v =
      A.substitution.injectVar (injPrefix (Γ := Δ) Γ v) := by
  have coordinates :
      fstProjection A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone Γ)
          (ContextObject.ofList A.substitution.toClone Δ) =
        (fun i => A.substitution.injectVar (injPrefix (Γ := Δ) Γ (varOfIdx Γ i))) := by
    funext i
    exact leftProjection_as_var A Γ Δ i
  rw [coordinates]
  exact fromPositions_ofEnvironment
    (fun sort var => A.substitution.injectVar (injPrefix (Γ := Δ) Γ var)) v

/-- At the canonical extended context, categorical variable projections
read the original clone's prefix variables. -/
theorem context_projection_prefix (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) (X : Base A) :
    programsAtEquiv A s
        (Opposite.op (concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone Γ) X.unop))
        ((CategoricalBindingModel.projectVar (programs A) v).app
          (Opposite.op (concat A.substitution.toClone
            (ContextObject.ofList A.substitution.toClone Γ) X.unop))
          ((contextAtEquiv A Γ
            (Opposite.op (concat A.substitution.toClone
              (ContextObject.ofList A.substitution.toClone Γ) X.unop))).symm
              (fstProjection A.substitution.toClone _ _))) =
      A.substitution.injectVar (injPrefix (Γ := X.unop.context) Γ v) := by
  rw [context_projection]
  exact (congrArg (fun assignment => fromPositions Γ assignment s v)
    ((contextAtEquiv A Γ
      (Opposite.op (concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone Γ) X.unop))).apply_symm_apply
          (fstProjection A.substitution.toClone _ _))).trans
    (fromPositions_fst A Γ X.unop.context v)

/-- Joining positional assignments agrees with the original typed environment
join, preserving both ordered blocks. -/
theorem fromPositions_append (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (Γ Δ : Ctx S) {Θ : Ctx S}
      (left : (i : Fin Γ.length) → A.substitution.Carrier Θ (Γ.get i))
      (right : (i : Fin Δ.length) → A.substitution.Carrier Θ (Δ.get i)),
      fromPositions (Γ ++ Δ)
          (appendEnvironment A.substitution.toClone Γ Δ left right) =
        SemanticContextualMetavariables.joinEnvironment
          (fromPositions Γ left) (fromPositions Δ right)
  | [], _, _, _, _ => rfl
  | _ :: Γ, Δ, Θ, left, right => by
      funext s v
      cases v with
      | zero => rfl
      | succ v =>
          exact congrFun (congrFun
            (fromPositions_append A Γ Δ (fun i => left i.succ) right) s) v

/-- The evaluation assignment joins the supplied prefix with identity values
for every ambient variable. -/
theorem evaluation_environment (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (X : Base A) (a : (binders A Γ).obj X) :
    fromPositions (Γ ++ X.unop.context)
        (pair A.substitution.toClone a (𝟙 X.unop)) =
      SemanticContextualMetavariables.joinEnvironment
        (fromPositions Γ a) (fun _ v => A.substitution.injectVar v) := by
  have ambient :
      fromPositions X.unop.context (𝟙 X.unop) =
        (fun _ v => A.substitution.injectVar v) := by
    funext s v
    exact fromPositions_ofEnvironment
      (fun _ w => A.substitution.injectVar w) v
  exact (fromPositions_append A Γ X.unop.context a (𝟙 X.unop)).trans
    (congrArg (SemanticContextualMetavariables.joinEnvironment
      (fromPositions Γ a)) ambient)

/-- The chosen power is the actual exponential of the whole binder context. -/
abbrev power (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) (s : S.Srt) :
    target A := (binders A Γ).functorHom (programs A s)

/-- Chosen powers represent the original contextual body presheaves. -/
def powerBodiesIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (s : S.Srt) : power A Γ s ≅ scopedBodies A Γ s :=
  scopedBodiesIso A Γ s

/-- The product of the selected powers retains each authored argument. -/
def familyAtEquiv (A : BindingCloneAlgebra.Algebra.{u} S) :
    (arities : List (List S.Srt × S.Srt)) → (X : Base A) →
      (CategoricalBindingModel.familyOf (power A) arities).obj X ≃
        FunctionArgs A arities X.unop.context
  | [], _ => {
      toFun := fun _ => .nil
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  | (bs, s) :: arities, X => {
      toFun := fun x => .cons x.1 (familyAtEquiv A arities X x.2)
      invFun := fun x => match x with
        | .cons head tail => (head, (familyAtEquiv A arities X).symm tail)
      left_inv := fun x => by
        apply Prod.ext
        · rfl
        · exact (familyAtEquiv A arities X).symm_apply_apply x.2
      right_inv := fun x => by
        cases x with
        | cons head tail =>
            exact congrArg (FunctionArgs.cons head)
              ((familyAtEquiv A arities X).apply_symm_apply tail) }

private theorem environmentArrow_fromPositions
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {X Y : Base A} (f : X ⟶ Y) :
    MultiBinderPresheaf.environmentArrow A
        (fromPositions X.unop.context f.unop) = f.unop := by
  funext i
  exact fromPositions_varOfIdx X.unop.context f.unop i

theorem familyAtEquiv_natural (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (arities : List (List S.Srt × S.Srt)) {X Y : Base A} (f : X ⟶ Y)
      (x : (CategoricalBindingModel.familyOf (power A) arities).obj X),
      familyAtEquiv A arities Y
          ((CategoricalBindingModel.familyOf (power A) arities).map f x) =
        (functionArguments A arities).map f (familyAtEquiv A arities X x)
  | [], _, _, _, _ => rfl
  | (bs, s) :: arities, X, Y, f, x => by
      change FunctionArgs.cons ((power A bs s).map f x.1)
          (familyAtEquiv A arities Y
            ((CategoricalBindingModel.familyOf (power A) arities).map f x.2)) =
        FunctionArgs.cons
          ((power A bs s).map
            (Quiver.Hom.op (MultiBinderPresheaf.environmentArrow A
              (fromPositions X.unop.context f.unop))) x.1)
          (FunctionArgs.reindex A (fromPositions X.unop.context f.unop)
            (familyAtEquiv A arities X x.2))
      rw [environmentArrow_fromPositions]
      exact congrArg (FunctionArgs.cons ((power A bs s).map f x.1))
        (familyAtEquiv_natural A arities f x.2)

/-- The categorical family product is the original contextual argument tuple. -/
def familyIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (arities : List (List S.Srt × S.Srt)) :
    CategoricalBindingModel.familyOf (power A) arities ≅ functionArguments A arities :=
  NatIso.ofComponents (fun X => (familyAtEquiv A arities X).toIso)
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro x
      exact familyAtEquiv_natural A arities f x)

/-- Evaluation uses the represented context assignment at the same stage. -/
def eval (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) (s : S.Srt) :
    CategoricalBindingModel.contextOf (programs A) Γ ⊗ power A Γ s ⟶ programs A s :=
  (contextIso A Γ).hom ▷ power A Γ s ≫
    FunctorToTypes.functorHomEquiv (binders A Γ) (power A Γ s) (programs A s) (𝟙 _)

/-- Currying transports the context product to the whole-context representable. -/
def curry (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} {Z : target A}
    (f : CategoricalBindingModel.contextOf (programs A) Γ ⊗ Z ⟶ programs A s) :
    Z ⟶ power A Γ s :=
  (FunctorToTypes.functorHomEquiv (binders A Γ) Z (programs A s)).symm
    ((contextIso A Γ).inv ▷ Z ≫ f)

theorem curry_eval (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} {Z : target A}
    (f : CategoricalBindingModel.contextOf (programs A) Γ ⊗ Z ⟶ programs A s) :
    (CategoricalBindingModel.contextOf (programs A) Γ ◁ curry A f) ≫ eval A Γ s = f := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  rintro ⟨x, z⟩
  have beta := (FunctorToTypes.functorHomEquiv (binders A Γ) Z (programs A s)).apply_symm_apply
    ((contextIso A Γ).inv ▷ Z ≫ f)
  have point := congrArg
    (fun (k : binders A Γ ⊗ Z ⟶ programs A s) =>
      k.app X (((contextIso A Γ).hom.app X x, z) : (binders A Γ ⊗ Z).obj X)) beta
  change ((curry A f).app X z).app X (𝟙 X) ((contextIso A Γ).hom.app X x) = _
  change ((curry A f).app X z).app X (𝟙 X) ((contextIso A Γ).hom.app X x) =
    f.app X ((contextIso A Γ).inv.app X ((contextIso A Γ).hom.app X x), z) at point
  simpa only [contextIso, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Equiv.toIso_hom_hom_apply, Equiv.toIso_inv_hom_apply, Equiv.symm_apply_apply] using point

theorem curry_unique (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} {Z : target A}
    (f : CategoricalBindingModel.contextOf (programs A) Γ ⊗ Z ⟶ programs A s)
    (g : Z ⟶ power A Γ s)
    (h : (CategoricalBindingModel.contextOf (programs A) Γ ◁ g) ≫ eval A Γ s = f) :
    curry A f = g := by
  apply (FunctorToTypes.functorHomEquiv (binders A Γ) Z (programs A s)).injective
  change (FunctorToTypes.functorHomEquiv (binders A Γ) Z (programs A s))
      ((FunctorToTypes.functorHomEquiv (binders A Γ) Z (programs A s)).symm
        ((contextIso A Γ).inv ▷ Z ≫ f)) = _
  rw [Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  rintro ⟨a, z⟩
  have point := congrArg
    (fun (k : CategoricalBindingModel.contextOf (programs A) Γ ⊗ Z ⟶ programs A s) =>
      k.app X (((contextIso A Γ).inv.app X a, z) :
        (CategoricalBindingModel.contextOf (programs A) Γ ⊗ Z).obj X)) h
  change (g.app X z).app X (𝟙 X)
      ((contextIso A Γ).hom.app X ((contextIso A Γ).inv.app X a)) =
    f.app X ((contextIso A Γ).inv.app X a, z) at point
  change f.app X ((contextIso A Γ).inv.app X a, z) = (g.app X z).app X (𝟙 X) a
  simpa only [contextIso, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Equiv.toIso_hom_hom_apply, Equiv.toIso_inv_hom_apply, Equiv.apply_symm_apply] using point.symm

/-- Each authored operation acts on the genuine contextual function arguments. -/
def op (A : BindingCloneAlgebra.Algebra.{u} S) {s : S.Srt} (o : S.Op s) :
    CategoricalBindingModel.familyOf (power A) (S.arity o) ⟶ programs A s :=
  (familyIso A (S.arity o)).hom ≫ functionOperation A o ≫ (programsIso A s).inv

/-- The categorical binding model obtained from an arbitrary binding clone. -/
def model (A : BindingCloneAlgebra.Algebra.{u} S) :
    CategoricalBindingModel.Model S (target A) where
  sort := programs A
  power := power A
  eval := eval A
  curry := curry A
  curry_eval := curry_eval A
  curry_unique := curry_unique A
  op := op A

/-- Evaluation at a stage uses precisely that stage's whole assignment. -/
theorem eval_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (s : S.Srt) (X : Base A)
    (x : (CategoricalBindingModel.contextOf (programs A) Γ).obj X)
    (function : (power A Γ s).obj X) :
    (eval A Γ s).app X (x, function) =
      (function.app X (𝟙 X)) (contextAtEquiv A Γ X x) := rfl

/-- Evaluating a represented body substitutes its binder assignment while
the ambient stage variables remain the identity projections. -/
theorem function_eval_body (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (s : S.Srt) (X : Base A)
    (a : (binders A Γ).obj X) (function : (power A Γ s).obj X) :
    programsAtEquiv A s X ((function.app X (𝟙 X)) a) =
      A.substitution.toClone.substitute
        (scopedBodyEquiv A X.unop Γ s function)
        (pair A.substitution.toClone a (𝟙 X.unop)) := by
  let input := ContextObject.ofList A.substitution.toClone Γ
  let extended := concat A.substitution.toClone input X.unop
  change X.unop ⟶ input at a
  let assignment : X.unop ⟶ extended :=
    pair A.substitution.toClone a (𝟙 X.unop)
  have point := ConcreteCategory.congr_hom
    (function.naturality (Quiver.Hom.op assignment)
      (Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop)))
    (fstProjection A.substitution.toClone input X.unop)
  change (function.app X
      (Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop) ≫
        Quiver.Hom.op assignment))
      (assignment ≫ fstProjection A.substitution.toClone input X.unop) =
    assignment ≫
      ((function.app (Opposite.op extended)
        (Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop)))
        (fstProjection A.substitution.toClone input X.unop)) at point
  have sndLaw :
      Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop) ≫
        Quiver.Hom.op assignment = 𝟙 X := by
    simpa only [op_comp, op_id, assignment] using congrArg Quiver.Hom.op
      (categorical_pair_snd A.substitution.toClone a (𝟙 X.unop))
  have fstLaw : assignment ≫ fstProjection A.substitution.toClone input X.unop = a :=
    categorical_pair_fst A.substitution.toClone a (𝟙 X.unop)
  rw [sndLaw, fstLaw] at point
  have value := congrFun point (0 : Fin 1)
  rw [scopedBodyEquiv_apply]
  exact value

/-- The model evaluation is the original contextual substitution of its body. -/
theorem eval_body (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (s : S.Srt) (X : Base A)
    (x : (CategoricalBindingModel.contextOf (programs A) Γ).obj X)
    (function : (power A Γ s).obj X) :
    programsAtEquiv A s X ((eval A Γ s).app X (x, function)) =
      A.substitution.toClone.substitute
        ((powerBodiesIso A Γ s).hom.app X function)
        (pair A.substitution.toClone (contextAtEquiv A Γ X x) (𝟙 X.unop)) :=
  function_eval_body A Γ s X (contextAtEquiv A Γ X x) function

/-- Model evaluation agrees with the typed substitution algebra, including
the separate unchanged ambient block. -/
theorem eval_body_substitute (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (s : S.Srt) (X : Base A)
    (x : (CategoricalBindingModel.contextOf (programs A) Γ).obj X)
    (function : (power A Γ s).obj X) :
    programsAtEquiv A s X ((eval A Γ s).app X (x, function)) =
      A.substitution.substitute
        (SemanticContextualMetavariables.joinEnvironment
          (fromPositions Γ (contextAtEquiv A Γ X x))
          (fun _ v => A.substitution.injectVar v))
        ((powerBodiesIso A Γ s).hom.app X function) := by
  have equality := eval_body A Γ s X x function
  change programsAtEquiv A s X ((eval A Γ s).app X (x, function)) =
    A.substitution.substitute
      (fromPositions (Γ ++ X.unop.context)
        (pair A.substitution.toClone (contextAtEquiv A Γ X x) (𝟙 X.unop)))
      ((powerBodiesIso A Γ s).hom.app X function) at equality
  exact equality.trans (congrArg
    (fun env => A.substitution.substitute env
      ((powerBodiesIso A Γ s).hom.app X function))
    (evaluation_environment A Γ X (contextAtEquiv A Γ X x)))

/-- A curried function at any later stage evaluates the original operation
on the represented assignment and the reindexed stage parameter. -/
theorem curry_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} {Z : target A}
    (f : CategoricalBindingModel.contextOf (programs A) Γ ⊗ Z ⟶ programs A s)
    (X Y : Base A) (h : X ⟶ Y) (z : Z.obj X) (a : (binders A Γ).obj Y) :
    (((curry A f).app X z).app Y h) a =
      f.app Y ((contextAtEquiv A Γ Y).symm a, Z.map h z) := rfl

/-- Reading a curried function as its contextual body uses the canonical
binder and ambient projections at the extended context. -/
theorem curry_body (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} {Z : target A}
    (f : CategoricalBindingModel.contextOf (programs A) Γ ⊗ Z ⟶ programs A s)
    (X : Base A) (z : Z.obj X) :
    (powerBodiesIso A Γ s).hom.app X ((curry A f).app X z) =
      programsAtEquiv A s
        (Opposite.op (concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone Γ) X.unop))
        (f.app
          (Opposite.op (concat A.substitution.toClone
            (ContextObject.ofList A.substitution.toClone Γ) X.unop))
          ((contextAtEquiv A Γ
            (Opposite.op (concat A.substitution.toClone
              (ContextObject.ofList A.substitution.toClone Γ) X.unop))).symm
              (fstProjection A.substitution.toClone _ _),
            Z.map (Quiver.Hom.op (sndProjection A.substitution.toClone _ _)) z)) := by
  change scopedBodyEquiv A X.unop Γ s ((curry A f).app X z) = _
  rw [scopedBodyEquiv_apply]
  rfl

/-- Currying a variable projection represents that same prefix variable,
independently of the stage parameter. -/
theorem curry_projection_body (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} {Z : target A} (v : Var Γ s)
    (X : Base A) (z : Z.obj X) :
    (powerBodiesIso A Γ s).hom.app X
        ((curry A (fst (CategoricalBindingModel.contextOf (programs A) Γ) Z ≫
          CategoricalBindingModel.projectVar (programs A) v)).app X z) =
      A.substitution.injectVar (injPrefix (Γ := X.unop.context) Γ v) := by
  rw [curry_body]
  exact context_projection_prefix A v X

/-- The categorical operation recovers the original authored constructor. -/
theorem op_body (A : BindingCloneAlgebra.Algebra.{u} S)
    {s : S.Srt} (o : S.Op s) (X : Base A)
    (args : (CategoricalBindingModel.familyOf (power A) (S.arity o)).obj X) :
    programsAtEquiv A s X ((op A o).app X args) =
      A.operation o (fromFunctions A (familyAtEquiv A (S.arity o) X args)) := rfl

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafPrograms
