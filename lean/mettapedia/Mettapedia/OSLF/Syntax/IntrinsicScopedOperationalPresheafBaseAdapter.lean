import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafReadback

/-!
# The original binding clone inside every operational presheaf stage

An original contextual value determines a natural family by substituting the
ordinary environment into that value. This construction retains the actual
variables, substitution, and ordered binder operations of the original clone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBaseAdapter

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf
open IntrinsicScopedOperationalPresheafPrograms IntrinsicScopedOperationalPresheafReadback
open BindingFunctionArgumentComparison FreeBindingTerms SecondOrderContext

universe u
variable {S : Signature}

/-- Substitution of an ordinary categorical environment into an original value
is natural under every ambient clone substitution. -/
def baseValue (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {s : S.Srt} (x : A.substitution.Carrier Γ s)
    {U : target A} (ρ : (model A).Env U Γ) : U ⟶ programs A s where
  app X := TypeCat.ofHom fun p => (programsAtEquiv A s X).symm
    (A.substitution.substitute (readEnv A ρ X p) x)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply (programsAtEquiv A s Y).injective
    change A.substitution.substitute (readEnv A ρ Y (U.map f p)) x =
      A.substitution.substitute (fromPositions X.unop.context f.unop)
        (A.substitution.substitute (readEnv A ρ X p) x)
    rw [readEnv_reindex, A.substitution.substitute_comp]

/-- The original contextual value as a natural family at an arbitrary stage. -/
def baseElem (A : BindingCloneAlgebra.Algebra.{u} S) {Z : target A}
    {Γ : Ctx S} {s : S.Srt} (x : A.substitution.Carrier Γ s) :
    (model A).ElemOver Z Γ s where
  value U _ ρ := baseValue A x ρ
  natural h m ρ := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- The adapter's value is the original simultaneous substitution, at every
ordinary environment and every representable point. -/
theorem baseElem_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z U : target A} {Γ : Ctx S} {s : S.Srt} (x : A.substitution.Carrier Γ s)
    (m : U ⟶ Z) (ρ : (model A).Env U Γ) (X : Base A) (p : U.obj X) :
    programsAtEquiv A s X (((baseElem A (Z := Z) x).value U m ρ).app X p) =
      A.substitution.substitute (readEnv A ρ X p) x :=
  (programsAtEquiv A s X).apply_symm_apply _

/-- The adapter sends every original variable to the actual stage variable. -/
theorem baseElem_variable (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    baseElem A (Z := Z) (A.substitution.injectVar v) =
      ((model A).stage Z).substitution.injectVar v := by
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext U m ρ
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro p
  apply (programsAtEquiv A s X).injective
  rw [baseElem_value_point, A.substitution.substitute_var]
  rfl

/-- Reading an environment of adapted original values is the original
environment evaluated by simultaneous substitution. -/
theorem baseEnv_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z U : target A} {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (m : U ⟶ Z) (ρ : (model A).Env U Δ) (X : Base A) (p : U.obj X) :
    readEnv A ((model A).envValue (fun s v => baseElem A (σ s v)) U m ρ) X p =
      (fun s v => A.substitution.substitute (readEnv A ρ X p) (σ s v)) := by
  funext s v
  exact baseElem_value_point A (σ s v) m ρ X p

/-- The adapter preserves actual simultaneous substitution of the original
contextual values. -/
theorem baseElem_substitute (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ Δ : Ctx S} {s : S.Srt}
    (σ : Environment S A.substitution.Carrier Γ Δ) (x : A.substitution.Carrier Γ s) :
    baseElem A (Z := Z) (A.substitution.substitute σ x) =
      ((model A).stage Z).substitution.substitute
        (fun s v => baseElem A (σ s v)) (baseElem A x) := by
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext U m ρ
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro p
  apply (programsAtEquiv A s X).injective
  change programsAtEquiv A s X (((baseElem A (A.substitution.substitute σ x)).value U m ρ).app X p) =
    programsAtEquiv A s X (((baseElem A x).value U m
      ((model A).envValue (fun s v => baseElem A (σ s v)) U m ρ)).app X p)
  rw [baseElem_value_point, baseElem_value_point, baseEnv_value_point,
    A.substitution.substitute_comp]

/-- Every declared semantic argument is read beneath its own authored binder
list, using the original lifted substitution environment. -/
theorem baseArgs_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z U : target A} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S A.substitution.Carrier arity Γ)
      (m : U ⟶ Z) (ρ : (model A).Env U Γ) (X : Base A) (p : U.obj X),
      fromFunctions A (familyAtEquiv A arity X
        (((model A).tupleArgs (toAmbientArgs ⟨[]⟩
          (FamilyArgs.map (fun x => baseElem A (Z := Z) x) args)) U m ρ).app X p)) =
        A.substitution.substituteArgs (readEnv A ρ X p) args
  | _, _, .nil, _, _, _, _ => rfl
  | _, _, .cons (bs := bs) head tail, m, ρ, X, p => by
      change FamilyArgs.cons
          ((powerBodiesIso A bs _).hom.app X
            ((curry A ((baseElem A (Z := Z) head).value
              ((model A).ctx bs ⊗ U) (snd _ _ ≫ m) ((model A).extendEnv bs ρ))).app X p))
          (fromFunctions A (familyAtEquiv A _ X
            (((model A).tupleArgs (toAmbientArgs ⟨[]⟩
              (FamilyArgs.map (fun x => baseElem A (Z := Z) x) tail)) U m ρ).app X p))) =
        FamilyArgs.cons
          (A.substitution.substitute (A.substitution.liftEnvironment (readEnv A ρ X p) bs) head)
          (A.substitution.substituteArgs (readEnv A ρ X p) tail)
      apply congrArg₂ FamilyArgs.cons
      · have curried := curry_body A
          ((baseElem A (Z := Z) head).value ((model A).ctx bs ⊗ U)
            (snd _ _ ≫ m) ((model A).extendEnv bs ρ)) X p
        have evaluated := baseElem_value_point A head (snd _ _ ≫ m)
          ((model A).extendEnv bs ρ) (extendedStage A bs X) (canonicalPoint A bs X p)
        exact curried.trans (evaluated.trans
          (congrArg (fun env => A.substitution.substitute env head)
            (readEnv_extend_canonical A ρ bs X p)))
      · exact baseArgs_value_point A tail m ρ X p

/-- The adapter preserves the original operation with every ordered argument
and every declared binder context. -/
theorem baseElem_operation (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : FamilyArgs S A.substitution.Carrier (S.arity o) Γ) :
    baseElem A (Z := Z) (A.operation o args) =
      ((model A).stage Z).operation o (FamilyArgs.map (fun x => baseElem A x) args) := by
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext U m ρ
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro p
  apply (programsAtEquiv A s X).injective
  change programsAtEquiv A s X (((baseElem A (A.operation o args)).value U m ρ).app X p) =
    programsAtEquiv A s X ((op A o).app X
      (((model A).tupleArgs (toAmbientArgs ⟨[]⟩
        (FamilyArgs.map (fun x => baseElem A (Z := Z) x) args)) U m ρ).app X p))
  have operation := op_body A o X
    (((model A).tupleArgs (toAmbientArgs ⟨[]⟩
      (FamilyArgs.map (fun x => baseElem A (Z := Z) x) args)) U m ρ).app X p)
  exact (baseElem_value_point A (A.operation o args) m ρ X p).trans
    ((A.operation_substitute (readEnv A ρ X p) o args).trans
      ((congrArg (A.operation o) (baseArgs_value_point A args m ρ X p)).symm.trans
        operation.symm))

/-- The original binding clone maps into the actual generalized-element clone
at every presheaf stage, preserving variables, substitution and operators. -/
def baseHom (A : BindingCloneAlgebra.Algebra.{u} S) (Z : target A) :
    FreeBindingClone.Hom A ((model A).stage Z) where
  raw := {
    map := baseElem A
    map_variable := baseElem_variable A
    map_operation := baseElem_operation A
  }
  map_substitute := baseElem_substitute A

/-- The named adapter commutes with the original free binding-clone
interpretation by its proved homomorphism laws and the existing initiality. -/
theorem baseHom_interpret (A : BindingCloneAlgebra.Algebra.{u} S) (Z : target A) :
    FreeBindingClone.Hom.comp (FreeBindingClone.interpretHom A) (baseHom A Z) =
      FreeBindingClone.interpretHom ((model A).stage Z) :=
  FreeBindingClone.hom_unique _ _

/-- Original term interpretation followed by the adapter is exactly term
interpretation in the actual stage clone. -/
theorem baseElem_interpret (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s) :
    baseElem A (Z := Z) (BindingCloneFoldSubstitution.interpret A term) =
      BindingCloneFoldSubstitution.interpret ((model A).stage Z) term :=
  congrArg (fun h : FreeBindingClone.Hom (BindingCloneAlgebra.terms S) ((model A).stage Z) =>
    h.raw.map term) (baseHom_interpret A Z)

/-- The named interpretation comparison reads at an arbitrary ordinary
environment as the original clone interpretation followed by substitution. -/
theorem interpret_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z U : target A} {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s)
    (m : U ⟶ Z) (ρ : (model A).Env U Γ) (X : Base A) (p : U.obj X) :
    programsAtEquiv A s X
      (((BindingCloneFoldSubstitution.interpret ((model A).stage Z) term :
        (model A).ElemOver Z Γ s).value U m ρ).app X p) =
      A.substitution.substitute (readEnv A ρ X p)
        (BindingCloneFoldSubstitution.interpret A term) := by
  exact (congrArg (fun e : (model A).ElemOver Z Γ s =>
      programsAtEquiv A s X ((e.value U m ρ).app X p))
    (baseElem_interpret A term).symm).trans
      (baseElem_value_point A _ m ρ X p)

/-- Reading an adapted original value retains its full ordinary prefix and
introduces no dependence on the ambient presheaf parameter. -/
theorem read_baseElem (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt} (x : A.substitution.Carrier Γ s)
    (X : Base A) (z : Z.obj X) :
    read A (baseElem A x) X z =
      A.substitution.substitute
        (fun _ v => A.substitution.injectVar (injPrefix (Γ := X.unop.context) Γ v)) x := by
  have generic : readEnv A ((model A).genericEnv Γ Z) (extendedStage A Γ X)
      (canonicalPoint A Γ X z) =
        (fun _ v => A.substitution.injectVar (injPrefix (Γ := X.unop.context) Γ v)) := by
    funext s v
    exact context_projection_prefix A v X
  exact (read_canonical A (baseElem A x) X z).trans
    ((baseElem_value_point A x (snd _ _) ((model A).genericEnv Γ Z)
      (extendedStage A Γ X) (canonicalPoint A Γ X z)).trans
        (congrArg (fun env => A.substitution.substitute env x) generic))

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBaseAdapter
