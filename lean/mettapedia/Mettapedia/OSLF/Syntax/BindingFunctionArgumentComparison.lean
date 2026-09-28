import Mettapedia.OSLF.Syntax.BindingContextExtensionComparison

/-!
# Authored operator arguments as contextual function arguments

Each argument of an authored binding operator carries its own ordered binder
context. This file compares the actual semantic argument family with the
corresponding family of presheaf function objects, including reindexing by
ambient substitution. No program equation or operational step is added by
this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingFunctionArgumentComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.BindingOperationPresheaf

universe u
variable {S : Signature}

/-- A semantic operator's arguments, each represented as a function of its
own local binder context. -/
inductive FunctionArgs (A : BindingCloneAlgebra.Algebra.{u} S) :
    List (List S.Srt × S.Srt) → Ctx S → Type u where
  | nil {Γ : Ctx S} : FunctionArgs A [] Γ
  | cons {bs : Ctx S} {sort : S.Srt}
      {rest : List (List S.Srt × S.Srt)} {Γ : Ctx S} :
      ((binders A bs).functorHom (programs A sort)).obj
        (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)) →
      FunctionArgs A rest Γ →
      FunctionArgs A ((bs, sort) :: rest) Γ

/-- The categorical action of an ambient substitution on every contextual
function argument. -/
def FunctionArgs.reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ) :
    {arity : List (List S.Srt × S.Srt)} →
      FunctionArgs A arity Γ → FunctionArgs A arity Δ
  | _, .nil => .nil
  | _, .cons (bs := bs) (sort := sort) head tail =>
      .cons
        (((binders A bs).functorHom (programs A sort)).map
          (Quiver.Hom.op (environmentArrow A σ)) head)
        (FunctionArgs.reindex A σ tail)

/-- A binding-clone interpretation maps each contextual function argument,
including the particular binder context of that argument. -/
def FunctionArgs.mapModel {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FunctionArgs A arity Γ → FunctionArgs B arity Γ
  | _, _, .nil => .nil
  | _, Γ, .cons (bs := bs) (sort := sort) head tail =>
      .cons
        ((mapScopedFunctions h bs sort).app
          (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)) head)
        (FunctionArgs.mapModel h tail)

/-- Read the source algebra's actual argument tuple as a tuple of contextual
function objects. -/
def toFunctions (A : BindingCloneAlgebra.Algebra.{u} S) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FamilyArgs S A.substitution.Carrier arity Γ → FunctionArgs A arity Γ
  | _, _, .nil => .nil
  | _, Γ, .cons (bs := bs) (s := sort) head tail =>
      .cons
        ((scopedBodyEquiv A
          (ContextObject.ofList A.substitution.toClone Γ) bs sort).symm head)
        (toFunctions A tail)

/-- Recover the original source argument tuple without identifying any
distinct bodies. -/
def fromFunctions (A : BindingCloneAlgebra.Algebra.{u} S) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FunctionArgs A arity Γ → FamilyArgs S A.substitution.Carrier arity Γ
  | _, _, .nil => .nil
  | _, Γ, .cons (bs := bs) (sort := sort) head tail =>
      .cons
        (scopedBodyEquiv A
          (ContextObject.ofList A.substitution.toClone Γ) bs sort head)
        (fromFunctions A tail)

theorem fromFunctions_toFunctions (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S A.substitution.Carrier arity Γ),
      fromFunctions A (toFunctions A args) = args
  | _, _, .nil => rfl
  | _, Γ, .cons (bs := bs) (s := sort) head tail => by
      change FamilyArgs.cons
          ((scopedBodyEquiv A
            (ContextObject.ofList A.substitution.toClone Γ) bs sort)
            ((scopedBodyEquiv A
              (ContextObject.ofList A.substitution.toClone Γ) bs sort).symm head))
          (fromFunctions A (toFunctions A tail)) =
        FamilyArgs.cons head tail
      exact congrArg₂ FamilyArgs.cons
        ((scopedBodyEquiv A
          (ContextObject.ofList A.substitution.toClone Γ) bs sort).apply_symm_apply head)
        (fromFunctions_toFunctions A tail)

theorem toFunctions_fromFunctions (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FunctionArgs A arity Γ),
      toFunctions A (fromFunctions A args) = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [toFunctions, fromFunctions,
        Equiv.symm_apply_apply, toFunctions_fromFunctions A tail]

/-- The source argument carrier is precisely the contextual-function tuple. -/
def argumentEquiv (A : BindingCloneAlgebra.Algebra.{u} S)
    (arity : List (List S.Srt × S.Srt)) (Γ : Ctx S) :
    FamilyArgs S A.substitution.Carrier arity Γ ≃ FunctionArgs A arity Γ where
  toFun := toFunctions A
  invFun := fromFunctions A
  left_inv := fromFunctions_toFunctions A
  right_inv := toFunctions_fromFunctions A

/-- The equivalence respects arbitrary ambient substitution, including the
different local binders on different arguments. -/
theorem toFunctions_substitute (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S A.substitution.Carrier arity Γ),
      toFunctions A (A.substitution.substituteArgs σ args) =
        FunctionArgs.reindex A σ (toFunctions A args)
  | _, .nil => rfl
  | _, .cons (bs := bs) (s := sort) head tail => by
      simp only [BindingSubstitutionAlgebra.Algebra.substituteArgs,
        toFunctions, FunctionArgs.reindex]
      apply congrArg₂ FunctionArgs.cons
      · apply (scopedBodyEquiv A
          (ContextObject.ofList A.substitution.toClone Δ) bs sort).injective
        dsimp only [ContextObject.ofList, ContextObject.context]
        have reindex := scopedBodyEquiv_reindex A bs sort
          (Quiver.Hom.op (environmentArrow A σ))
          ((scopedBodyEquiv A
            (ContextObject.ofList A.substitution.toClone Γ) bs sort).symm head)
        have hbody :
            A.substitution.substitute
              (A.substitution.liftEnvironment σ bs) head =
            A.substitution.toClone.substitute head
              (extendScope A bs (environmentArrow A σ)) := by
          rw [extendScope_environment]
          change A.substitution.substitute
              (A.substitution.liftEnvironment σ bs) head =
            A.substitution.substitute
              (fromPositions (bs ++ Γ)
                (environmentArrow A (A.substitution.liftEnvironment σ bs)))
              head
          congr 1
          funext s v
          exact (fromPositions_ofEnvironment
            (A.substitution.liftEnvironment σ bs) v).symm
        have hReindex :
            (scopedBodyEquiv A
              (ContextObject.ofList A.substitution.toClone Δ) bs sort)
              (((binders A bs).functorHom (programs A sort)).map
                (Quiver.Hom.op (environmentArrow A σ))
                ((scopedBodyEquiv A
                  (ContextObject.ofList A.substitution.toClone Γ) bs sort).symm head)) =
            A.substitution.toClone.substitute head
              (extendScope A bs (environmentArrow A σ)) := by
          have hHead :
              (scopedBodyEquiv A
                (ContextObject.ofList A.substitution.toClone Γ) bs sort)
                ((scopedBodyEquiv A
                  (ContextObject.ofList A.substitution.toClone Γ) bs sort).symm head) =
              head := Equiv.apply_symm_apply _ _
          rw [hHead] at reindex
          exact reindex
        exact (Equiv.apply_symm_apply _ _).trans
          (hbody.trans hReindex.symm)
      · exact toFunctions_substitute A σ tail

/-- The actual source model map and the contextual-function map agree for
every authored operator argument tuple. -/
theorem toFunctions_map
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S A.substitution.Carrier arity Γ),
      toFunctions B (FamilyArgs.map h.raw.map args) =
        FunctionArgs.mapModel h (toFunctions A args)
  | _, _, .nil => rfl
  | _, Γ, .cons (bs := bs) (s := sort) head tail => by
      simp only [FamilyArgs.map, toFunctions, FunctionArgs.mapModel]
      apply congrArg₂ FunctionArgs.cons
      · apply (scopedBodyEquiv B
          (ContextObject.ofList B.substitution.toClone Γ) bs sort).injective
        have hBody := mapScopedFunctions_body h bs sort
          (ContextObject.ofList A.substitution.toClone Γ)
          ((scopedBodyEquiv A
            (ContextObject.ofList A.substitution.toClone Γ) bs sort).symm head)
        have hHead :
            (scopedBodyEquiv A
              (ContextObject.ofList A.substitution.toClone Γ) bs sort)
              ((scopedBodyEquiv A
                (ContextObject.ofList A.substitution.toClone Γ) bs sort).symm head) =
            head := Equiv.apply_symm_apply _ _
        rw [hHead] at hBody
        exact (Equiv.apply_symm_apply _ _).trans hBody.symm
      · exact toFunctions_map h tail

/-- Mapping contextual-function arguments by the identity model map is the
identity on each tuple. -/
theorem FunctionArgs.mapModel_id (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FunctionArgs A arity Γ),
      FunctionArgs.mapModel (FreeBindingClone.Hom.id A) args = args
  | _, _, .nil => rfl
  | _, Γ, .cons (bs := bs) (sort := sort) head tail => by
      simp only [FunctionArgs.mapModel]
      exact congrArg₂ FunctionArgs.cons
        (mapScopedFunctions_id A bs sort
          (ContextObject.ofList A.substitution.toClone Γ) head)
        (FunctionArgs.mapModel_id A tail)

/-- Interpreting a tuple through two binding models composes pointwise,
retaining each argument's contextual function object. -/
theorem FunctionArgs.mapModel_comp
    {A B C : BindingCloneAlgebra.Algebra.{u} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FunctionArgs A arity Γ),
      FunctionArgs.mapModel (FreeBindingClone.Hom.comp first second) args =
        FunctionArgs.mapModel second (FunctionArgs.mapModel first args)
  | _, _, .nil => rfl
  | _, Γ, .cons (bs := bs) (sort := sort) head tail => by
      simp only [FunctionArgs.mapModel]
      exact congrArg₂ FunctionArgs.cons
        (mapScopedFunctions_comp first second bs sort
          (ContextObject.ofList A.substitution.toClone Γ) head)
        (FunctionArgs.mapModel_comp first second tail)

/-- Reindexing a tuple of represented functions reads back to the source
algebra's actual capture-avoiding substitution of its argument family. -/
theorem fromFunctions_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ)
    {arity : List (List S.Srt × S.Srt)}
    (args : FunctionArgs A arity Γ) :
    fromFunctions A (FunctionArgs.reindex A σ args) =
      A.substitution.substituteArgs σ (fromFunctions A args) := by
  apply (argumentEquiv A arity Δ).injective
  change toFunctions A (fromFunctions A (FunctionArgs.reindex A σ args)) =
    toFunctions A
      (A.substitution.substituteArgs σ (fromFunctions A args))
  rw [toFunctions_fromFunctions, toFunctions_substitute,
    toFunctions_fromFunctions]

/-- Identity substitution fixes the represented contextual-function tuple. -/
theorem FunctionArgs.reindex_id (A : BindingCloneAlgebra.Algebra.{u} S)
    {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (args : FunctionArgs A arity Γ) :
    FunctionArgs.reindex A
      (fun _ v => A.substitution.injectVar v) args = args := by
  apply (argumentEquiv A arity Γ).symm.injective
  change fromFunctions A
      (FunctionArgs.reindex A
        (fun _ v => A.substitution.injectVar v) args) =
    fromFunctions A args
  rw [fromFunctions_reindex]
  exact substituteArgs_identity A.substitution (fromFunctions A args)

/-- Contextual-function argument reindexing composes with the actual
capture-avoiding substitution law for arbitrary nested binder lists. -/
theorem FunctionArgs.reindex_comp (A : BindingCloneAlgebra.Algebra.{u} S)
    {arity : List (List S.Srt × S.Srt)} {Γ Δ Θ : Ctx S}
    (first : Environment S A.substitution.Carrier Γ Δ)
    (second : Environment S A.substitution.Carrier Δ Θ)
    (args : FunctionArgs A arity Γ) :
    FunctionArgs.reindex A second
      (FunctionArgs.reindex A first args) =
    FunctionArgs.reindex A
      (fun sort var => A.substitution.substitute second (first sort var))
      args := by
  apply (argumentEquiv A arity Θ).symm.injective
  change fromFunctions A
      (FunctionArgs.reindex A second
        (FunctionArgs.reindex A first args)) =
    fromFunctions A
      (FunctionArgs.reindex A
        (fun sort var => A.substitution.substitute second (first sort var))
        args)
  rw [fromFunctions_reindex, fromFunctions_reindex,
    fromFunctions_reindex]
  exact substituteArgs_comp A.substitution first second
    (fromFunctions A args)

/-- Interpreting a mapped function tuple reads back to the actual authored
binding-clone interpretation on source arguments. -/
theorem fromFunctions_map
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (args : FunctionArgs A arity Γ) :
    fromFunctions B (FunctionArgs.mapModel h args) =
      FamilyArgs.map h.raw.map (fromFunctions A args) := by
  apply (argumentEquiv B arity Γ).injective
  change toFunctions B (fromFunctions B (FunctionArgs.mapModel h args)) =
    toFunctions B (FamilyArgs.map h.raw.map (fromFunctions A args))
  rw [toFunctions_fromFunctions, toFunctions_map,
    toFunctions_fromFunctions]

/-- A model map commutes with contextual reindexing of the interpreted
function tuple, including each argument's own binder lift. -/
theorem FunctionArgs.mapModel_reindex
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    {arity : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (args : FunctionArgs A arity Γ) :
    FunctionArgs.mapModel h (FunctionArgs.reindex A σ args) =
    FunctionArgs.reindex B (fun sort var => h.raw.map (σ sort var))
      (FunctionArgs.mapModel h args) := by
  apply (argumentEquiv B arity Δ).symm.injective
  change fromFunctions B
      (FunctionArgs.mapModel h (FunctionArgs.reindex A σ args)) =
    fromFunctions B
      (FunctionArgs.reindex B
        (fun sort var => h.raw.map (σ sort var))
        (FunctionArgs.mapModel h args))
  have firstMap := fromFunctions_map h
    (FunctionArgs.reindex A σ args)
  have sourceReindex := fromFunctions_reindex A σ args
  have targetReindex := fromFunctions_reindex B
    (fun sort var => h.raw.map (σ sort var))
    (FunctionArgs.mapModel h args)
  have laterMap := fromFunctions_map h args
  exact firstMap.trans
    ((congrArg (FamilyArgs.map h.raw.map) sourceReindex).trans
      ((map_substituteArgs h σ (fromFunctions A args)).trans
        ((congrArg
          (B.substitution.substituteArgs
            (fun sort var => h.raw.map (σ sort var)))
          laterMap.symm).trans targetReindex.symm)))

/-- The contextual-function tuples form a presheaf over the actual clone
substitution category. Its functor laws follow from the authored argument
substitution laws, including arbitrary binder lists. -/
def functionArguments (A : BindingCloneAlgebra.Algebra.{u} S)
    (arity : List (List S.Srt × S.Srt)) : Base A ⥤ Type u where
  obj X := FunctionArgs A arity X.unop.context
  map f := TypeCat.ofHom (FunctionArgs.reindex A
    (fromPositions _ f.unop))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro args
    have envEq :
        fromPositions X.unop.context (𝟙 X).unop =
          (fun _ v => A.substitution.injectVar v) := by
      funext sort var
      exact fromPositions_ofEnvironment
        (fun _ v => A.substitution.injectVar v) var
    change FunctionArgs.reindex A
        (fromPositions X.unop.context (𝟙 X).unop) args = args
    exact (congrArg (fun env => FunctionArgs.reindex A env args)
      envEq).trans (FunctionArgs.reindex_id A args)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro args
    have envEq :
        fromPositions _ (f ≫ g).unop =
          (fun sort var => A.substitution.substitute
            (fromPositions _ g.unop)
            (fromPositions _ f.unop sort var)) := by
      funext sort var
      exact fromPositions_substitute A.substitution f.unop
        (fromPositions _ g.unop) var
    change FunctionArgs.reindex A
        (fromPositions _ (f ≫ g).unop) args =
      FunctionArgs.reindex A (fromPositions _ g.unop)
        (FunctionArgs.reindex A (fromPositions _ f.unop) args)
    exact (congrArg (fun env => FunctionArgs.reindex A env args)
      envEq).trans
        (FunctionArgs.reindex_comp A
          (fromPositions _ f.unop) (fromPositions _ g.unop) args).symm

/-- The actual authored argument presheaf is naturally isomorphic to the
tuple of genuine contextual presheaf function objects. -/
def argumentIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (arity : List (List S.Srt × S.Srt)) :
    arguments A arity ≅ functionArguments A arity where
  hom := {
    app X := TypeCat.ofHom (toFunctions A)
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro args
      exact toFunctions_substitute A
        (fromPositions _ f.unop) args
  }
  inv := {
    app X := TypeCat.ofHom (fromFunctions A)
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro args
      exact fromFunctions_reindex A
        (fromPositions _ f.unop) args
  }
  hom_inv_id := by
    ext X args
    exact fromFunctions_toFunctions A args
  inv_hom_id := by
    ext X args
    exact toFunctions_fromFunctions A args

/-- Every binding-clone interpretation induces a natural map of the complete
contextual-function argument presheaves. -/
def mapFunctionArguments
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    (arity : List (List S.Srt × S.Srt)) :
    functionArguments A arity ⟶
      h.toCloneTranslation.contextFunctor.op ⋙ functionArguments B arity where
  app X := TypeCat.ofHom (FunctionArgs.mapModel h)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro args
    have envEq :
        fromPositions X.unop.context
          (h.toCloneTranslation.contextFunctor.op.map f).unop =
        (fun sort var => h.raw.map
          (fromPositions X.unop.context f.unop sort var)) := by
      funext sort var
      exact (bindingHom_fromPositions h X.unop.context f.unop var).symm
    change FunctionArgs.mapModel h
        (FunctionArgs.reindex A
          (fromPositions X.unop.context f.unop) args) =
      FunctionArgs.reindex B
        (fromPositions X.unop.context
          (h.toCloneTranslation.contextFunctor.op.map f).unop)
        (FunctionArgs.mapModel h args)
    exact (FunctionArgs.mapModel_reindex h
      (fromPositions X.unop.context f.unop) args).trans
        (congrArg (fun env => FunctionArgs.reindex B env
          (FunctionArgs.mapModel h args)) envEq.symm)

/-- The contextual-function comparison commutes with actual model maps on
the source argument presheaf, at each ambient substitution context. -/
theorem argumentIso_map
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    (arity : List (List S.Srt × S.Srt)) (X : Base A)
    (args : (arguments A arity).obj X) :
    ((mapFunctionArguments h arity).app X)
        (((argumentIso A arity).hom.app X) args) =
      ((argumentIso B arity).hom.app
        (h.toCloneTranslation.contextFunctor.op.obj X))
        (((mapArguments h arity).app X) args) :=
  (toFunctions_map h args).symm

/-- An authored binding constructor interpreted on the genuine contextual
function arguments of its declared arity. -/
def applyFunctionArgs (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (args : FunctionArgs A (S.arity operator) Γ) :
    A.substitution.Carrier Γ sort :=
  A.operation operator (fromFunctions A args)

/-- The authored constructor as a natural transformation from the genuine
contextual-function argument presheaf into the result-program presheaf. -/
def functionOperation (A : BindingCloneAlgebra.Algebra.{u} S)
    {sort : S.Srt} (operator : S.Op sort) :
    functionArguments A (S.arity operator) ⟶
      semanticPrograms A sort :=
  (argumentIso A (S.arity operator)).inv ≫ operation A operator

theorem functionOperation_body (A : BindingCloneAlgebra.Algebra.{u} S)
    {sort : S.Srt} (operator : S.Op sort)
    (X : Base A)
    (args : (functionArguments A (S.arity operator)).obj X) :
    ((functionOperation A operator).app X) args =
      applyFunctionArgs A operator args := rfl

/-- The contextual-function interpretation of an authored constructor is
natural in ambient substitution. -/
theorem applyFunctionArgs_substitute
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ)
    {sort : S.Srt} (operator : S.Op sort)
    (args : FunctionArgs A (S.arity operator) Γ) :
    applyFunctionArgs A operator (FunctionArgs.reindex A σ args) =
      A.substitution.substitute σ (applyFunctionArgs A operator args) := by
  unfold applyFunctionArgs
  rw [fromFunctions_reindex]
  exact (A.operation_substitute σ operator (fromFunctions A args)).symm

/-- The contextual-function interpretation of an authored constructor is
preserved by every binding-clone model map. -/
theorem applyFunctionArgs_map
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (args : FunctionArgs A (S.arity operator) Γ) :
    h.raw.map (applyFunctionArgs A operator args) =
      applyFunctionArgs B operator (FunctionArgs.mapModel h args) := by
  unfold applyFunctionArgs
  rw [fromFunctions_map]
  exact h.raw.map_operation operator (fromFunctions A args)

/-- A model morphism preserves each authored constructor interpreted on
contextual functions, not just its uncurried source argument family. -/
theorem functionOperation_map
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    {sort : S.Srt} (operator : S.Op sort)
    (X : Base A)
    (args : (functionArguments A (S.arity operator)).obj X) :
    ((mapPrograms h sort).app X)
      (((functionOperation A operator).app X) args) =
    ((functionOperation B operator).app
      (h.toCloneTranslation.contextFunctor.op.obj X))
      (((mapFunctionArguments h (S.arity operator)).app X) args) :=
  applyFunctionArgs_map h operator args

#print axioms argumentEquiv
#print axioms toFunctions_substitute
#print axioms toFunctions_map
#print axioms FunctionArgs.mapModel_comp
#print axioms FunctionArgs.reindex_comp
#print axioms FunctionArgs.mapModel_reindex
#print axioms argumentIso
#print axioms mapFunctionArguments
#print axioms argumentIso_map
#print axioms applyFunctionArgs_substitute
#print axioms applyFunctionArgs_map
#print axioms functionOperation_map

end Mettapedia.OSLF.Binding.BindingFunctionArgumentComparison
