import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels
import Mettapedia.OSLF.Syntax.BindingCloneContextComparison
import Mettapedia.GSLT.LanguageDef.MultiSortedCloneFiniteProducts
import Mettapedia.OSLF.Syntax.FreePresheafEventImage
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Contextual states and firing evidence in the clone presheaf category

The established multisorted-clone context category supplies the substitution
base. Programs are represented by singleton contexts. A free firing tree is
kept as an individual point of an event presheaf, with its source and target
in the sorted state presheaf. The endpoint image is a separate subfunctor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

universe u

variable {S : Signature} {M : List (MetaArity S)}

abbrev Base (A : BindingCloneAlgebra.Algebra.{u} S) :=
  (ContextObject A.substitution.toClone)ᵒᵖ

/-- The semantic category has finite limits computed pointwise. -/
theorem hasFiniteLimits (A : BindingCloneAlgebra.Algebra.{u} S) :
    Limits.HasFiniteLimits ((Base A) ⥤ Type u) := inferInstance

/-- The semantic category has the function objects used for binder bodies. -/
@[instance_reducible] def monoidalClosed (A : BindingCloneAlgebra.Algebra.{u} S) :
    MonoidalClosed ((Base A) ⥤ Type u) := inferInstance

/-- One sort is represented by the corresponding singleton context. -/
def programs (A : BindingCloneAlgebra.Algebra.{u} S) (s : S.Srt) :
    (Base A) ⥤ Type u :=
  yoneda.obj (ContextObject.ofList A.substitution.toClone [s])

/-- A represented program is precisely a semantic term of its declared sort. -/
def programsAtEquiv (A : BindingCloneAlgebra.Algebra.{u} S)
    (s : S.Srt) (X : Base A) :
    (programs A s).obj X ≃ A.substitution.Carrier X.unop.context s where
  toFun f := f (0 : Fin 1)
  invFun term := A.substitution.toClone.operationAsSingletonMorphism term
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
    rfl
  right_inv _ := rfl

/-- The explicit semantic carrier of one sort, reindexed by clone
substitution. -/
def semanticPrograms (A : BindingCloneAlgebra.Algebra.{u} S)
    (s : S.Srt) : (Base A) ⥤ Type u where
  obj X := A.substitution.Carrier X.unop.context s
  map f := TypeCat.ofHom (fun term =>
    A.substitution.toClone.substitute term f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro term
    exact A.substitution.toClone.substitute_projects term
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro term
    exact (A.substitution.toClone.substitute_assoc term f.unop g.unop).symm

/-- The semantic program presheaf is represented by a one-variable context,
including naturality under every contextual substitution. -/
def programsIso (A : BindingCloneAlgebra.Algebra.{u} S) (s : S.Srt) :
    programs A s ≅ semanticPrograms A s where
  hom := {
    app X := TypeCat.ofHom (programsAtEquiv A s X)
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro term
      rfl
  }
  inv := {
    app X := TypeCat.ofHom (programsAtEquiv A s X).symm
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro term
      funext i
      refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
      rfl
  }
  hom_inv_id := by
    ext X term
    exact (programsAtEquiv A s X).left_inv term
  inv_hom_id := by
    ext X term
    exact (programsAtEquiv A s X).right_inv term

private abbrev CloneContext (A : BindingCloneAlgebra.Algebra.{u} S) :=
  ContextObject A.substitution.toClone

/-- A natural operation in an argument and an ambient environment is
determined by one operation in the context extended by that argument. -/
private def bodyHomToTensorNat (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (binder result : S.Srt)
    (body : Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) context ⟶
      ContextObject.ofList A.substitution.toClone [result]) :
    (programs A binder ⊗ yoneda.obj context) ⟶ programs A result where
  app stage := TypeCat.ofHom fun pair =>
    Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone pair.1 pair.2 ≫ body
  naturality first last substitution := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, environment⟩
    change first.unop ⟶ ContextObject.ofList A.substitution.toClone [binder]
      at argument
    change first.unop ⟶ context at environment
    have pairNaturality :
        Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
          (substitution.unop ≫ argument) (substitution.unop ≫ environment) =
        substitution.unop ≫
          Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
            argument environment := by
      symm
      apply Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_unique
        A.substitution.toClone
        (substitution.unop ≫ argument) (substitution.unop ≫ environment)
      · rw [Category.assoc,
          Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_fst]
      · rw [Category.assoc,
          Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_snd]
    change Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
        (substitution.unop ≫ argument)
        (substitution.unop ≫ environment) ≫ body =
      substitution.unop ≫
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone argument environment ≫ body)
    rw [pairNaturality, Category.assoc]

private def tensorNatToBodyHom (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (binder result : S.Srt)
    (operation : (programs A binder ⊗ yoneda.obj context) ⟶
      programs A result) :
    Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) context ⟶
      ContextObject.ofList A.substitution.toClone [result] :=
  operation.app (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
    (ContextObject.ofList A.substitution.toClone [binder]) context))
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection A.substitution.toClone _ _,
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection A.substitution.toClone _ _)

/-- At every context, the presheaf internal hom between singleton-program
representables is exactly the clone's binder-extended body carrier. -/
def binderBodyEquiv (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (binder result : S.Srt) :
    ((programs A binder).functorHom (programs A result)).obj
        (Opposite.op context) ≃
      A.substitution.Carrier (binder :: context.context) result :=
  ((yonedaEquiv.symm).trans
    ((FunctorToTypes.functorHomEquiv
      (programs A binder) (yoneda.obj context)
      (programs A result)).trans {
        toFun := tensorNatToBodyHom A context binder result
        invFun := bodyHomToTensorNat A context binder result
        left_inv := by
          intro operation
          apply NatTrans.ext
          funext stage
          apply ConcreteCategory.hom_ext
          rintro ⟨argument, environment⟩
          let input := ContextObject.ofList A.substitution.toClone [binder]
          let extended := Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone input context
          change stage.unop ⟶ input at argument
          change stage.unop ⟶ context at environment
          let canonical : (programs A binder ⊗ yoneda.obj context).obj
              (Opposite.op extended) := by
            change (extended ⟶ input) × (extended ⟶ context)
            exact (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection A.substitution.toClone input context,
              Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection A.substitution.toClone input context)
          have pointwise := operation.naturality_apply
            (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
              argument environment)) canonical
          change operation.app stage
              (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone argument environment ≫
                  Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection A.substitution.toClone input context,
                Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone argument environment ≫
                  Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection A.substitution.toClone input context) =
            Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone argument environment ≫
              tensorNatToBodyHom A context binder result operation at pointwise
          rw [Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_fst, Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_snd] at pointwise
          exact pointwise.symm
        right_inv := by
          intro body
          change Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
              (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection A.substitution.toClone _ _)
              (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection A.substitution.toClone _ _) ≫
                body = body
          have pairIdentity := Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_eta A.substitution.toClone
            (𝟙 (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
              (ContextObject.ofList A.substitution.toClone [binder]) context))
          simpa only [Category.id_comp] using congrArg (fun f => f ≫ body) pairIdentity
      })).trans (programsAtEquiv A result
        (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone [binder]) context)))

/-- Extend an ambient clone substitution while leaving the newly bound
variable untouched. -/
def extendBinderContext (A : BindingCloneAlgebra.Algebra.{u} S)
    (binder : S.Srt) {first last : CloneContext A}
    (f : first ⟶ last) :
    Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) first ⟶
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) last :=
  Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
      A.substitution.toClone _ _)
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
      A.substitution.toClone _ _ ≫ f)

@[simp] theorem extendBinderContext_fst
    (A : BindingCloneAlgebra.Algebra.{u} S) (binder : S.Srt)
    {first last : CloneContext A} (f : first ⟶ last) :
    extendBinderContext A binder f ≫
        Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
          A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone [binder]) last =
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) first :=
  Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_fst
    A.substitution.toClone _ _

@[simp] theorem extendBinderContext_snd
    (A : BindingCloneAlgebra.Algebra.{u} S) (binder : S.Srt)
    {first last : CloneContext A} (f : first ⟶ last) :
    extendBinderContext A binder f ≫
        Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
          A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone [binder]) last =
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) first ≫ f :=
  Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_snd
    A.substitution.toClone _ _

@[simp] theorem extendBinderContext_id
    (A : BindingCloneAlgebra.Algebra.{u} S) (binder : S.Srt)
    (context : CloneContext A) :
    extendBinderContext A binder (𝟙 context) =
      𝟙 (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) context) := by
  simpa [extendBinderContext] using
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_eta
      A.substitution.toClone
      (𝟙 (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) context)))

@[simp] theorem extendBinderContext_comp
    (A : BindingCloneAlgebra.Algebra.{u} S) (binder : S.Srt)
    {first middle last : CloneContext A}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    extendBinderContext A binder (f ≫ g) =
      extendBinderContext A binder f ≫ extendBinderContext A binder g := by
  symm
  apply Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_unique
    A.substitution.toClone
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
      A.substitution.toClone _ _)
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
      A.substitution.toClone _ _ ≫ f ≫ g)
  · rw [Category.assoc, extendBinderContext_fst, extendBinderContext_fst]
  · rw [Category.assoc, extendBinderContext_snd,
      ← Category.assoc, extendBinderContext_snd]
    exact Category.assoc _ _ _

/-- An element of the internal hom is read by applying it at the extended
context to the fresh variable and the ambient projection. -/
theorem binderBodyEquiv_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (binder result : S.Srt)
    (function : ((programs A binder).functorHom (programs A result)).obj
      (Opposite.op context)) :
    binderBodyEquiv A context binder result function =
      ((function.app
        (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
          A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone [binder]) context))
        (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
          A.substitution.toClone _ _)))
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
          A.substitution.toClone _ _)) (0 : Fin 1) := by
  change (tensorNatToBodyHom A context binder result
      ((FunctorToTypes.functorHomEquiv
        (programs A binder) (yoneda.obj context)
        (programs A result)) (yonedaEquiv.symm function))) (0 : Fin 1) = _
  change ((function.app
      (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone [binder]) context))
      (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
        A.substitution.toClone _ _) ≫ 𝟙 _))
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
        A.substitution.toClone _ _)) (0 : Fin 1) = _
  rw [Category.comp_id]

/-- The exponential comparison commutes with every ambient substitution;
the fresh bound variable stays fixed while the ambient environment changes. -/
theorem binderBodyEquiv_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    (binder result : S.Srt) {first last : Base A}
    (f : first ⟶ last)
    (function : ((programs A binder).functorHom (programs A result)).obj first) :
    binderBodyEquiv A last.unop binder result
        (((programs A binder).functorHom (programs A result)).map f function) =
      A.substitution.toClone.substitute
        (binderBodyEquiv A first.unop binder result function)
        (extendBinderContext A binder f.unop) := by
  rw [binderBodyEquiv_apply, binderBodyEquiv_apply]
  let input := ContextObject.ofList A.substitution.toClone [binder]
  let extension := extendBinderContext A binder f.unop
  have naturality := function.naturality
    (Quiver.Hom.op extension)
    (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
      A.substitution.toClone input first.unop))
  have pointwise := ConcreteCategory.congr_hom naturality
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
      A.substitution.toClone input first.unop)
  change
      (function.app (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
        A.substitution.toClone input last.unop))
        (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
          A.substitution.toClone input first.unop) ≫
          Quiver.Hom.op extension))
        (extension ≫ Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
          A.substitution.toClone input first.unop) =
      extension ≫
        (function.app
          (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
            A.substitution.toClone input first.unop))
          (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
            A.substitution.toClone input first.unop)))
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
            A.substitution.toClone input first.unop) at pointwise
  have sndLaw :
      Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
          A.substitution.toClone input first.unop) ≫
        Quiver.Hom.op extension =
      f ≫ Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
        A.substitution.toClone input last.unop) := by
    simpa only [op_comp, Quiver.Hom.op_unop] using congrArg Quiver.Hom.op
      (extendBinderContext_snd A binder f.unop)
  rw [sndLaw, extendBinderContext_fst] at pointwise
  have evaluated := congrFun pointwise (0 : Fin 1)
  change
      ((function.app
        (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
          A.substitution.toClone input last.unop))
        (f ≫ Quiver.Hom.op
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
            A.substitution.toClone input last.unop)))
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
          A.substitution.toClone input last.unop)) (0 : Fin 1) =
      (extension ≫
        (function.app
          (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
            A.substitution.toClone input first.unop))
          (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
            A.substitution.toClone input first.unop)))
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
            A.substitution.toClone input first.unop)) (0 : Fin 1) at evaluated
  exact evaluated

/-- Binder bodies are semantic clone operations in an extended context,
reindexed by a substitution that leaves the binder variable fixed. -/
def binderBodies (A : BindingCloneAlgebra.Algebra.{u} S)
    (binder result : S.Srt) : Base A ⥤ Type u where
  obj X := A.substitution.Carrier (binder :: X.unop.context) result
  map f := TypeCat.ofHom (fun body => A.substitution.toClone.substitute body
    (extendBinderContext A binder f.unop))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro body
    change A.substitution.toClone.substitute body
      (extendBinderContext A binder (𝟙 X.unop)) = body
    rw [extendBinderContext_id]
    exact A.substitution.toClone.substitute_projects body
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro body
    change A.substitution.toClone.substitute body
        (extendBinderContext A binder (g.unop ≫ f.unop)) =
      A.substitution.toClone.substitute
        (A.substitution.toClone.substitute body
          (extendBinderContext A binder f.unop))
        (extendBinderContext A binder g.unop)
    rw [extendBinderContext_comp]
    exact (A.substitution.toClone.substitute_assoc body
      (extendBinderContext A binder f.unop)
      (extendBinderContext A binder g.unop)).symm

/-- The binder-body presheaf is naturally isomorphic to the actual
presheaf exponential between the two singleton-program representables. -/
def binderBodiesIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (binder result : S.Srt) :
    ((programs A binder).functorHom (programs A result)) ≅
      binderBodies A binder result := by
  refine NatIso.ofComponents
    (fun context => (binderBodyEquiv A context.unop binder result).toIso) ?_
  intro first last f
  apply ConcreteCategory.hom_ext
  intro function
  exact binderBodyEquiv_reindex A binder result f function

-- The semantic presheaf category has the finite limits and closed structure
-- used by the following program and event interpretations.
example (A : BindingCloneAlgebra.Algebra.{u} S) :
    _root_.CategoryTheory.Limits.HasFiniteLimits (Base A ⥤ Type u) :=
  inferInstance

example (A : BindingCloneAlgebra.Algebra.{u} S) :
    _root_.CategoryTheory.MonoidalClosed (Base A ⥤ Type u) :=
  inferInstance

/-- Sorted program states, retaining the sort of every endpoint. -/
def states (A : BindingCloneAlgebra.Algebra.{u} S) : (Base A) ⥤ Type u where
  obj X := Σ s : S.Srt, A.substitution.Carrier X.unop.context s
  map f := TypeCat.ofHom (fun state =>
    ⟨state.1, A.substitution.toClone.substitute state.2 f.unop⟩)
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, term⟩
    exact congrArg (Sigma.mk s)
      (A.substitution.toClone.substitute_projects term)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, term⟩
    exact congrArg (Sigma.mk s)
      (A.substitution.toClone.substitute_assoc term f.unop g.unop).symm

/-- An event is an individual free rule tree at one sorted pair of endpoints. -/
abbrev Event (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) : Type u :=
  Σ s : S.Srt, Σ pair : A.substitution.Carrier Γ s ×
      A.substitution.Carrier Γ s,
    Tree R A ⟨Γ, s, pair⟩

/-- Apply one authored rule constructor to its ordered premise derivations.
The result retains the selected occurrence and every child tree. -/
def ruleAction (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).premises.length,
      Tree R A (childJudgment R A occurrence position)) :
    Event R A occurrence.ambient :=
  ⟨(R.get occurrence.index).conclusion.sort,
    (conclusionJudgment R A occurrence).2.2,
    Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
      (⟨occurrence, rfl⟩ : Shape R A (conclusionJudgment R A occurrence))
      children⟩

@[simp] theorem ruleAction_source (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).premises.length,
      Tree R A (childJudgment R A occurrence position)) :
    (ruleAction R A occurrence children).2.1.1 =
      (conclusionJudgment R A occurrence).2.2.1 := rfl

@[simp] theorem ruleAction_target (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).premises.length,
      Tree R A (childJudgment R A occurrence position)) :
    (ruleAction R A occurrence children).2.1.2 =
      (conclusionJudgment R A occurrence).2.2.2 := rfl

/-- Substitution acts on an authored firing by substituting its occurrence
and each ordered premise tree under that premise's local binders. -/
theorem ruleAction_substitute (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).premises.length,
      Tree R A (childJudgment R A occurrence position))
    {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    substTree R A (conclusionJudgment R A occurrence)
      (ruleAction R A occurrence children).2.2 σ
      (conclusionJudgment R A (Instance.subst R occurrence σ))
      (conclusionJudgment_subst R occurrence σ).symm =
    (ruleAction R A (Instance.subst R occurrence σ)
      (fun position =>
        substTree R A (childJudgment R A occurrence position)
          (children position)
          (A.substitution.liftEnvironment σ
            ((R.get occurrence.index).premises.get position).binders)
          (childJudgment R A (Instance.subst R occurrence σ) position)
          (childJudgment_subst R occurrence σ position).symm)).2.2 := by
  rfl

/-- Reindex a complete event by substitution, retaining its tree. -/
noncomputable def mapEvent (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {X Y : Base A} (f : X ⟶ Y) :
    Event R A X.unop.context → Event R A Y.unop.context
  | ⟨s, pair, tree⟩ =>
      ⟨s, (A.substitution.toClone.substitute pair.1 f.unop,
        A.substitution.toClone.substitute pair.2 f.unop),
        substTree R A ⟨X.unop.context, s, pair⟩ tree
          (fromPositions X.unop.context f.unop)
          ⟨Y.unop.context, s,
            (A.substitution.toClone.substitute pair.1 f.unop,
              A.substitution.toClone.substitute pair.2 f.unop)⟩ rfl⟩

/-- Reindexing a rule firing reindexes its authored occurrence and every
ordered premise tree beneath the local binders of that premise. -/
theorem mapEvent_ruleAction (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).premises.length,
      Tree R A (childJudgment R A occurrence position))
    {Y : Base A}
    (f : (Opposite.op (ContextObject.ofList A.substitution.toClone
        occurrence.ambient) : Base A) ⟶ Y) :
    mapEvent R A f (ruleAction R A occurrence children) =
      ruleAction R A
        (Instance.subst R occurrence
          (fromPositions occurrence.ambient f.unop))
        (fun position =>
          substTree R A (childJudgment R A occurrence position)
            (children position)
            (A.substitution.liftEnvironment
              (fromPositions occurrence.ambient f.unop)
              ((R.get occurrence.index).premises.get position).binders)
            (childJudgment R A
              (Instance.subst R occurrence
                (fromPositions occurrence.ambient f.unop)) position)
            (childJudgment_subst R occurrence
              (fromPositions occurrence.ambient f.unop) position).symm) := by
  rcases occurrence with ⟨index, ambient, valuation, close⟩
  let occurrence : Instance R A := ⟨index, ambient, valuation, close⟩
  let σ := fromPositions ambient f.unop
  have judgmentEq :
      substJudgment (conclusionJudgment R A occurrence) σ =
        conclusionJudgment R A (Instance.subst R occurrence σ) :=
    (conclusionJudgment_subst R occurrence σ).symm
  have treeEq : HEq
      (substTree R A (conclusionJudgment R A occurrence)
        (ruleAction R A occurrence children).2.2 σ
        (substJudgment (conclusionJudgment R A occurrence) σ) rfl)
      (ruleAction R A (Instance.subst R occurrence σ)
        (fun position =>
          substTree R A (childJudgment R A occurrence position)
            (children position)
            (A.substitution.liftEnvironment σ
              ((R.get occurrence.index).premises.get position).binders)
            (childJudgment R A (Instance.subst R occurrence σ) position)
            (childJudgment_subst R occurrence σ position).symm)).2.2 := by
    exact (substTree_congr R A (ruleAction R A occurrence children).2.2
      rfl judgmentEq rfl judgmentEq).trans
        (heq_of_eq (ruleAction_substitute R A occurrence children σ))
  have leftEq := substitute_interpretSchema_identity A σ valuation close
    (R.get index).conclusion.lhs
  have rightEq := substitute_interpretSchema_identity A σ valuation close
    (R.get index).conclusion.rhs
  simp [mapEvent, ruleAction, Instance.subst, conclusionJudgment]
  constructor
  · apply Prod.ext
    · exact leftEq
    · exact rightEq
  · change HEq
        (substTree R A (conclusionJudgment R A occurrence)
          (ruleAction R A occurrence children).2.2 σ
          (substJudgment (conclusionJudgment R A occurrence) σ) rfl)
        (ruleAction R A (Instance.subst R occurrence σ)
          (fun position =>
            substTree R A (childJudgment R A occurrence position)
              (children position)
              (A.substitution.liftEnvironment σ
                ((R.get occurrence.index).premises.get position).binders)
              (childJudgment R A (Instance.subst R occurrence σ) position)
              (childJudgment_subst R occurrence σ position).symm)).2.2
    exact treeEq

private theorem identityEnvironment (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) :
    fromPositions Γ (fun i => A.substitution.injectVar (varOfIdx Γ i)) =
      (fun _ v => A.substitution.injectVar v) := by
  funext s v
  exact fromPositions_ofEnvironment
    (fun _ v => A.substitution.injectVar v) v

theorem mapEvent_id (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S) (X : Base A)
    (event : Event R A X.unop.context) :
    mapEvent R A (𝟙 X) event = event := by
  rcases event with ⟨s, ⟨source, target⟩, tree⟩
  have envEq : fromPositions X.unop.context (𝟙 X).unop =
      (fun _ v => A.substitution.injectVar v) := by
    cases X with
    | op X =>
      cases X with
      | mk Γ marker =>
        cases marker
        exact identityEnvironment A Γ
  have targetEq :
      (⟨X.unop.context, s,
        (A.substitution.toClone.substitute source (𝟙 X).unop,
          A.substitution.toClone.substitute target (𝟙 X).unop)⟩ :
        Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A) =
      ⟨X.unop.context, s, (source, target)⟩ := by
    exact congrArg (fun pair => (⟨X.unop.context, s, pair⟩ :
      Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A))
      (Prod.ext (A.substitution.toClone.substitute_projects source)
        (A.substitution.toClone.substitute_projects target))
  dsimp only [mapEvent]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · exact Prod.ext
        (A.substitution.toClone.substitute_projects source)
        (A.substitution.toClone.substitute_projects target)
    · exact (substTree_congr R A tree envEq targetEq rfl
        (substJudgment_identity _)).trans
        (heq_of_eq (substTree_identity R A _ tree
          (substJudgment_identity _)))

private theorem compositionEnvironment
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {X Y Z : Base A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fromPositions X.unop.context (f ≫ g).unop =
      (fun s v => A.substitution.substitute
        (fromPositions Y.unop.context g.unop)
        (fromPositions X.unop.context f.unop s v)) := by
  funext s v
  exact fromPositions_substitute A.substitution f.unop
    (fromPositions Y.unop.context g.unop) v

theorem mapEvent_comp (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {X Y Z : Base A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (event : Event R A X.unop.context) :
    mapEvent R A (f ≫ g) event = mapEvent R A g (mapEvent R A f event) := by
  rcases event with ⟨s, ⟨source, target⟩, tree⟩
  let j : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A :=
    ⟨X.unop.context, s, (source, target)⟩
  let σ : Environment S A.substitution.Carrier X.unop.context Y.unop.context :=
    fromPositions X.unop.context f.unop
  let τ : Environment S A.substitution.Carrier Y.unop.context Z.unop.context :=
    fromPositions Y.unop.context g.unop
  let ρ : Environment S A.substitution.Carrier X.unop.context Z.unop.context :=
    fromPositions X.unop.context (f ≫ g).unop
  have envEq : ρ = fun t v => A.substitution.substitute τ (σ t v) :=
    compositionEnvironment A f g
  have judgedEq : substJudgment j ρ =
      substJudgment j (fun t v => A.substitution.substitute τ (σ t v)) :=
    congrArg (substJudgment j) envEq
  have twiceEq : substJudgment (substJudgment j σ) τ =
      substJudgment j (fun t v => A.substitution.substitute τ (σ t v)) :=
    substJudgment_comp j σ τ
  have directToComp : HEq
      (substTree R A j tree ρ (substJudgment j ρ) rfl)
      (substTree R A j tree
        (fun t v => A.substitution.substitute τ (σ t v))
        (substJudgment j (fun t v => A.substitution.substitute τ (σ t v)))
        rfl) :=
    substTree_congr R A tree envEq judgedEq rfl rfl
  have rightToComp : HEq
      (substTree R A (substJudgment j σ)
        (substTree R A j tree σ (substJudgment j σ) rfl)
        τ (substJudgment (substJudgment j σ) τ) rfl)
      (substTree R A (substJudgment j σ)
        (substTree R A j tree σ (substJudgment j σ) rfl)
        τ (substJudgment j
          (fun t v => A.substitution.substitute τ (σ t v))) twiceEq) :=
    substTree_congr R A _ rfl twiceEq rfl twiceEq
  have twiceIsComp := substTree_comp R A j tree σ τ
    (substJudgment j (fun t v => A.substitution.substitute τ (σ t v)))
    twiceEq rfl
  dsimp only [mapEvent]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · exact Prod.ext
        (A.substitution.toClone.substitute_assoc source f.unop g.unop).symm
        (A.substitution.toClone.substitute_assoc target f.unop g.unop).symm
    · exact directToComp.trans
        ((heq_of_eq twiceIsComp.symm).trans rightToComp.symm)

/-- Complete free firing trees form a presheaf over the same clone contexts
as programs. This uses contextual substitution on evidence, not merely a map
between whole term models. -/
noncomputable def events (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S) : (Base A) ⥤ Type u where
  obj X := Event R A X.unop.context
  map f := TypeCat.ofHom (mapEvent R A f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact mapEvent_id R A X event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact mapEvent_comp R A f g event

/-- Read the source of a retained firing without forgetting its sort. -/
def source (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    events R A ⟶ states A where
  app X := TypeCat.ofHom (fun event => ⟨event.1, event.2.1.1⟩)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, ⟨first, second⟩, tree⟩
    rfl

/-- Read the target of a retained firing without forgetting its sort. -/
def target (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    events R A ⟶ states A where
  app X := TypeCat.ofHom (fun event => ⟨event.1, event.2.1.2⟩)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, ⟨first, second⟩, tree⟩
    rfl

/-- The proof-relevant operational graph in the clone's presheaf category. -/
noncomputable def graph (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    FreePresheafEventExtension.Graph (states A) where
  edge := events R A
  source := source R A
  target := target R A

/-- The one-step endpoint relation is the image of the event graph. -/
noncomputable def reduction (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    Subfunctor (FunctorToTypes.prod (states A) (states A)) :=
  FreePresheafEventImage.endpointImage (graph R A)

/-- Membership in the internal endpoint image agrees exactly with the
previously proved least, substitution-stable one-step relation. -/
theorem mem_reduction_iff (R : List (Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (X : Base A) (s : S.Srt)
    (first last : A.substitution.Carrier X.unop.context s) :
    ((⟨s, first⟩, ⟨s, last⟩) :
      (states A).obj X × (states A).obj X) ∈
        (reduction R A).obj X ↔
      Reduces R (⟨X.unop.context, s, (first, last)⟩ :
        Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A) := by
  change (∃ event : Event R A X.unop.context,
    ((source R A).app X event, (target R A).app X event) =
      (⟨s, first⟩, ⟨s, last⟩)) ↔ _
  constructor
  · rintro ⟨⟨sort, ⟨sourceTerm, targetTerm⟩, tree⟩, endpointsEq⟩
    have sourceEq := congrArg Prod.fst endpointsEq
    have targetEq := congrArg Prod.snd endpointsEq
    have sortEq : sort = s := congrArg Sigma.fst sourceEq
    subst sortEq
    change (⟨sort, sourceTerm⟩ : (states A).obj X) =
      ⟨sort, first⟩ at sourceEq
    change (⟨sort, targetTerm⟩ : (states A).obj X) =
      ⟨sort, last⟩ at targetEq
    have firstEq : sourceTerm = first :=
      eq_of_heq (Sigma.mk.inj_iff.mp sourceEq).2
    have lastEq : targetTerm = last :=
      eq_of_heq (Sigma.mk.inj_iff.mp targetEq).2
    subst firstEq
    subst lastEq
    exact ⟨tree⟩
  · rintro ⟨tree⟩
    exact ⟨⟨s, (first, last), tree⟩, rfl⟩

#print axioms programsIso
#print axioms binderBodiesIso
#print axioms ruleAction_substitute
#print axioms mapEvent_ruleAction
#print axioms mapEvent_id
#print axioms mapEvent_comp
#print axioms mem_reduction_iff

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
