import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPresheaf
import Mettapedia.OSLF.Syntax.BindingCloneContextComparison

/-!
# Whole-context binder bodies in the clone presheaf model

An authored premise can bind an arbitrary ordered list of sorts. Its body is
represented by the exponential from that whole context's representable into
the result-sort program representable. The equivalence below applies to every
multisorted binding clone, including the equation quotient, and does not
identify an operational step with an equation of programs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MultiBinderPresheaf

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf

universe u

variable {S : Signature}

private abbrev CloneContext (A : BindingCloneAlgebra.Algebra.{u} S) :=
  ContextObject A.substitution.toClone

/-- The representable for an entire ordered binder context. -/
def binders (A : BindingCloneAlgebra.Algebra.{u} S) (scope : Ctx S) :
    Base A ⥤ Type u :=
  yoneda.obj (ContextObject.ofList A.substitution.toClone scope)

private def bodyToTensorNat (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (scope : Ctx S) (result : S.Srt)
    (body : Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context ⟶
      ContextObject.ofList A.substitution.toClone [result]) :
    (binders A scope ⊗ yoneda.obj context) ⟶ programs A result where
  app stage := TypeCat.ofHom fun pair =>
    Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
      pair.1 pair.2 ≫ body
  naturality first last substitution := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, environment⟩
    change first.unop ⟶ ContextObject.ofList A.substitution.toClone scope
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
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
          argument environment ≫ body)
    rw [pairNaturality, Category.assoc]

private def tensorNatToBody (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (scope : Ctx S) (result : S.Srt)
    (operation : (binders A scope ⊗ yoneda.obj context) ⟶ programs A result) :
    Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context ⟶
      ContextObject.ofList A.substitution.toClone [result] :=
  operation.app (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
    A.substitution.toClone
    (ContextObject.ofList A.substitution.toClone scope) context))
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection A.substitution.toClone _ _,
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection A.substitution.toClone _ _)

/-- A function of a whole binder context is exactly one semantic body in
that context, naturally in its ambient variables. -/
def scopedBodyEquiv (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (scope : Ctx S) (result : S.Srt) :
    ((binders A scope).functorHom (programs A result)).obj
        (Opposite.op context) ≃
      A.substitution.Carrier (scope ++ context.context) result :=
  ((yonedaEquiv.symm).trans
    ((FunctorToTypes.functorHomEquiv
      (binders A scope) (yoneda.obj context)
      (programs A result)).trans {
        toFun := tensorNatToBody A context scope result
        invFun := bodyToTensorNat A context scope result
        left_inv := by
          intro operation
          apply NatTrans.ext
          funext stage
          apply ConcreteCategory.hom_ext
          rintro ⟨argument, environment⟩
          let input := ContextObject.ofList A.substitution.toClone scope
          let extended := Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
            A.substitution.toClone input context
          change stage.unop ⟶ input at argument
          change stage.unop ⟶ context at environment
          let canonical : (binders A scope ⊗ yoneda.obj context).obj
              (Opposite.op extended) := by
            change (extended ⟶ input) × (extended ⟶ context)
            exact (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
              A.substitution.toClone input context,
              Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
                A.substitution.toClone input context)
          have pointwise := operation.naturality_apply
            (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair
              A.substitution.toClone argument environment)) canonical
          change operation.app stage
              (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair
                  A.substitution.toClone argument environment ≫
                Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
                  A.substitution.toClone input context,
                Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair
                  A.substitution.toClone argument environment ≫
                Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
                  A.substitution.toClone input context) =
            Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair
              A.substitution.toClone argument environment ≫
              tensorNatToBody A context scope result operation at pointwise
          rw [Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_fst,
            Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_snd]
            at pointwise
          exact pointwise.symm
        right_inv := by
          intro body
          change Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair
              A.substitution.toClone
              (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
                A.substitution.toClone _ _)
              (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
                A.substitution.toClone _ _) ≫ body = body
          have pairIdentity :=
            Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_eta
              A.substitution.toClone
              (𝟙 (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
                A.substitution.toClone
                (ContextObject.ofList A.substitution.toClone scope) context))
          simpa only [Category.id_comp] using
            congrArg (fun f => f ≫ body) pairIdentity
      })).trans (programsAtEquiv A result
        (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
          A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) context)))

/-- Extend an ambient substitution past a whole binder context while
preserving every binder projection. -/
def extendScope (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) {first last : CloneContext A}
    (f : first ⟶ last) :
    Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) first ⟶
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) last :=
  Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair A.substitution.toClone
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
      A.substitution.toClone _ _)
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
      A.substitution.toClone _ _ ≫ f)

@[simp] theorem extendScope_fst
    (A : BindingCloneAlgebra.Algebra.{u} S) (scope : Ctx S)
    {first last : CloneContext A} (f : first ⟶ last) :
    extendScope A scope f ≫
        Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
          A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) last =
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) first :=
  Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_fst
    A.substitution.toClone _ _

@[simp] theorem extendScope_snd
    (A : BindingCloneAlgebra.Algebra.{u} S) (scope : Ctx S)
    {first last : CloneContext A} (f : first ⟶ last) :
    extendScope A scope f ≫
        Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
          A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) last =
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) first ≫ f :=
  Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_snd
    A.substitution.toClone _ _

@[simp] theorem extendScope_id
    (A : BindingCloneAlgebra.Algebra.{u} S) (scope : Ctx S)
    (context : CloneContext A) :
    extendScope A scope (𝟙 context) =
      𝟙 (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context) := by
  simpa [extendScope] using
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_eta
      A.substitution.toClone
      (𝟙 (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context)))

@[simp] theorem extendScope_comp
    (A : BindingCloneAlgebra.Algebra.{u} S) (scope : Ctx S)
    {first middle last : CloneContext A}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    extendScope A scope (f ≫ g) =
      extendScope A scope f ≫ extendScope A scope g := by
  symm
  apply Mettapedia.GSLT.LanguageDef.MultiSortedClone.categorical_pair_unique
    A.substitution.toClone
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
      A.substitution.toClone _ _)
    (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
      A.substitution.toClone _ _ ≫ f ≫ g)
  · rw [Category.assoc, extendScope_fst, extendScope_fst]
  · rw [Category.assoc, extendScope_snd,
      ← Category.assoc, extendScope_snd]
    exact Category.assoc _ _ _

/-- Read the function at the context extended by all its bound variables. -/
theorem scopedBodyEquiv_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CloneContext A) (scope : Ctx S) (result : S.Srt)
    (function : ((binders A scope).functorHom (programs A result)).obj
      (Opposite.op context)) :
    scopedBodyEquiv A context scope result function =
      ((function.app
        (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
          A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) context))
        (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
          A.substitution.toClone _ _)))
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
          A.substitution.toClone _ _)) (0 : Fin 1) := by
  change (tensorNatToBody A context scope result
      ((FunctorToTypes.functorHomEquiv
        (binders A scope) (yoneda.obj context)
        (programs A result)) (yonedaEquiv.symm function))) (0 : Fin 1) = _
  change ((function.app
      (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat
        A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context))
      (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
        A.substitution.toClone _ _) ≫ 𝟙 _))
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
        A.substitution.toClone _ _)) (0 : Fin 1) = _
  rw [Category.comp_id]

/-- The whole-context exponential comparison respects every ambient
substitution while keeping all newly bound variables fixed. -/
theorem scopedBodyEquiv_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (result : S.Srt) {first last : Base A}
    (f : first ⟶ last)
    (function : ((binders A scope).functorHom (programs A result)).obj first) :
    scopedBodyEquiv A last.unop scope result
        (((binders A scope).functorHom (programs A result)).map f function) =
      A.substitution.toClone.substitute
        (scopedBodyEquiv A first.unop scope result function)
        (extendScope A scope f.unop) := by
  rw [scopedBodyEquiv_apply, scopedBodyEquiv_apply]
  let input := ContextObject.ofList A.substitution.toClone scope
  let extension := extendScope A scope f.unop
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
      (extendScope_snd A scope f.unop)
  rw [sndLaw, extendScope_fst] at pointwise
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

/-- Contextual bodies under any binder list, reindexed by extending the
ambient substitution under precisely that list. -/
def scopedBodies (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (result : S.Srt) : Base A ⥤ Type u where
  obj X := A.substitution.Carrier (scope ++ X.unop.context) result
  map f := TypeCat.ofHom (fun body => A.substitution.toClone.substitute body
    (extendScope A scope f.unop))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro body
    change A.substitution.toClone.substitute body
      (extendScope A scope (𝟙 X.unop)) = body
    rw [extendScope_id]
    exact A.substitution.toClone.substitute_projects body
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro body
    change A.substitution.toClone.substitute body
        (extendScope A scope (g.unop ≫ f.unop)) =
      A.substitution.toClone.substitute
        (A.substitution.toClone.substitute body
          (extendScope A scope f.unop))
        (extendScope A scope g.unop)
    rw [extendScope_comp]
    exact (A.substitution.toClone.substitute_assoc body
      (extendScope A scope f.unop)
      (extendScope A scope g.unop)).symm

/-- Arbitrary binder contexts, not just one variable, are represented by
the actual presheaf exponential. -/
def scopedBodiesIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (result : S.Srt) :
    ((binders A scope).functorHom (programs A result)) ≅
      scopedBodies A scope result := by
  refine NatIso.ofComponents
    (fun context => (scopedBodyEquiv A context.unop scope result).toIso) ?_
  intro first last f
  apply ConcreteCategory.hom_ext
  intro function
  exact scopedBodyEquiv_reindex A scope result f function

/-- A clone interpretation preserves the precise extension of an ambient
substitution past an ordered binder context. -/
theorem map_extendScope {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (scope : Ctx S)
    {first last : CloneContext A} (f : first ⟶ last) :
    h.toCloneTranslation.contextFunctor.map (extendScope A scope f) =
      extendScope B scope (h.toCloneTranslation.contextFunctor.map f) := by
  unfold extendScope
  rw [h.toCloneTranslation.map_pair,
    h.toCloneTranslation.map_fstProjection]
  rw [Functor.map_comp,
    h.toCloneTranslation.map_sndProjection]
  rfl

/-- Interpreting a body through a binding-clone map commutes with every
ambient substitution, including the locally bound variables. -/
theorem map_scoped_substitute {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (scope : Ctx S)
    {first last : CloneContext A} (f : first ⟶ last)
    {result : S.Srt} (body : A.substitution.Carrier
      (scope ++ last.context) result) :
    h.raw.map (A.substitution.toClone.substitute body (extendScope A scope f)) =
      B.substitution.toClone.substitute (h.raw.map body)
        (extendScope B scope (h.toCloneTranslation.contextFunctor.map f)) := by
  have hsub := h.toCloneTranslation.map_substitute body (extendScope A scope f)
  change h.raw.map (A.substitution.toClone.substitute body
      (extendScope A scope f)) =
    B.substitution.toClone.substitute (h.raw.map body)
      (h.toCloneTranslation.contextFunctor.map (extendScope A scope f))
    at hsub
  rw [map_extendScope h scope f] at hsub
  exact hsub

/-- A model morphism induces a map of all contextual binder-body
presheaves. This is natural in substitutions, not merely pointwise in terms. -/
def mapScopedBodies {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (scope : Ctx S) (result : S.Srt) :
    scopedBodies A scope result ⟶
      h.toCloneTranslation.contextFunctor.op ⋙ scopedBodies B scope result where
  app X := TypeCat.ofHom fun body => h.raw.map body
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro body
    exact map_scoped_substitute h scope f.unop body

/-- The induced map of genuine presheaf function objects. The construction
uses the represented contextual body on both sides, so it retains the
authored substitution discipline rather than assuming that arbitrary
presheaf exponentials are preserved by base change. -/
def mapScopedFunctions {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (scope : Ctx S) (result : S.Srt) :
    ((binders A scope).functorHom (programs A result)) ⟶
      h.toCloneTranslation.contextFunctor.op ⋙
        ((binders B scope).functorHom (programs B result)) :=
  (scopedBodiesIso A scope result).hom ≫
    mapScopedBodies h scope result ≫
    Functor.whiskerLeft h.toCloneTranslation.contextFunctor.op
      (scopedBodiesIso B scope result).inv

/-- The induced function map is exactly the authored interpretation of its
body, at every context and for every ordered local binder list. -/
theorem mapScopedFunctions_body {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (scope : Ctx S) (result : S.Srt)
    (context : CloneContext A)
    (function : ((binders A scope).functorHom (programs A result)).obj
      (Opposite.op context)) :
    scopedBodyEquiv B
        (h.toCloneTranslation.contextFunctor.obj context) scope result
        ((mapScopedFunctions h scope result).app (Opposite.op context) function) =
      h.raw.map (scopedBodyEquiv A context scope result function) := by
  simp only [mapScopedFunctions, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  exact (scopedBodyEquiv B
    (h.toCloneTranslation.contextFunctor.obj context) scope result).apply_symm_apply _

/-- Identity interpretation fixes every contextual function, not only its
represented body. -/
theorem mapScopedFunctions_id (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (result : S.Srt) (context : CloneContext A)
    (function : ((binders A scope).functorHom (programs A result)).obj
      (Opposite.op context)) :
    ((mapScopedFunctions (FreeBindingClone.Hom.id A) scope result).app
      (Opposite.op context)) function = function := by
  apply (scopedBodyEquiv A context scope result).injective
  have body := mapScopedFunctions_body (FreeBindingClone.Hom.id A)
    scope result context function
  exact body

/-- Composition of interpretations acts by composition on whole-context
function bodies, including their ambient reindexing. -/
theorem mapScopedFunctions_comp
    {A B C : BindingCloneAlgebra.Algebra.{u} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C)
    (scope : Ctx S) (result : S.Srt) (context : CloneContext A)
    (function : ((binders A scope).functorHom (programs A result)).obj
      (Opposite.op context)) :
    ((mapScopedFunctions (FreeBindingClone.Hom.comp first second)
        scope result).app (Opposite.op context)) function =
      ((mapScopedFunctions second scope result).app
        (Opposite.op (first.toCloneTranslation.contextFunctor.obj context)))
        (((mapScopedFunctions first scope result).app
          (Opposite.op context)) function) := by
  apply (scopedBodyEquiv C
    ((FreeBindingClone.Hom.comp first second).toCloneTranslation.contextFunctor.obj
      context) scope result).injective
  have direct := mapScopedFunctions_body
    (FreeBindingClone.Hom.comp first second) scope result context function
  have middle := mapScopedFunctions_body first scope result context function
  have later := mapScopedFunctions_body second scope result
    (first.toCloneTranslation.contextFunctor.obj context)
    (((mapScopedFunctions first scope result).app
      (Opposite.op context)) function)
  exact direct.trans ((congrArg second.raw.map middle).symm.trans later.symm)

#print axioms scopedBodiesIso
#print axioms map_scoped_substitute
#print axioms mapScopedFunctions_id
#print axioms mapScopedFunctions_comp
#print axioms scopedBodyEquiv

end Mettapedia.OSLF.Binding.MultiBinderPresheaf
