import Mettapedia.OSLF.Syntax.LambdaFreePresheafEvents
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Binder-extended terms and the operational beta square

An intrinsic term with one additional bound variable varies naturally under
substitution of its ambient context. This supplies a general presheaf for a
single binding argument, independent of the lambda example. In the Chapter 7
lambda presentation, abstraction, application, and capture-avoiding body
application are natural maps. Beta is a natural factorization through the
least reduction subobject, not an equality of raw source terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualTermAbstraction

open CategoryTheory

variable {S : Signature}

/-- Transport a body while leaving its distinguished new binder untouched. -/
def mapBody {Γ Δ : Ctx S} (binder result : S.Srt)
    (sigma : Sub S Γ Δ) (body : Term S (binder :: Γ) result) :
    Term S (binder :: Δ) result :=
  bind (liftSub sigma [binder]) body

theorem mapBody_id {Γ : Ctx S} (binder result : S.Srt)
    (body : Term S (binder :: Γ) result) :
    mapBody binder result (fun _ v => Term.var v) body = body := by
  simp only [mapBody, liftSub_var, bind_id]

theorem mapBody_comp {Γ Δ Θ : Ctx S} (binder result : S.Srt)
    (sigma : Sub S Γ Δ) (tau : Sub S Δ Θ)
    (body : Term S (binder :: Γ) result) :
    mapBody binder result tau (mapBody binder result sigma body) =
      mapBody binder result (fun sort v => bind tau (sigma sort v)) body := by
  simp only [mapBody]
  rw [bind_comp, liftSub_comp]

/-- The single-binder body family is a genuine presheaf on the intrinsic
context/substitution category. -/
def boundTermPresheaf (S : Signature) (binder result : S.Srt) :
    (Syntactic.Ctxt S)ᵒᵖ ⥤ Type where
  obj X := Term S (binder :: X.unop.vars) result
  map f := TypeCat.ofHom (mapBody binder result f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro body
    exact mapBody_id binder result body
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro body
    exact (mapBody_comp binder result f.unop g.unop body).symm

end Mettapedia.OSLF.Binding.ContextualTermAbstraction

namespace Mettapedia.OSLF.Binding.LambdaPresheafOperations

open CategoryTheory
open Mettapedia.OSLF.Binding.ContextualTermAbstraction
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaReductionSubobject
open Mettapedia.OSLF.Binding.BinderLocalPremise

/-- Lambda bodies indexed by the ambient context, with one distinguished
bound program variable. -/
abbrev Bodies : Base ⥤ Type := boundTermPresheaf sig .term .term

/-- The authored abstraction constructor is natural under substitutions. -/
def abstraction : Bodies ⟶ Programs where
  app X := TypeCat.ofHom lamT
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro body
    exact (bind_lamT f.unop body).symm

/-- The authored application constructor is natural in both arguments. -/
def application : ProgramPairs ⟶ Programs where
  app X := TypeCat.ofHom (fun pair => appT pair.1 pair.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨funTerm, arg⟩
    exact (bind_appT f.unop funTerm arg).symm

/-- Evaluate a binding body at an argument by capture-avoiding substitution.
This is distinct from the authored `app` constructor. -/
def bodyAt : FunctorToTypes.prod Bodies Programs ⟶ Programs where
  app X := TypeCat.ofHom (fun pair => inst pair.1 pair.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨body, arg⟩
    exact (ContextualLinearSubstitution.bind_inst f.unop body arg).symm

/-- First construct the lambda application of the supplied body. -/
def betaRedex : FunctorToTypes.prod Bodies Programs ⟶ Programs :=
  FunctorToTypes.prod.lift
      (FunctorToTypes.prod.fst ≫ abstraction) FunctorToTypes.prod.snd ≫
    application

/-- Pair the independently defined redex and capture-avoiding contractum. -/
def betaPairs : FunctorToTypes.prod Bodies Programs ⟶ rootPairsPresheaf sig :=
  FunctorToTypes.prod.lift betaRedex bodyAt ≫ sortedPairsIso.inv

/-- Each body and argument supplies an actual beta step in the reduction
subobject, naturally over every simultaneous context substitution. -/
def betaWitness : FunctorToTypes.prod Bodies Programs ⟶
    reduction.toFunctor where
  app X := TypeCat.ofHom (fun pair =>
    ⟨(⟨Srt.term, appT (lamT pair.1) pair.2, inst pair.1 pair.2⟩ :
      rootPairs sig X.unop.vars), Step.beta pair.1 pair.2⟩)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨body, arg⟩
    apply Subtype.ext
    change (⟨Srt.term, appT (lamT (mapBody (S := sig) Srt.term Srt.term f.unop body))
        (bind f.unop arg),
        inst (mapBody (S := sig) Srt.term Srt.term f.unop body) (bind f.unop arg)⟩ :
          rootPairs sig Y.unop.vars) =
      ⟨Srt.term, bind f.unop (appT (lamT body) arg),
        bind f.unop (inst body arg)⟩
    exact congrArg
      (fun p : Term sig Y.unop.vars .term × Term sig Y.unop.vars .term =>
        (⟨Srt.term, p⟩ : rootPairs sig Y.unop.vars))
      (Prod.ext
        (by rfl)
        (ContextualLinearSubstitution.bind_inst f.unop body arg).symm)

/-- The operational beta witness factors the actual abstract/apply and
body-evaluation maps; the square commutes at every context. -/
theorem beta_square : betaWitness ≫ reduction.ι = betaPairs := by
  ext X pair
  rfl

/-- The same beta pair, now read in the categorical product of program
presheaves rather than the explicit sorted-pair representation. -/
noncomputable def betaCategoricalPairs :
    FunctorToTypes.prod Bodies Programs ⟶ Programs ⨯ Programs :=
  betaPairs ≫ productIso.inv

/-- Every source beta instance factors through the actual categorical
reduction subobject of the program product. -/
theorem beta_factors_reductionSubobject :
    reductionSubobject.Factors betaCategoricalPairs := by
  apply (Subobject.mk_factors_iff _ _).mpr
  refine ⟨betaWitness, ?_⟩
  change betaWitness ≫ (reduction.ι ≫ productIso.inv) = betaCategoricalPairs
  rw [← Category.assoc, beta_square]
  rfl

/-- At an open term, beta is a reduction rather than an equality of the two
raw syntax trees. The argument is the ambient variable and remains open. -/
theorem open_beta_not_raw_equality :
    betaRedex.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) ≠
    bodyAt.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) := by
  exact LambdaContextualRung.open_beta_changes_term

end Mettapedia.OSLF.Binding.LambdaPresheafOperations
