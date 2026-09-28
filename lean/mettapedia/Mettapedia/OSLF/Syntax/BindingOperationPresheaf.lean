import Mettapedia.OSLF.Syntax.MultiBinderPresheaf

/-!
# Authored binding operators as natural transformations

For any binding-clone algebra, an operator with arbitrarily many arguments
and arbitrary binder lists acts on a presheaf of argument families. The
operator-substitution law is exactly the naturality square. This packages the
actual authored syntax operations in the same presheaf category that holds
programs and individual firing events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingOperationPresheaf

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables

universe u

variable {S : Signature}

/-- Substitution of an identity environment fixes every argument, including
arguments beneath any list of locally bound variables. -/
theorem substituteArgs_identity
    (A : BindingSubstitutionAlgebra.Algebra.{u} S) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S A.Carrier arity Γ),
      A.substituteArgs (fun _ v => A.injectVar v) args = args
  | _, _, .nil => rfl
  | _, _, .cons (bs := scope) head tail => by
      simp only [BindingSubstitutionAlgebra.Algebra.substituteArgs]
      rw [liftEnvironment_injectVar A scope, A.substitute_identity,
        substituteArgs_identity A tail]

/-- Successive substitutions of an operator's argument family compose
pointwise, with each argument's own binder context respected. -/
theorem substituteArgs_comp
    (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    {Γ Δ Θ : Ctx S}
    (first : Environment S A.Carrier Γ Δ)
    (second : Environment S A.Carrier Δ Θ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S A.Carrier arity Γ),
      A.substituteArgs second (A.substituteArgs first args) =
        A.substituteArgs
          (fun sort var => A.substitute second (first sort var)) args
  | _, .nil => rfl
  | _, .cons (bs := scope) head tail => by
      simp only [BindingSubstitutionAlgebra.Algebra.substituteArgs]
      congr 1
      · rw [A.substitute_comp]
        congr 1
        funext sort var
        exact substitute_liftEnvironment A second first scope var
      · exact substituteArgs_comp A first second tail

/-- Contextual argument tuples, reindexed by simultaneous substitution in
all ambient variables and lifted through each argument's binder list. -/
def arguments (A : BindingCloneAlgebra.Algebra.{u} S)
    (arity : List (List S.Srt × S.Srt)) : Base A ⥤ Type u where
  obj X := FamilyArgs S A.substitution.Carrier arity X.unop.context
  map f := TypeCat.ofHom (fun args =>
    A.substitution.substituteArgs
      (fromPositions _ f.unop) args)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro args
    have envEq :
        fromPositions X.unop.context (𝟙 X).unop =
          (fun _ v => A.substitution.injectVar v) := by
      funext sort var
      exact fromPositions_ofEnvironment
        (fun _ v => A.substitution.injectVar v) var
    change A.substitution.substituteArgs
        (fromPositions X.unop.context (𝟙 X).unop) args = args
    exact (congrArg (fun env => A.substitution.substituteArgs env args)
      envEq).trans (substituteArgs_identity A.substitution args)
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
    change A.substitution.substituteArgs
        (fromPositions _ (f ≫ g).unop) args =
      A.substitution.substituteArgs (fromPositions _ g.unop)
        (A.substitution.substituteArgs (fromPositions _ f.unop) args)
    exact (congrArg (fun env => A.substitution.substituteArgs env args)
      envEq).trans ((substituteArgs_comp A.substitution
      (fromPositions _ f.unop) (fromPositions _ g.unop) args).symm)

/-- Each authored operator is a natural transformation from its full
argument-family presheaf to the program presheaf of its result sort. -/
def operation (A : BindingCloneAlgebra.Algebra.{u} S)
    {sort : S.Srt} (operator : S.Op sort) :
    arguments A (S.arity operator) ⟶ semanticPrograms A sort where
  app X := TypeCat.ofHom (fun args => A.operation operator args)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro args
    exact (A.operation_substitute
      (fromPositions X.unop.context f.unop) operator args).symm

/-- A binding-clone interpretation commutes with substitution of every
operator argument, including the binder lift particular to that argument. -/
theorem map_substituteArgs
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    {Γ Δ : Ctx S} (env : Environment S A.substitution.Carrier Γ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S A.substitution.Carrier arity Γ),
      FamilyArgs.map h.raw.map
        (A.substitution.substituteArgs env args) =
      B.substitution.substituteArgs
        (fun sort var => h.raw.map (env sort var))
        (FamilyArgs.map h.raw.map args)
  | _, .nil => rfl
  | _, .cons (bs := scope) head tail => by
      simp only [BindingSubstitutionAlgebra.Algebra.substituteArgs,
        FamilyArgs.map]
      apply congrArg₂ FamilyArgs.cons
      · rw [h.map_substitute, liftEnvironment_map h env scope]
      · exact map_substituteArgs h env tail

/-- Interpretation of the full authored argument family is natural in
ambient substitution, including its ordered binder lists. -/
def mapArguments {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    (arity : List (List S.Srt × S.Srt)) :
    arguments A arity ⟶
      h.toCloneTranslation.contextFunctor.op ⋙ arguments B arity where
  app X := TypeCat.ofHom (FamilyArgs.map h.raw.map)
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
    change FamilyArgs.map h.raw.map
        (A.substitution.substituteArgs
          (fromPositions X.unop.context f.unop) args) =
      B.substitution.substituteArgs
        (fromPositions X.unop.context
          (h.toCloneTranslation.contextFunctor.op.map f).unop)
        (FamilyArgs.map h.raw.map args)
    exact (map_substituteArgs h
      (fromPositions X.unop.context f.unop) args).trans
        (congrArg (fun env => B.substitution.substituteArgs env
          (FamilyArgs.map h.raw.map args)) envEq.symm)

/-- Program values are natural under the same clone interpretation. -/
def mapPrograms {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (sort : S.Srt) :
    semanticPrograms A sort ⟶
      h.toCloneTranslation.contextFunctor.op ⋙ semanticPrograms B sort where
  app X := TypeCat.ofHom fun term => h.raw.map term
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro term
    exact h.toCloneTranslation.map_substitute term f.unop

/-- The natural transformations interpreting an authored operator commute
with every binding-clone model map, at each ambient context. -/
theorem operation_map
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    {sort : S.Srt} (operator : S.Op sort)
    (X : Base A)
    (args : (arguments A (S.arity operator)).obj X) :
    ((mapPrograms h sort).app X)
        (((operation A operator).app X) args) =
      ((operation B operator).app
        (h.toCloneTranslation.contextFunctor.op.obj X))
        (((mapArguments h (S.arity operator)).app X) args) :=
  h.raw.map_operation operator args

#print axioms substituteArgs_identity
#print axioms substituteArgs_comp
#print axioms operation
#print axioms mapArguments
#print axioms operation_map

end Mettapedia.OSLF.Binding.BindingOperationPresheaf
