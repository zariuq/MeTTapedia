import Mettapedia.GSLT.LanguageDef.MultiSortedCloneTranslation
import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mettapedia.OSLF.Syntax.TermCloneCategoryComparison

/-!
# Authored binding equations as a finite-product context quotient

A morphism of binding clones induces a finite-product-preserving functor on
context categories. The quotient by authored equations is full and surjective
on context objects, but a nontrivial equation can make it nonfaithful. The
comparison is tied to actual terms, substitutions, and equation classes.

This is a finite-product base for the Chapter 7 classifying construction. It
neither adjoins all finite limits nor proves cartesian closure or initiality
among finite-limit/cartesian-closed models.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Mettapedia.OSLF.Binding

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra

universe u v

variable {S : Signature}

/-- Pointwise images commute with reading a positional environment as a typed
semantic environment. -/
theorem bindingHom_fromPositions
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (hom : FreeBindingClone.Hom A B) :
    ∀ (Γ : Ctx S) {Δ : Ctx S}
      (env : (i : Fin Γ.length) → A.substitution.Carrier Δ (Γ.get i))
      {sort : S.Srt} (typedVar : Var Γ sort),
      hom.raw.map (fromPositions Γ env sort typedVar) =
        fromPositions Γ (fun i => hom.raw.map (env i)) sort typedVar
  | _ :: _, _, _, _, .zero => rfl
  | _ :: Γ, _, env, _, .succ typedVar =>
      bindingHom_fromPositions hom Γ (fun i => env i.succ) typedVar

/-- A full binding-clone morphism induces a clone translation and hence a
functor between its context categories. -/
def FreeBindingClone.Hom.toCloneTranslation
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (hom : FreeBindingClone.Hom A B) :
    CloneTranslation A.substitution.toClone B.substitution.toClone where
  map := hom.raw.map
  map_project := by
    intro Γ index
    exact hom.raw.map_variable (varOfIdx Γ index)
  map_substitute := by
    intro Γ Δ sort term env
    change hom.raw.map (A.substitution.substitute
        (fromPositions Γ env) term) =
      B.substitution.substitute
        (fromPositions Γ (fun i => hom.raw.map (env i)))
        (hom.raw.map term)
    have mappedEnv :
        (fun s v => hom.raw.map (fromPositions Γ env s v)) =
          fromPositions Γ (fun i => hom.raw.map (env i)) := by
      funext s v
      exact bindingHom_fromPositions hom Γ env v
    have first := hom.map_substitute (fromPositions Γ env) term
    have second :=
      congrArg
        (fun environment => B.substitution.substitute environment
          (hom.raw.map term)) mappedEnv
    exact first.trans second

end Mettapedia.OSLF.Binding

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

variable {S : Signature} {M : List (MetaArity S)}

/-- The semantic term clone and the existing syntactic term clone have the
same operations, variables, and substitution, propositionally rather than by
an unproved identification of records. -/
def semanticTermsToTermClone (S : Signature) :
    CloneTranslation ((BindingCloneAlgebra.terms S).substitution.toClone)
      (termClone S) where
  map := id
  map_project := by intros; rfl
  map_substitute := by
    intro Γ Δ sort term env
    exact BindingSubstitutionAlgebra.terms_substitution_eq_termClone term env

def termCloneToSemanticTerms (S : Signature) :
    CloneTranslation (termClone S)
      ((BindingCloneAlgebra.terms S).substitution.toClone) where
  map := id
  map_project := by intros; rfl
  map_substitute := by
    intro Γ Δ sort term env
    exact (BindingSubstitutionAlgebra.terms_substitution_eq_termClone term env).symm

/-- Equations induce an actual functor between the two corresponding
context categories, via the already-proved binding-clone projection. -/
noncomputable def quotientContextFunctor (E : List (EqAxiom S M)) :
    ContextObject ((BindingCloneAlgebra.terms S).substitution.toClone) ⥤
      ContextObject ((BindingEquationQuotientModel.algebra E).substitution.toClone) :=
  (BindingEquationQuotientModel.projection E).toCloneTranslation.contextFunctor

theorem quotientContextFunctor_preservesFiniteProducts
    (E : List (EqAxiom S M)) :
    CategoryTheory.Limits.PreservesFiniteProducts
      (quotientContextFunctor E) :=
  (BindingEquationQuotientModel.projection E).toCloneTranslation.preservesFiniteProducts

/-- At a one-output context, the quotient functor sends an authored term to
its actual equation class. -/
theorem quotientContextFunctor_operation
    (E : List (EqAxiom S M)) {Γ : Ctx S} {sort : S.Srt}
    (term : Term S Γ sort) :
    (quotientContextFunctor E).map
      (((BindingCloneAlgebra.terms S).substitution.toClone).operationAsSingletonMorphism term) =
      ((BindingEquationQuotientModel.algebra E).substitution.toClone).operationAsSingletonMorphism
        (Quotient.mk _ term) := by
  funext i
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
  rfl

/-- Every quotient substitution arrow has a raw precursor, coordinate by
coordinate. This is fullness, not faithfulness. -/
instance quotientContextFunctor_full (E : List (EqAxiom S M)) :
    (quotientContextFunctor E).Full where
  map_surjective := by
    intro source target env
    refine ⟨fun i => Quotient.out (env i), ?_⟩
    funext i
    exact Quotient.out_eq (env i)

/-- The equation quotient changes arrows but retains every ordered context. -/
theorem quotientContextFunctor_obj_surjective (E : List (EqAxiom S M)) :
    Function.Surjective (quotientContextFunctor E).obj := by
  intro target
  cases target with
  | mk context marker =>
      refine ⟨ContextObject.ofList _ context, ?_⟩
      cases marker
      rfl

instance quotientContextFunctor_essSurj (E : List (EqAxiom S M)) :
    (quotientContextFunctor E).EssSurj :=
  Functor.essSurj_of_surj (quotientContextFunctor_obj_surjective E)

end Mettapedia.OSLF.Binding

namespace Mettapedia.OSLF.Binding.QuotientContextControls

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.Duplication

private abbrev rawClone :=
  (BindingCloneAlgebra.terms dsig).substitution.toClone
private noncomputable abbrev quotientClone :=
  (BindingEquationQuotientModel.algebra dupE).substitution.toClone
private abbrev oneRaw : ContextObject rawClone :=
  ContextObject.ofList rawClone [Srt2.tm]

private def bareHole : oneRaw ⟶ oneRaw :=
  rawClone.operationAsSingletonMorphism hole1
private def duplicatedHole : oneRaw ⟶ oneRaw :=
  rawClone.operationAsSingletonMorphism hole2

private theorem holes_distinct : bareHole ≠ duplicatedHole := by
  intro equal
  have termsEqual := congrFun equal (0 : Fin 1)
  change hole1 = hole2 at termsEqual
  have countsEqual := congrArg (holeCount (S := dsig) (Γ := [])
    (c := Srt2.tm)) termsEqual
  rw [holeCount_hole1, holeCount_hole2] at countsEqual
  omega

private theorem holes_identified :
    (quotientContextFunctor dupE).map bareHole =
      (quotientContextFunctor dupE).map duplicatedHole := by
  funext index
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
  exact Quotient.sound hole1_eq_hole2

/-- The quotient functor is generally not faithful: a real authored equation
identifies two distinct raw substitution arrows. -/
theorem quotient_context_functor_not_faithful :
    ¬ (quotientContextFunctor dupE).Faithful := by
  intro faithful
  exact holes_distinct (faithful.map_injective holes_identified)

end Mettapedia.OSLF.Binding.QuotientContextControls

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

/-- The semantic term clone is equivalent, as a context category, to the
previously established syntactic term clone. -/
def termCloneToSemanticContextFunctor (S : Signature) :
    ContextObject (termClone S) ⥤
      ContextObject ((BindingCloneAlgebra.terms S).substitution.toClone) :=
  (termCloneToSemanticTerms S).contextFunctor

instance termCloneToSemanticContextFunctor_faithful (S : Signature) :
    (termCloneToSemanticContextFunctor S).Faithful where
  map_injective := by
    intro source target first second equality
    exact equality

instance termCloneToSemanticContextFunctor_full (S : Signature) :
    (termCloneToSemanticContextFunctor S).Full where
  map_surjective := by
    intro source target arrow
    exact ⟨arrow, rfl⟩

theorem termCloneToSemanticContextFunctor_obj_surjective (S : Signature) :
    Function.Surjective (termCloneToSemanticContextFunctor S).obj := by
  intro target
  cases target with
  | mk context marker =>
      refine ⟨ContextObject.ofList (termClone S) context, ?_⟩
      cases marker
      rfl

instance termCloneToSemanticContextFunctor_essSurj (S : Signature) :
    (termCloneToSemanticContextFunctor S).EssSurj :=
  Functor.essSurj_of_surj (termCloneToSemanticContextFunctor_obj_surjective S)

instance termCloneToSemanticContextFunctor_isEquivalence (S : Signature) :
    (termCloneToSemanticContextFunctor S).IsEquivalence where

noncomputable def termCloneSemanticContextEquivalence (S : Signature) :
    ContextObject (termClone S) ≌
      ContextObject ((BindingCloneAlgebra.terms S).substitution.toClone) :=
  (termCloneToSemanticContextFunctor S).asEquivalence

/-- The raw side of the equation-context quotient is equivalent to the
repository's intrinsic typed-substitution category. -/
noncomputable def semanticTermsSyntacticEquivalence (S : Signature) :
    ContextObject ((BindingCloneAlgebra.terms S).substitution.toClone) ≌
      Syntactic.Ctxt S :=
  (termCloneSemanticContextEquivalence S).symm.trans
    (termCloneContextEquivalence S)

end Mettapedia.OSLF.Binding

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

variable {S : Signature} {M : List (MetaArity S)}

/-- The chapter's raw typed-substitution category maps to the context
category of its authored equation presentation. -/
noncomputable def syntacticQuotientContextFunctor
    (E : List (EqAxiom S M)) :
    Syntactic.Ctxt S ⥤
      ContextObject ((BindingEquationQuotientModel.algebra E).substitution.toClone) :=
  (semanticTermsSyntacticEquivalence S).inverse ⋙ quotientContextFunctor E

theorem syntacticQuotientContextFunctor_preservesFiniteProducts
    (E : List (EqAxiom S M)) :
    CategoryTheory.Limits.PreservesFiniteProducts
      (syntacticQuotientContextFunctor E) := by
  letI : CategoryTheory.Limits.PreservesFiniteProducts
      (semanticTermsSyntacticEquivalence S).inverse := inferInstance
  letI : CategoryTheory.Limits.PreservesFiniteProducts
      (quotientContextFunctor E) :=
    quotientContextFunctor_preservesFiniteProducts E
  change CategoryTheory.Limits.PreservesFiniteProducts
    ((semanticTermsSyntacticEquivalence S).inverse ⋙ quotientContextFunctor E)
  exact inferInstance

theorem syntacticQuotientContextFunctor_full
    (E : List (EqAxiom S M)) :
    (syntacticQuotientContextFunctor E).Full := by
  letI : (quotientContextFunctor E).Full := quotientContextFunctor_full E
  change ((semanticTermsSyntacticEquivalence S).inverse ⋙
    quotientContextFunctor E).Full
  infer_instance

theorem syntacticQuotientContextFunctor_essSurj
    (E : List (EqAxiom S M)) :
    (syntacticQuotientContextFunctor E).EssSurj := by
  letI : (quotientContextFunctor E).EssSurj := quotientContextFunctor_essSurj E
  change ((semanticTermsSyntacticEquivalence S).inverse ⋙
    quotientContextFunctor E).EssSurj
  infer_instance

end Mettapedia.OSLF.Binding
