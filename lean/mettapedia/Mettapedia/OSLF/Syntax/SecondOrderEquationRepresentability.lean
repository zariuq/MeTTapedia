import Mettapedia.OSLF.Syntax.SecondOrderAuthoredEquationPresentation

/-!
# Terms represented after an authored equation quotient

A contextual term remains a map to a one-metavariable object after equations
are imposed. The hom-set is exactly the term quotient by the authored
congruence. This makes the relevant represented-term interface explicit
before adding chosen function objects or operational events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)}

/-- Equation classes of terms at a fixed second-order context and variable
dependency list. -/
abbrev EquationTermClass (P : EquationPresentation S M)
    (X : Object S) (dependencies : Ctx S) (sort : S.Srt) : Type :=
  Quot (EqClosure (P.axioms X) (Γ := dependencies) (s := sort))

/-- Quotienting context maps to a single metavariable is exactly quotienting
the represented terms by the authored equation closure. -/
def equationTermsRepresented (P : EquationPresentation S M)
    (X : Object S) (dependencies : Ctx S) (sort : S.Srt) :
    ((P.quotientFunctor.obj X) ⟶
        (P.quotientFunctor.obj (single S dependencies sort))) ≃
      EquationTermClass P X dependencies sort where
  toFun morphism := Quot.liftOn morphism
    (fun arrow => Quot.mk _
      (termsRepresented S X dependencies sort arrow))
    (by
      intro first second related
      apply Quot.sound
      have same : P.homRel first second := by
        simpa only [HomRel.compClosure_eq_self P.homRel] using related
      exact same ⟨0, by change 0 < 1; omega⟩)
  invFun term := Quot.liftOn term
    (fun representative => Quot.mk _
      ((termsRepresented S X dependencies sort).symm representative))
    (by
      intro first second related
      apply _root_.CategoryTheory.Quotient.sound P.homRel
      intro index
      have indexZero : index = ⟨0, by simp [single]⟩ := by
        apply Fin.ext
        have bound := index.isLt
        change index.val < 1 at bound
        change index.val = 0
        omega
      subst index
      change EqClosure (P.axioms X) first second
      exact related)
  left_inv morphism := by
    induction morphism using Quot.ind with
    | _ arrow =>
        change Quot.mk _ ((termsRepresented S X dependencies sort).symm
          (termsRepresented S X dependencies sort arrow)) = Quot.mk _ arrow
        exact congrArg (fun arrow : X ⟶ single S dependencies sort =>
          P.quotientFunctor.map arrow)
          ((termsRepresented S X dependencies sort).symm_apply_apply arrow)
  right_inv term := by
    induction term using Quot.ind with
    | _ representative =>
        change Quot.mk _ (termsRepresented S X dependencies sort
          ((termsRepresented S X dependencies sort).symm representative)) =
          Quot.mk _ representative
        exact congrArg (Quot.mk (EqClosure (P.axioms X)))
          ((termsRepresented S X dependencies sort).apply_symm_apply representative)

/-- Second-order substitution acts on equation classes of terms. Its
well-definedness is the authored generator-stability theorem, so no choice of
representative enters the result. -/
def substituteTermClass (P : EquationPresentation S M)
    {X Y : Object S} (substitution : X ⟶ Y)
    {dependencies : Ctx S} {sort : S.Srt} :
    EquationTermClass P Y dependencies sort →
      EquationTermClass P X dependencies sort :=
  Quot.lift (fun term => Quot.mk _ (instInto substitution term))
    (by
      intro first second related
      apply Quot.sound
      exact instInto_eqClosure_generators (D := P.axioms X)
        substitution (P.generator_substitute substitution) related)

/-- The identity assignment leaves an equation class unchanged. -/
theorem substituteTermClass_id (P : EquationPresentation S M)
    (X : Object S) {dependencies : Ctx S} {sort : S.Srt}
    (term : EquationTermClass P X dependencies sort) :
    substituteTermClass P (𝟙 X) term = term := by
  induction term using Quot.ind with
  | _ representative =>
      change Quot.mk _ (instInto (𝟙 X) representative) =
        Quot.mk _ representative
      exact congrArg (Quot.mk (EqClosure (P.axioms X)))
        (instInto_metaVar_id representative)

/-- Two contextual substitutions compose on term classes in the same order
as they compose on the underlying intrinsically scoped terms. -/
theorem substituteTermClass_comp (P : EquationPresentation S M)
    {X Y Z : Object S} (first : X ⟶ Y) (second : Y ⟶ Z)
    {dependencies : Ctx S} {sort : S.Srt}
    (term : EquationTermClass P Z dependencies sort) :
    substituteTermClass P (first ≫ second) term =
      substituteTermClass P first (substituteTermClass P second term) := by
  induction term using Quot.ind with
  | _ representative =>
      change Quot.mk _ (instInto (first ≫ second) representative) =
        Quot.mk _ (instInto first (instInto second representative))
      exact congrArg (Quot.mk (EqClosure (P.axioms X)))
        (instInto_instInto second first representative).symm

/-- The represented-term equivalence intertwines categorical precomposition
with the explicit substitution action on equation classes. -/
theorem equationTermsRepresented_comp (P : EquationPresentation S M)
    {X Y : Object S} (substitution : X ⟶ Y)
    (dependencies : Ctx S) (sort : S.Srt)
    (term : Y ⟶ single S dependencies sort) :
    equationTermsRepresented P X dependencies sort
        (P.quotientFunctor.map substitution ≫
          P.quotientFunctor.map term) =
      substituteTermClass P substitution
        (equationTermsRepresented P Y dependencies sort
          (P.quotientFunctor.map term)) := by
  rfl

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.equationTermsRepresented
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.substituteTermClass_comp
