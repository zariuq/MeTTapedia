import Mettapedia.OSLF.Syntax.CategoricalBindingEquationEquivalence

/-!
# Binding and equation classification over the quotient context category

The quotient of second-order contexts by an authored equation presentation
classifies models satisfying those equations, provided interpretations
preserve the stated context products, exponentials, and operators. The
equivalence covers natural maps, including noninvertible ones.

Operational firing events remain separate proof-relevant structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- A functor from equation-class contexts whose restriction has the
specified binding, product, exponential and operator interpretation. -/
structure QuotientStructuredFunctor (P : EquationPresentation S schema) where
  carrier : EquationContexts P ⥤ D
  preserving : Preserving (P.quotientFunctor ⋙ carrier)

instance (P : EquationPresentation S schema) :
    Category (QuotientStructuredFunctor (D := D) P) where
  Hom F G := F.carrier ⟶ G.carrier
  id F := 𝟙 F.carrier
  comp f g := f ≫ g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; exact Category.assoc _ _ _

/-- Restriction along the quotient; equation soundness is inherited from
the quotient's arrow equality. -/
def restrictStructured (P : EquationPresentation S schema) :
    QuotientStructuredFunctor (D := D) P ⥤ RespectingStructuredFunctor (D := D) P where
  obj F := {
    structured := ⟨P.quotientFunctor ⋙ F.carrier, F.preserving⟩
    respects := by
      intro X Y σ τ related
      exact congrArg F.carrier.map
        (_root_.CategoryTheory.Quotient.sound P.homRel related) }
  map τ := Functor.whiskerLeft P.quotientFunctor τ
  map_id := by intro; rfl
  map_comp := by intros; rfl

instance (P : EquationPresentation S schema) : (restrictStructured (D := D) P).Faithful where
  map_injective := by
    intro F G first second same
    exact _root_.CategoryTheory.Quotient.natTrans_ext first second same

instance (P : EquationPresentation S schema) : (restrictStructured (D := D) P).Full where
  map_surjective := by
    intro F G τ
    refine ⟨_root_.CategoryTheory.Quotient.natTransLift P.homRel τ, ?_⟩
    apply NatTrans.ext
    funext X
    rfl

instance (P : EquationPresentation S schema) : (restrictStructured (D := D) P).EssSurj where
  mem_essImage F := by
    let L : LawfulEquationInterpretation P D :=
      ⟨F.structured.carrier, F.respects⟩
    let E := SecondOrderContext.extend P D L
    have equality : P.quotientFunctor ⋙ E = F.structured.carrier :=
      congrArg LawfulEquationInterpretation.functor (SecondOrderContext.restrict_extend P D L)
    let Q : QuotientStructuredFunctor (D := D) P :=
      ⟨E, equality.symm ▸ F.structured.preserving⟩
    refine ⟨Q, ⟨?_⟩⟩
    exact {
      hom := (eqToIso equality).hom
      inv := (eqToIso equality).inv
      hom_inv_id := (eqToIso equality).hom_inv_id
      inv_hom_id := (eqToIso equality).inv_hom_id }

instance (P : EquationPresentation S schema) :
    (restrictStructured (D := D) P).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

noncomputable def quotientStructuredEquivalence (P : EquationPresentation S schema) :
    QuotientStructuredFunctor (D := D) P ≌ RespectingStructuredFunctor (D := D) P :=
  (restrictStructured (D := D) P).asEquivalence

/-- The relative classifying property of the equation-class second-order
context category, with its binding structure and all interpretation maps. -/
noncomputable def bindingEquationEquivalence (P : EquationPresentation S schema) :
    SatisfyingInterpretation (D := D) P ≌ QuotientStructuredFunctor (D := D) P :=
  (equationEquivalence (D := D) P).trans
    (quotientStructuredEquivalence (D := D) P).symm

end Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence.bindingEquationEquivalence
