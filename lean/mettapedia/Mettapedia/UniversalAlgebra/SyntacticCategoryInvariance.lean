import Mathlib.CategoryTheory.Equivalence
import Mettapedia.UniversalAlgebra.SyntacticFiniteProducts

/-!
# Invariance of the equational syntactic category

Equation systems with the same generated consequence relation determine
equivalent finite-product syntactic categories.  The comparison is the
identity on finite contexts and on raw term tuples; only the quotient proof
changes.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open CategoryTheory

universe u

variable {S : Signature.{u}}

namespace SyntacticCategory

/-- Reinterpret a syntactic arrow under a consequence-equivalent equation
system. -/
def mapHom {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target)
    {input output : Nat} :
    Hom source input output → Hom target input output :=
  Quotient.lift
    (fun tuple => mk target tuple)
    (by
      intro left right sourceEquivalent
      apply (mk_eq_iff target _ _).mpr
      intro position
      exact (equivalent _).mp (sourceEquivalent position))

@[simp] theorem mapHom_mk {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target)
    {input output : Nat} (tuple : BoundedTermTuple S input output) :
    mapHom equivalent (mk source tuple) = mk target tuple := rfl

/-- Changing to an equivalent consequence quotient and back is the identity. -/
theorem mapHom_symm_mapHom {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target)
    {input output : Nat} (arrow : Hom source input output) :
    mapHom equivalent.symm (mapHom equivalent arrow) = arrow := by
  induction arrow using Quotient.inductionOn with
  | _ tuple => rfl

/-- Consequence equivalence induces an identity-on-syntax functor. -/
def changeSystemFunctor {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    SyntacticCategory source ⥤ SyntacticCategory target where
  obj context := object target (objectSize source context)
  map arrow := mapHom equivalent arrow
  map_id _context := rfl
  map_comp first second := by
    induction first using Quotient.inductionOn with
    | _ first =>
      induction second using Quotient.inductionOn with
      | _ second => rfl

/-- The identity-on-syntax comparison is faithful. -/
theorem changeSystemFunctor_faithful
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    (changeSystemFunctor equivalent).Faithful := by
  constructor
  intro input output first second mappedEqual
  change mapHom equivalent first = mapHom equivalent second at mappedEqual
  have returnedEqual := congrArg (mapHom equivalent.symm) mappedEqual
  rw [mapHom_symm_mapHom, mapHom_symm_mapHom] at returnedEqual
  exact returnedEqual

/-- The identity-on-syntax comparison is full. -/
theorem changeSystemFunctor_full
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    (changeSystemFunctor equivalent).Full := by
  constructor
  intro input output arrow
  refine ⟨mapHom equivalent.symm arrow, ?_⟩
  exact mapHom_symm_mapHom equivalent.symm arrow

/-- The identity-on-context comparison is essentially surjective. -/
theorem changeSystemFunctor_essSurj
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    (changeSystemFunctor equivalent).EssSurj := by
  constructor
  intro context
  refine ⟨object source (objectSize target context), ?_⟩
  exact ⟨Iso.refl _⟩

/-- The consequence comparison functor is an equivalence of categories. -/
theorem changeSystemFunctor_isEquivalence
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    (changeSystemFunctor equivalent).IsEquivalence where
  faithful := changeSystemFunctor_faithful equivalent
  full := changeSystemFunctor_full equivalent
  essSurj := changeSystemFunctor_essSurj equivalent

/-- Consequence-equivalent equation systems determine equivalent syntactic
categories. -/
noncomputable def equivalenceOfSameConsequences
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    SyntacticCategory source ≌ SyntacticCategory target := by
  letI : (changeSystemFunctor equivalent).IsEquivalence :=
    changeSystemFunctor_isEquivalence equivalent
  exact (changeSystemFunctor equivalent).asEquivalence

/-- The comparison functor preserves the chosen first projection exactly. -/
@[simp] theorem changeSystemFunctor_map_firstProjection
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target)
    (left right : Nat) :
    (changeSystemFunctor equivalent).map
      (firstProjection source left right) =
        firstProjection target left right := rfl

/-- The comparison functor preserves the chosen second projection exactly. -/
@[simp] theorem changeSystemFunctor_map_secondProjection
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target)
    (left right : Nat) :
    (changeSystemFunctor equivalent).map
      (secondProjection source left right) =
        secondProjection target left right := rfl

/-- The comparison functor preserves tuple pairing exactly. -/
theorem changeSystemFunctor_map_pair
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target)
    {input left right : Nat}
    (first : object source input ⟶ object source left)
    (second : object source input ⟶ object source right) :
    (changeSystemFunctor equivalent).map (pair source first second) =
      pair target
        ((changeSystemFunctor equivalent).map first)
        ((changeSystemFunctor equivalent).map second) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second => rfl

end SyntacticCategory

end Mettapedia.UniversalAlgebra
