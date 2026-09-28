import Mettapedia.Languages.Agda.Structural.StaticTypeViews

/-!
# Derived equivalence operations on structural type equality

The operations inspect the actual finite-annotation boundary and build ordinary
term-equality rules at its universe. Transitivity reconciles the intermediate
type code before joining the ordered equality children. No equality rule is
added to the presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

variable {D : Judgment → Type}

def FormationView.reflexivity
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {n : Nat} {Γ : RawContext n} {A : RawTy n} (view : FormationView D Γ A) :
    D (typeEqual Γ A A) := by
  let equal := algebra.act () _ ⟨.reflexivity Γ view.parameter.term
    (universeType n view.parameter.level).code, consEvidence D view.typing (noEvidence D)⟩
  let result := algebra.act () _ ⟨.typeEquality Γ view.parameter.level view.parameter.term view.parameter.term,
    consEvidence D equal (noEvidence D)⟩
  exact (congrArg (fun A => D (typeEqual Γ A A)) view.boundary).mpr result

def TypeEqualityView.symmetry
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {n : Nat} {Γ : RawContext n} {A B : RawTy n} (view : TypeEqualityView D Γ A B) :
    D (typeEqual Γ B A) := by
  let equal := algebra.act () _ ⟨.symmetry Γ view.first view.second (universeType n view.level).code,
    consEvidence D view.terms (noEvidence D)⟩
  let result := algebra.act () _ ⟨.typeEquality Γ view.level view.second view.first,
    consEvidence D equal (noEvidence D)⟩
  exact (congrArg₂ (fun B A => D (typeEqual Γ B A)) view.rightBoundary view.leftBoundary).mpr result

def TypeEqualityView.transitivity
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    (first : TypeEqualityView D Γ A B) (second : TypeEqualityView D Γ B C) :
    D (typeEqual Γ A C) := by
  have middle := TypeParameter.code_injective (first.rightBoundary.symm.trans second.leftBoundary)
  have levels : first.level = second.level := congrArg TypeParameter.level middle
  have terms : first.second = second.first := congrArg TypeParameter.term middle
  have right : D (termEqual Γ first.second second.second (universeType n first.level).code) :=
    (congrArg₂ (fun level term => D (termEqual Γ term second.second (universeType n level).code))
      levels terms).mpr second.terms
  let equal := algebra.act () _ ⟨.transitivity Γ first.first first.second second.second
    (universeType n first.level).code,
    consEvidence D first.terms (consEvidence D right (noEvidence D))⟩
  let result := algebra.act () _ ⟨.typeEquality Γ first.level first.first second.second,
    consEvidence D equal (noEvidence D)⟩
  have endBoundary : C = (TypeParameter.mk first.level second.second).code :=
    second.rightBoundary.trans (congrArg (fun k => (TypeParameter.mk k second.second).code) levels.symm)
  exact (congrArg₂ (fun A C => D (typeEqual Γ A C)) first.leftBoundary endBoundary).mpr result

noncomputable def Derivation.typeReflexivity {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : Derivation (formed Γ A)) : Derivation (typeEqual Γ A A) :=
  tree.formationView.reflexivity (IndexedPolynomial.Algebra.initial presentation.polynomial)

noncomputable def Derivation.typeSymmetry {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : Derivation (typeEqual Γ A B)) : Derivation (typeEqual Γ B A) :=
  tree.typeEqualityView.symmetry (IndexedPolynomial.Algebra.initial presentation.polynomial)

noncomputable def Derivation.typeTransitivity {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    (first : Derivation (typeEqual Γ A B)) (second : Derivation (typeEqual Γ B C)) :
    Derivation (typeEqual Γ A C) :=
  first.typeEqualityView.transitivity (IndexedPolynomial.Algebra.initial presentation.polynomial)
    second.typeEqualityView

end Mettapedia.Languages.Agda.Structural.Statics
