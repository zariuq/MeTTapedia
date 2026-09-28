import Mettapedia.Languages.Agda.Structural.AdministrativeRenaming
import Mettapedia.Languages.Agda.Structural.SpineTypeViews
import Mettapedia.Languages.Agda.Structural.StaticTypeEquivalence

/-!
# Finite type boundaries in the administrative presentation

The extension supplies typed term equalities and conditional spine equalities, but introduces no
new formation or type-equality rule. Its finite-annotation views are therefore
recovered by the same canonical rule algebra. The views retain actual combined
typing and equality trees, including administrative terms in their premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext TypeParameter)

def TypeViews (D : Judgment → Type) : Judgment → Type
  | .core j => Statics.TypeViews (fun j => D (.core j)) j
  | .spineAction _ _ _ _ | .spineEquality _ _ _ _ _ => PUnit

def ofPriorTypeViews {D : Judgment → Type} {j : SpineStatics.CombinedJudgment}
    (value : SpineStatics.TypeViews (fun j => D (mapPrior j)) j) : TypeViews D (mapPrior j) := by
  cases j <;> exact value

def typeViewRule {D : Judgment → Type} {j : Judgment} (shape : RuleShape j)
    (children : Evidence D (premises shape)) : TypeViews D j := by
  cases shape with
  | prior shape => exact ofPriorTypeViews (SpineStatics.typeViewRule shape (priorPremiseEvidence children))
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence | emptyElimination
    | nestedElimination => exact ⟨⟩

noncomputable def Derivation.typeViews {j : Judgment} (tree : Derivation j) : TypeViews Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => TypeViews Derivation j)
    (fun _ _ shape children _ih => typeViewRule shape children) () j tree

noncomputable def CoreDerivation.formationView {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : CoreDerivation (Statics.formed Γ A)) : Statics.FormationView CoreDerivation Γ A :=
  Derivation.typeViews tree

noncomputable def CoreDerivation.typeEqualityView {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : CoreDerivation (Statics.typeEqual Γ A B)) : Statics.TypeEqualityView CoreDerivation Γ A B :=
  Derivation.typeViews tree

theorem CoreDerivation.typeEquality_levels {n : Nat} {Γ : RawContext n} {A B : TypeParameter n}
    (tree : CoreDerivation (Statics.typeEqual Γ A.code B.code)) : A.level = B.level :=
  tree.typeEqualityView.levels_equal

noncomputable def CoreDerivation.typeReflexivity {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : CoreDerivation (Statics.formed Γ A)) : CoreDerivation (Statics.typeEqual Γ A A) :=
  tree.formationView.reflexivity (canonicalAlgebra (IndexedPolynomial.Algebra.initial presentation.polynomial))

noncomputable def CoreDerivation.typeSymmetry {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : CoreDerivation (Statics.typeEqual Γ A B)) : CoreDerivation (Statics.typeEqual Γ B A) :=
  tree.typeEqualityView.symmetry (canonicalAlgebra (IndexedPolynomial.Algebra.initial presentation.polynomial))

noncomputable def CoreDerivation.typeTransitivity {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    (first : CoreDerivation (Statics.typeEqual Γ A B)) (second : CoreDerivation (Statics.typeEqual Γ B C)) :
    CoreDerivation (Statics.typeEqual Γ A C) :=
  first.typeEqualityView.transitivity (canonicalAlgebra (IndexedPolynomial.Algebra.initial presentation.polynomial))
    second.typeEqualityView

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
