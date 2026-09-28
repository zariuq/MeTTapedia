import Mettapedia.Languages.Agda.Adequacy.AdministrativePreservation
import Mettapedia.Languages.Agda.Structural.PresentationCorrespondence
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalPaths

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (RawTm RawTy RawContext)
open Structural.AdministrativeStatics

abbrev ComputationTree {n : Nat} {s : Srt} (source target : Term sig (scope n) s) :=
  IntrinsicScopedLocalPolynomial.Tree Authored.computationRules Authored.algebra
    ⟨scope n, s, source, target⟩

abbrev ComputationPath {n : Nat} {s : Srt} (source target : Term sig (scope n) s) :=
  IntrinsicScopedLocalPolynomial.DerivationPath Authored.computationRules Authored.algebra source target

noncomputable def treeTermEquality {n : Nat} {Γ : RawContext n} {source target : RawTm n} {A : RawTy n}
    (tree : ComputationTree source target) (typed : CoreDerivation (Statics.typed Γ source A)) :
    CoreDerivation (Statics.termEqual Γ source target A) := termEquality (treeToStep tree) typed

noncomputable def treeTermPreservation {n : Nat} {Γ : RawContext n} {source target : RawTm n} {A : RawTy n}
    (tree : ComputationTree source target) (typed : CoreDerivation (Statics.typed Γ source A)) :
    CoreDerivation (Statics.typed Γ target A) := (treeTermEquality tree typed).termEndpoints.right

noncomputable def treeTypeEquality {n : Nat} {Γ : RawContext n} {source target : RawTy n}
    (tree : ComputationTree source target) (formed : CoreDerivation (Statics.formed Γ source)) :
    CoreDerivation (Statics.typeEqual Γ source target) := typeEquality (treeToStep tree) formed

noncomputable def treeSpineEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {source target : Spine (scope n)} (tree : ComputationTree source target) (action : Action Γ A source B) :
    SpineEq Γ A source target B := spineEquality (treeToStep tree) action

noncomputable def pathTermEquality {n : Nat} {Γ : RawContext n} {source target : RawTm n} {A : RawTy n}
    (path : ComputationPath source target) (typed : CoreDerivation (Statics.typed Γ source A)) :
    CoreDerivation (Statics.termEqual Γ source target A) := by
  induction path with
  | nil =>
      exact Derivation.core (.reflexivity Γ source A)
        (consEvidence CoreDerivation typed (noEvidence CoreDerivation))
  | @cons middle last earlier edge first =>
      let second := treeTermEquality edge first.termEndpoints.right
      exact Derivation.core (.transitivity Γ source middle last A)
        (consEvidence CoreDerivation first (consEvidence CoreDerivation second (noEvidence CoreDerivation)))

noncomputable def pathTermPreservation {n : Nat} {Γ : RawContext n} {source target : RawTm n} {A : RawTy n}
    (path : ComputationPath source target) (typed : CoreDerivation (Statics.typed Γ source A)) :
    CoreDerivation (Statics.typed Γ target A) := (pathTermEquality path typed).termEndpoints.right

noncomputable def pathTypeEquality {n : Nat} {Γ : RawContext n} {source target : RawTy n}
    (path : ComputationPath source target) (formed : CoreDerivation (Statics.formed Γ source)) :
    CoreDerivation (Statics.typeEqual Γ source target) := by
  induction path with
  | nil => exact formed.typeReflexivity
  | cons earlier edge first =>
      exact first.typeTransitivity (treeTypeEquality edge first.typeEndpoints.right)

noncomputable def pathSpineEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {source target : Spine (scope n)} (path : ComputationPath source target)
    (action : Action Γ A source B) (input : CoreDerivation (Statics.formed Γ A)) :
    SpineEq Γ A source target B := by
  induction path with
  | nil => exact Derivation.spineRefl action
  | cons earlier edge first =>
      exact Derivation.spineTrans first (treeSpineEquality edge (first.endpoints input).right)

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation
