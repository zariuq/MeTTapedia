import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRelatorConversionChecking

/-!
# Executable substitution of native conversion evidence

All List, identity and List-relator root fields are transformed as scoped
terms. Their actual decoder commutes with this substitution. The general
finite-code transport therefore applies with its assumptions discharged,
retaining the input certificate's selected roots and composition structure.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

open Presentation StructuralConversionCode NativeIndexedFamilies

namespace NativeIndexedRootConversionCode

def substitute {n m : Nat} (σ : Sub Tower.Head n m) :
    Intrinsic.IotaEvidenceCode n → Intrinsic.IotaEvidenceCode m
  | .nil element motive nilCase consCase =>
      .nil (subst σ element) (subst σ motive) (subst σ nilCase) (subst σ consCase)
  | .cons element motive nilCase consCase head tail =>
      .cons (subst σ element) (subst σ motive) (subst σ nilCase) (subst σ consCase)
        (subst σ head) (subst σ tail)
  | .identity element point motive reflCase =>
      .identity (subst σ element) (subst σ point) (subst σ motive) (subst σ reflCase)

theorem substitute_ids {n : Nat} (code : Intrinsic.IotaEvidenceCode n) :
    substitute ids code = code := by cases code <;> simp only [substitute, subst_ids]

theorem substitute_comp {n m k : Nat} (σ : Sub Tower.Head n m) (τ : Sub Tower.Head m k)
    (code : Intrinsic.IotaEvidenceCode n) :
    substitute τ (substitute σ code) = substitute (subComp τ σ) code := by
  cases code <;> simp only [substitute, subst_subComp]

theorem decode_substitute {n m : Nat} (σ : Sub Tower.Head n m) (code : Intrinsic.IotaEvidenceCode n) :
    decode (substitute σ code) = mapEndpoints (subst σ) (decode code) := by
  cases code <;> rfl

end NativeIndexedRootConversionCode

namespace NativeRelatorRootConversionCode

def substitute {n m : Nat} (σ : Sub Tower.Head n m) : Code n → Code m
  | .indexed code => .indexed (NativeIndexedRootConversionCode.substitute σ code)
  | .relNil source target relation motive nilCase consCase =>
      .relNil (subst σ source) (subst σ target) (subst σ relation) (subst σ motive)
        (subst σ nilCase) (subst σ consCase)
  | .relCons source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence =>
      .relCons (subst σ source) (subst σ target) (subst σ relation) (subst σ motive)
        (subst σ nilCase) (subst σ consCase) (subst σ sourceHead) (subst σ targetHead)
        (subst σ sourceTail) (subst σ targetTail) (subst σ headEvidence) (subst σ tailEvidence)

theorem substitute_ids {n : Nat} (code : Code n) : substitute ids code = code := by
  cases code <;> simp only [substitute, NativeIndexedRootConversionCode.substitute_ids, subst_ids]

theorem substitute_comp {n m k : Nat} (σ : Sub Tower.Head n m) (τ : Sub Tower.Head m k)
    (code : Code n) : substitute τ (substitute σ code) = substitute (subComp τ σ) code := by
  cases code <;> simp only [substitute, NativeIndexedRootConversionCode.substitute_comp, subst_subComp]

theorem decode_substitute {n m : Nat} (σ : Sub Tower.Head n m) (code : Code n) :
    decode (substitute σ code) = mapEndpoints (subst σ) (decode code) := by
  cases code with
  | indexed code => exact NativeIndexedRootConversionCode.decode_substitute σ code
  | relNil => rfl
  | relCons => rfl

end NativeRelatorRootConversionCode

namespace NativeRelatorConversionChecking

def substitute {n m : Nat} (σ : Sub Tower.Head n m) (code : Code n) : Code m :=
  code.substitute NativeRelatorRootConversionCode.substitute σ

theorem substitute_ids {n : Nat} (code : Code n) : substitute ids code = code :=
  StructuralConversionCode.Code.substitute_ids _ NativeRelatorRootConversionCode.substitute_ids code

theorem substitute_comp {n m k : Nat} (σ : Sub Tower.Head n m) (τ : Sub Tower.Head m k)
    (code : Code n) : substitute τ (substitute σ code) = substitute (subComp τ σ) code :=
  StructuralConversionCode.Code.substitute_comp _ NativeRelatorRootConversionCode.substitute_comp σ τ code

/-- This explicitly transformed certificate passes the unchanged checker
at the substituted original endpoints, at every source and target arity. -/
theorem check_substitute {n m : Nat} (σ : Sub Tower.Head n m) (code : Code n)
    {left right : Tower.Tm n} (accepted : check code left right = true) :
    check (substitute σ code) (subst σ left) (subst σ right) = true :=
  StructuralConversionCode.Code.check_substitute NativeRelatorRootConversionCode.substitute
    Tower.HeadEq NativeRelatorRootConversionCode.decode
    NativeRelatorRootConversionCode.decode_substitute σ code accepted

/-- Renaming is the variable-image case of the same certificate action. -/
def rename {n m : Nat} (ρ : Ren n m) (code : Code n) : Code m :=
  substitute (renSub ρ) code

theorem rename_id {n : Nat} (code : Code n) : rename idRen code = code :=
  substitute_ids code

theorem rename_comp {n m k : Nat} (ρ : Ren m k) (ξ : Ren n m) (code : Code n) :
    rename ρ (rename ξ code) = rename (fun index => ρ (ξ index)) code :=
  substitute_comp (renSub ξ) (renSub ρ) code

theorem rename_substitute {n m k : Nat} (ρ : Ren m k) (σ : Sub Tower.Head n m)
    (code : Code n) :
    rename ρ (substitute σ code) = substitute (fun i => Presentation.rename ρ (σ i)) code := by
  change substitute (renSub ρ) (substitute σ code) = _
  rw [substitute_comp]
  congr 1
  funext index
  exact subst_renSub ρ (σ index)

theorem substitute_rename {n m k : Nat} (σ : Sub Tower.Head m k) (ρ : Ren n m)
    (code : Code n) :
    substitute σ (rename ρ code) = substitute (fun i => σ (ρ i)) code :=
  substitute_comp (renSub ρ) σ code

theorem check_rename {n m : Nat} (ρ : Ren n m) (code : Code n)
    {left right : Tower.Tm n} (accepted : check code left right = true) :
    check (rename ρ code) (Presentation.rename ρ left) (Presentation.rename ρ right) = true := by
  simpa only [rename, subst_renSub] using check_substitute (renSub ρ) code accepted

namespace SubstitutionControls

def nonVariable : Sub Tower.Head 1 2 := fun _ => .app (.lam (.var 0)) (.var 1)

/-- Substitution enters the retained lambda with the right binder lift;
the supplied free term is itself a constructor tree containing a binder. -/
theorem nonvariable_beneath_binder_checked :
    check (substitute nonVariable (.single Examples.beneathBinder))
      (subst nonVariable Examples.beneathBinderSource)
      (.lam (.app (.lam (.var 0)) (.var 2))) = true := by
  decide +kernel

theorem captured_result_rejected :
    check (substitute nonVariable (.single Examples.beneathBinder))
      (subst nonVariable Examples.beneathBinderSource)
      (.lam (.app (.lam (.var 0)) (.var 0))) = false := by
  decide +kernel

/-- A real relator-cons root, under a lambda, transports all repeated
parameters and its recursive-result expression together. -/
theorem relator_beneath_binder_substitutes (σ : Sub Tower.Head 11 2) :
    check (substitute σ (.single (.congLam Examples.relConsStep)))
      (subst σ (.lam IntrinsicRelator.consIotaLeft))
      (subst σ (.lam IntrinsicRelator.consIotaRight)) = true :=
  check_substitute σ _ Examples.relational_root_beneath_binder_checked

def mismatchedJoin : Code 2 := .trans (.refl (.var 0)) (.refl (.var 1))
def identify : Sub Tower.Head 2 1 := fun _ => .var 0

/-- A failed certificate join can become valid when its distinct middle
terms are identified. Rejection preservation would be a false general law. -/
theorem substitution_can_repair_join :
    check mismatchedJoin (.var 0) (.var 1) = false ∧
      check (substitute identify mismatchedJoin) (.var 0) (.var 0) = true := by
  decide +kernel

end SubstitutionControls

#print axioms substitute_ids
#print axioms substitute_comp
#print axioms check_substitute
#print axioms rename_id
#print axioms rename_comp
#print axioms rename_substitute
#print axioms substitute_rename
#print axioms check_rename
#print axioms SubstitutionControls.nonvariable_beneath_binder_checked
#print axioms SubstitutionControls.captured_result_rejected
#print axioms SubstitutionControls.relator_beneath_binder_substitutes
#print axioms SubstitutionControls.substitution_can_repair_join

end NativeRelatorConversionChecking
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
