import Mettapedia.Languages.Agda.Structural.AdministrativeRootPreservation

/-!
# Preservation inside formed type codes

A type certificate consumes an actual formation tree. The term position of
El inherits typed term equality, while its finite Set annotation is inert.
Every step from a finite type parameter retains its level and exposes the
actual step of its term component.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Statics (RawTm RawTy RawContext TypeParameter)

structure TypeCertificate {n : Nat} (source target : RawTy n) where
  step : Step source target
  equality : ∀ (Γ : RawContext n), CoreDerivation (Statics.formed Γ source) →
    CoreDerivation (Statics.typeEqual Γ source target)

theorem el_injective {n : Nat} {s t : UnivSort (scope n)} {a b : RawTm n}
    (same : el s a = el t b) : s = t ∧ a = b := by
  cases same
  exact ⟨rfl, rfl⟩

noncomputable def elTerm {n : Nat} {first second : RawTm n}
    (certificate : TermCertificate first second) (sort : UnivSort (scope n)) :
    TypeCertificate (el sort first) (el sort second) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.el (.cons sort (.cons first .nil))) (.op Op.el (.cons sort (.cons second .nil)))
    apply CompatibleDerivations.Step.congr (R := Root) Op.el
    apply CompatibleDerivations.ArgsStep.tail
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ formed := by
    obtain ⟨⟨level, term⟩, boundary, typed⟩ := formed.formationView
    obtain ⟨rfl, rfl⟩ := el_injective boundary
    exact Derivation.core (.typeEquality Γ level first second)
      (consEvidence CoreDerivation (certificate.equality Γ (Statics.universeType n level).code typed)
        (noEvidence CoreDerivation))

theorem closedLevel_inert {n : Nat} (k : Nat) (target : Level (scope n)) :
    IsEmpty (Step (levelClosed k) target) := by
  constructor
  intro tree
  cases tree with
  | root occurrence => cases occurrence
  | congr op arguments => cases arguments

theorem finiteSet_inert {n : Nat} (k : Nat) (target : UnivSort (scope n)) :
    IsEmpty (Step (set (levelClosed k)) target) := by
  constructor
  intro tree
  cases tree with
  | root occurrence => cases occurrence
  | congr op arguments =>
      cases arguments with
      | head tail child => exact (closedLevel_inert k _).false child
      | tail head children => cases children

structure TypeCodeStepView {n : Nat} (A : TypeParameter n) (target : RawTy n) where
  next : RawTm n
  boundary : target = (TypeParameter.mk A.level next).code
  termStep : Step A.term next

def typeCodeStep {n : Nat} {A : TypeParameter n} {target : RawTy n}
    (step : Step A.code target) : TypeCodeStepView A target := by
  cases step with
  | root occurrence => cases occurrence
  | congr op arguments =>
      cases arguments with
      | head tail child => exact False.elim ((finiteSet_inert A.level _).false child)
      | tail head children =>
          cases children with
          | head tail child => exact ⟨_, rfl, child⟩
          | tail head children => cases children

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation
