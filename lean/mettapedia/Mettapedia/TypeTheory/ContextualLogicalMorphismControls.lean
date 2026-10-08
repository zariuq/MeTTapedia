import Mettapedia.TypeTheory.ContextualSumMorphism
import Mettapedia.TypeTheory.ContextualMarkedTypes
import Mettapedia.TypeTheory.ContextualSumComprehensionControls

/-!
# Logical morphism controls with varying families

Decoding removes a supplied presentation mark while retaining actual
dependent values. The generic full-motive law is exercised on a varying
domain, a varying second-component type, and a motive depending on both
witnesses. A negative pair constructor records why formation preservation
cannot replace term-constructor preservation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLogicalMorphismControls

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualSumComprehension
open ContextualComprehensionMorphism ContextualLogicalMorphism
open ContextualMarkedTypes
open ContextualSumComprehensionControls (varyingDomain varyingCodomain varyingMotive varyingBody familySums)

abbrev familyModel := familiesCwfWithTerminal.{0}
abbrev sourceModel := withTerminal familyModel
abbrev forget := decoder familyModel

def markedSums : StableSums sourceModel.toCwf where
  operations := sums Families.sums
  beta := ⟨fun _ _ => rfl, fun _ _ => HEq.rfl⟩
  eta := by
    intro Γ A B p
    funext γ
    change Sigma.mk (p γ).1 (p γ).2 = p γ
    cases p γ
    rfl
  substitution := by
    refine ⟨?_, ?_, ?_⟩
    · intro Γ Δ σ A B
      rfl
    · intro Γ Δ σ A B a b b' bodies
      cases eq_of_heq bodies
      rfl
    · intro Γ Δ σ A B p p' values
      cases eq_of_heq values
      exact ⟨HEq.rfl, HEq.rfl⟩

def A : sourceModel.toCwf.Ty Nat := ⟨varyingDomain, true⟩
def B : sourceModel.toCwf.Ty (sourceModel.toCwf.ext Nat A) := ⟨varyingCodomain, false⟩
def M : sourceModel.toCwf.Ty (sumContext markedSums A B) := ⟨varyingMotive, true⟩
def branch : sourceModel.toCwf.Tm (tupleContext A B)
    (sourceModel.toCwf.tySub M (pack markedSums A B)) := varyingBody

theorem local_products_preserved :
    PiPreservation forget (products Families.products) Families.products :=
  products_preserved familyModel Families.products

theorem local_sums_preserved :
    SigmaPreservation forget markedSums.operations familySums.operations :=
  sums_preserved familyModel Families.sums

def functionBody : sourceModel.toCwf.Tm (sourceModel.toCwf.ext Nat A) B :=
  fun point => ⟨point.2.val, by omega⟩

def suppliedFunction : sourceModel.toCwf.Tm Nat ((products Families.products).pi A B) :=
  (products Families.products).lam functionBody

def suppliedArgument : sourceModel.toCwf.Tm Nat A := fun n => ⟨n, Nat.lt_succ_self n⟩

theorem dependent_application_preserved :
    forget.toFamilyMorphism.mapTerm
      ((products Families.products).app suppliedFunction suppliedArgument) =
        Families.products.app (Families.products.lam functionBody) suppliedArgument :=
  eq_of_heq (local_products_preserved.application rfl HEq.rfl HEq.rfl
    suppliedFunction (Families.products.lam functionBody) suppliedArgument suppliedArgument HEq.rfl HEq.rfl)

theorem dependent_application_readout (n : Nat) :
    (forget.toFamilyMorphism.mapTerm
      ((products Families.products).app suppliedFunction suppliedArgument) n).val = n := by
  rw [dependent_application_preserved]
  rfl

theorem actual_application_substitution :
    HEq (forget.toFamilyMorphism.mapTerm (sourceModel.toCwf.tmSub
      ((products Families.products).app suppliedFunction suppliedArgument)
        ContextualSumComprehensionControls.shift))
      (familyModel.toCwf.tmSub
        (forget.toFamilyMorphism.mapTerm ((products Families.products).app suppliedFunction suppliedArgument))
        ContextualSumComprehensionControls.shift) :=
  forget.toFamilyMorphism.mapTerm_substitution _ _

theorem shifted_application_readout (n : Nat) :
    (forget.toFamilyMorphism.mapTerm (sourceModel.toCwf.tmSub
      ((products Families.products).app suppliedFunction suppliedArgument)
        ContextualSumComprehensionControls.shift) n).val = n + 2 := by
  rw [eq_of_heq actual_application_substitution]
  exact dependent_application_readout (n + 2)

theorem omitting_actual_substitution_changes_value (n : Nat) :
    (forget.toFamilyMorphism.mapTerm (sourceModel.toCwf.tmSub
      ((products Families.products).app suppliedFunction suppliedArgument)
        ContextualSumComprehensionControls.shift) n).val ≠
      (forget.toFamilyMorphism.mapTerm
        ((products Families.products).app suppliedFunction suppliedArgument) n).val := by
  rw [shifted_application_readout, dependent_application_readout]
  omega

theorem actual_pack_square :
    forget.toFamilyMorphism.base.map (pack markedSums A B) =
      pack familySums varyingDomain varyingCodomain := by
  exact eq_of_heq (pack_heq forget markedSums familySums local_sums_preserved
    rfl HEq.rfl HEq.rfl)

theorem full_motive_preserved :
    forget.toFamilyMorphism.mapTerm (eliminate markedSums A B M branch) =
      eliminate familySums varyingDomain varyingCodomain varyingMotive varyingBody :=
  eq_of_heq (elimination_heq forget markedSums familySums local_sums_preserved
    rfl HEq.rfl HEq.rfl M varyingMotive HEq.rfl branch varyingBody HEq.rfl)

theorem exact_second_witness_retained
    (point : sumContext familySums varyingDomain varyingCodomain) :
    (forget.toFamilyMorphism.mapTerm (eliminate markedSums A B M branch) point).val = point.2.2.val := by
  rw [full_motive_preserved]
  exact ContextualSumComprehensionControls.varying_elimination_readout point

/-- Both marks are real source type values; decoding has a proper collision. -/
theorem presentation_collision :
    (⟨varyingDomain, true⟩ : sourceModel.toCwf.Ty Nat) ≠ ⟨varyingDomain, false⟩ ∧
      forget.toFamilyMorphism.mapType (⟨varyingDomain, true⟩ : sourceModel.toCwf.Ty Nat) =
        forget.toFamilyMorphism.mapType (⟨varyingDomain, false⟩ : sourceModel.toCwf.Ty Nat) := by
  refine ⟨?_, rfl⟩
  intro same
  exact Bool.noConfusion (congrArg Prod.snd same)

theorem supplied_marks_survive_substitution :
    (sourceModel.toCwf.tySub A ContextualSumComprehensionControls.shift).2 = true ∧
      (sourceModel.toCwf.tySub B (TypeOver.extensionSubstitution
        (C := sourceModel.toCwf) ContextualSumComprehensionControls.shift A)).2 = false := ⟨rfl, rfl⟩

theorem nonidentity_lift_preserved :
    forget.toFamilyMorphism.base.map
      (TypeOver.extensionSubstitution (C := sourceModel.toCwf)
        ContextualSumComprehensionControls.shift A) =
      TypeOver.extensionSubstitution (C := familyModel.toCwf)
        ContextualSumComprehensionControls.shift varyingDomain :=
  eq_of_heq (lifted_substitution_heq forget rfl rfl HEq.rfl _ _ HEq.rfl)

def pairWithTrue : SigmaOperations familiesCwf.{0} where
  sigma := ContextualSumComprehensionControls.hiddenOperations.sigma
  pair a b γ := (⟨a γ, b γ⟩, true)
  fst := ContextualSumComprehensionControls.hiddenOperations.fst
  snd := ContextualSumComprehensionControls.hiddenOperations.snd

theorem negative_same_formation {Γ : familiesCwf.Ctx}
    (domain : familiesCwf.Ty Γ) (codomain : familiesCwf.Ty (familiesCwf.ext Γ domain)) :
    pairWithTrue.sigma domain codomain =
      ContextualSumComprehensionControls.hiddenOperations.sigma domain codomain := rfl

/-- The same formed sum type does not determine the actual pair constructor. -/
theorem formation_alone_cannot_preserve_pair :
    ¬ SigmaPreservation (StrictCwfMorphism.identity familyModel)
      pairWithTrue ContextualSumComprehensionControls.hiddenOperations := by
  intro preservation
  let domain : familiesCwf.Ty PUnit := fun _ => PUnit
  let codomain : familiesCwf.Ty (familiesCwf.ext PUnit domain) := fun _ => PUnit
  let first : familiesCwf.Tm PUnit domain := fun _ => PUnit.unit
  let second : familiesCwf.Tm PUnit (familiesCwf.tySub codomain
      (ContextualProductComparison.selfExtend familiesCwf first)) := fun _ => PUnit.unit
  have pairs := preservation.pairing rfl (A := domain) HEq.rfl (B := codomain) HEq.rfl
    first first second second HEq.rfl HEq.rfl
  have marks := congrArg (fun pair => (pair PUnit.unit).2) (eq_of_heq pairs)
  exact Bool.noConfusion marks

end Mettapedia.TypeTheory.ContextualLogicalMorphismControls
