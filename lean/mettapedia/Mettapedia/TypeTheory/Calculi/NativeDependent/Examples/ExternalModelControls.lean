import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalDeclaredModel
import Mettapedia.TypeTheory.ContextualSumComprehensionControls
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

/-!
# Supplied generated certificates in a varying dependent model

The primitive fibre is indexed by an actual Boolean function. The full-pair
motive depends on that function and its supplied second witness. Generated
certificate extraction recovers the supplied branch exactly. Incompatible
annotations fail checking instead of silently coercing a witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelControls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualPiEta

abbrev familyModel := familiesCwfWithTerminal.{0}
abbrev products := Families.products.{0}
abbrev sums := Mettapedia.TypeTheory.ContextualSumComprehensionControls.familySums.{0}

theorem products_eta : PiEta products Families.products_substitution.1 := by
  intro Γ A B function
  have read : genericSection products Families.products_substitution.1 function =
      (fun point : (familiesCwf.{0}).ext Γ A => function point.1 point.2) :=
    eq_of_heq (genericSection_heq products Families.products_substitution.1 function)
  rw [read]
  rfl

abbrev scalar : familyModel.toCwf.Ty familyModel.empty := fun _ => Bool

def functionSize (function : Bool → Bool) : Nat := if function false then 1 else 0

abbrev declarations : DeclaredModel.Declarations (C := familyModel) products sums where
  scalar := scalar
  fibre := fun (point : Σ _ : PUnit, Bool → Bool) => Fin (functionSize point.2 + 1)
  motive := fun (point : Σ _ : PUnit, Σ function : Bool → Bool, Fin (functionSize function + 1)) =>
    Fin (functionSize point.2.1 + point.2.2.val + 1)
  branch := fun (point : Σ first : (Σ _ : PUnit, Bool → Bool), Fin (functionSize first.2 + 1)) =>
    ⟨point.2.val, by
      change point.2.val < functionSize point.1.2 + point.2.val + 1
      omega⟩

abbrev model := declarations.model
theorem realization : SignatureRealization model Controls.signature :=
  declarations.realization Families.products_substitution

def generated_header_certificates : HeaderFormation Controls.signature := Controls.headers

theorem generated_function_interpreted :
    Interprets model (.term .nil Controls.fullMotiveFunction (.pi (Controls.sum 0) (Controls.motive 0))) :=
  declarations.generated_full_motive_sound Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta

noncomputable def extractedBranch :=
  (Controls.fullBranchTyped Controls.emptyContext).termSection model realization
    Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta
    declarations.componentContext
    (familyModel.toCwf.tySub declarations.motive
      (pack sums (DeclaredModel.functionDomain (C := familyModel) products declarations.scalar) declarations.fibre))
    declarations.component_header_read (declarations.branch_result_read Families.products_substitution)

theorem extracted_branch_is_supplied : extractedBranch = declarations.branch :=
  declarations.branch_section_recovers_supplied Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta

theorem generated_elimination_recovers_branch :
    model.evaluateTerm declarations.componentContext DeclaredModel.Declarations.pairElimination =
      some ⟨familyModel.toCwf.tySub declarations.motive
        (pack sums (DeclaredModel.functionDomain (C := familyModel) products declarations.scalar) declarations.fibre),
          extractedBranch⟩ := by
  rw [extracted_branch_is_supplied]
  exact declarations.pair_elimination_read Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta

def falseFunction (_ : Bool) : Bool := false
def trueFunction (_ : Bool) : Bool := true

def falsePoint : declarations.componentContext.1 := ⟨⟨PUnit.unit, falseFunction⟩, ⟨0, by decide⟩⟩
def trueZero : declarations.componentContext.1 := ⟨⟨PUnit.unit, trueFunction⟩, ⟨0, by decide⟩⟩
def trueOne : declarations.componentContext.1 := ⟨⟨PUnit.unit, trueFunction⟩, ⟨1, by decide⟩⟩

theorem supplied_witness_readouts :
    (extractedBranch falsePoint).val = 0 ∧ (extractedBranch trueZero).val = 0 ∧
      (extractedBranch trueOne).val = 1 := by
  rw [extracted_branch_is_supplied]
  exact ⟨rfl, rfl, rfl⟩

theorem function_changes_domain :
    Fintype.card (declarations.fibre ⟨PUnit.unit, falseFunction⟩) = 1 ∧
      Fintype.card (declarations.fibre ⟨PUnit.unit, trueFunction⟩) = 2 := by decide

theorem full_pair_motive_changes_type :
    Fintype.card (declarations.motive ⟨PUnit.unit, ⟨trueFunction, ⟨0, by decide⟩⟩⟩) = 2 ∧
      Fintype.card (declarations.motive ⟨PUnit.unit, ⟨trueFunction, ⟨1, by decide⟩⟩⟩) = 3 := by decide

theorem omission_of_second_witness_detected :
    (extractedBranch trueOne).val ≠ (extractedBranch trueZero).val := by
  rcases supplied_witness_readouts with ⟨_, zeroRead, oneRead⟩
  rw [zeroRead, oneRead]
  decide

def wrongAnnotation : familyModel.toCwf.Ty declarations.componentContext.1 := fun _ => Bool

theorem branch_annotation_differs :
    familyModel.toCwf.tySub declarations.motive
      (pack sums (DeclaredModel.functionDomain (C := familyModel) products declarations.scalar) declarations.fibre) ≠ wrongAnnotation := by
  intro same
  have atFalse := congrArg (fun family => Nat.card (family falsePoint)) same
  change Nat.card (Fin 1) = Nat.card Bool at atFalse
  norm_num [Nat.card_eq_fintype_card] at atFalse

theorem incompatible_annotation_rejected :
    ModelData.check? (model.evaluateTerm declarations.componentContext (Controls.fullBranch 0))
      wrongAnnotation = none := by
  rw [declarations.branch_read]
  change Value.atType? _ wrongAnnotation = none
  exact Value.atType?_none _ wrongAnnotation branch_annotation_differs

abbrev booleanContext : Context familyModel 2 :=
  ((Context.nil familyModel).snoc scalar).snoc (fun _ => Bool)

theorem duplicate_context_read : model.evaluateContext Controls.duplicateContext = some booleanContext :=
  model.evaluateContext_snoc (.snoc .nil (Controls.scalar 0)) (Controls.scalar 1)
    ((Context.nil familyModel).snoc scalar) (fun _ => Bool)
    (model.evaluateContext_snoc .nil (Controls.scalar 0) (Context.nil familyModel) scalar rfl
      declarations.scalar_empty_read)
    (declarations.scalar_read ((Context.nil familyModel).snoc scalar))

def exchangeRaw : Substitution Controls.symbols 2 2 :=
  Fin.cases (.var 1) (fun _ => .var 0)

def exchange (point : booleanContext.1) : booleanContext.1 :=
  ⟨⟨point.1.1, point.2⟩, point.1.2⟩

theorem exchange_evaluated : model.evaluateSubstitution booleanContext booleanContext exchangeRaw = some exchange := by
  apply (model.evaluateSubstitution_eq_some_iff _ _ _ _).mpr
  intro position
  fin_cases position <;> rfl

def exchangedNewest : Derivation Controls.signature
    (.term Controls.duplicateContext ((TermExpr.var 0).substitute exchangeRaw)
      ((Controls.scalar 2).substitute exchangeRaw)) :=
  Controls.duplicateOlder.reindex (congrArg (Judgment.term Controls.duplicateContext (.var 1))
    (Controls.scalar_substitute exchangeRaw).symm)

noncomputable def newest := Controls.duplicateNewest.termSection model realization
  Families.products_substitution
  (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta
  booleanContext (fun _ => Bool) duplicate_context_read (declarations.scalar_read booleanContext)

theorem newest_read : newest = fun point : booleanContext.1 => point.2 :=
  Controls.duplicateNewest.termSection_unique model realization Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta
    booleanContext (fun _ => Bool) duplicate_context_read (declarations.scalar_read booleanContext) _ rfl

noncomputable def afterExchange := familyModel.toCwf.tmSub newest exchange

theorem actual_generated_substitution :
    exchangedNewest.termSection model realization Families.products_substitution
        (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta
        booleanContext (familyModel.toCwf.tySub (fun _ => Bool) exchange) duplicate_context_read
        (model.evaluateType_substitute Families.products_substitution (Controls.scalar 2)
          booleanContext booleanContext exchangeRaw
          (ModelSubstitution.ofEvaluated model booleanContext booleanContext exchangeRaw exchange exchange_evaluated)
          (fun _ => Bool) (declarations.scalar_read booleanContext)) = afterExchange :=
  Controls.duplicateNewest.termSection_substitution model realization Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) products_eta
    exchangedNewest booleanContext booleanContext
    (ModelSubstitution.ofEvaluated model booleanContext booleanContext exchangeRaw exchange exchange_evaluated)
    (fun _ => Bool) duplicate_context_read duplicate_context_read (declarations.scalar_read booleanContext)

theorem omitted_substitution_changes_answer :
    newest ⟨⟨PUnit.unit, false⟩, true⟩ = true ∧
      afterExchange ⟨⟨PUnit.unit, false⟩, true⟩ = false := by
  change newest ⟨⟨PUnit.unit, false⟩, true⟩ = true ∧
    newest (exchange ⟨⟨PUnit.unit, false⟩, true⟩) = false
  rw [newest_read]
  exact ⟨rfl, rfl⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelControls
