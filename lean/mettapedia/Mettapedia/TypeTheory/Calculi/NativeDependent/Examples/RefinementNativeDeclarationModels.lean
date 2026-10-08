import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementEvidenceExtraction
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementJudgmentControls

/-!
# Native scalar, dependent finite fibre and guarded declaration models

For each small presheaf world category, the independent scalar declaration
has natural-number sections, its fibre has Fin (n + 1) at input n, and the
predicate declaration is actual positivity. Their local header realization
is earned by raw context and variable evaluation. Mixed assumption scopes
restrict the scalar values to positive inputs before refinement introduction.
The negative introduction test uses an explicitly supplied world.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.NativeDeclarationModels

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations
open PresheafNativePropositionReadout PresheafNativeStableRefinement

variable {C : Type} [Category C]

noncomputable section

abbrev native := NativeModel C
abbrev emptyScope : Scope C 0 := Scope.nil C

def naturalFamily (base : Cᵒᵖ ⥤ Type) : DisplayedFamily base :=
  (Functor.const base.Elements).obj Nat

def scalarType : NativeType (emptyScope (C := C)).1 := LocalType.present (naturalFamily emptyScope.1)

abbrev scalarScope : Scope C 1 := emptyScope.snoc scalarType

def naturals : Cᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def finiteFamily : DisplayedFamily (naturals (C := C)) where
  obj point := Fin (Nat.succ point.2)
  map arrow := TypeCat.ofHom (Fin.cast (congrArg Nat.succ arrow.property))
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

def scalarName : (scalarScope (C := C)).1 ⟶ naturals where
  app _ := TypeCat.ofHom fun value => value.2
  naturality := by intros; rfl

def fibreType : NativeType (scalarScope (C := C)).1 := ⟨naturals, finiteFamily, scalarName⟩

def positivity : Subfunctor (scalarScope (C := C)).1 where
  obj _ := {value | 0 < (show Nat from value.2)}
  map _ := by intro value positive; exact positive

def model : ModelData Controls.symbols C where
  typeParameters
    | .scalar => emptyScope
    | .fibre => scalarScope
  typeFamily
    | .scalar => scalarType
    | .fibre => fibreType
  termParameters := fun symbol => nomatch symbol
  termType := fun symbol => nomatch symbol
  termValue := fun symbol => nomatch symbol
  predicateParameters := fun _ => scalarScope
  predicateValue := fun _ => positivity

theorem scalar_read {n : Nat} (Γ : Scope C n) :
    (model (C := C)).evaluateType Γ (Controls.scalar n) =
      some (scalarType.reindex ((native (C := C)).toEmpty Γ.1)) :=
  (model (C := C)).evaluate_family Γ .scalar Fin.elim0 ((native (C := C)).toEmpty Γ.1)
    (fun position => Fin.elim0 position)

set_option backward.isDefEq.respectTransparency false in
theorem scalar_empty_read : (model (C := C)).evaluateType emptyScope (Controls.scalar 0) = some scalarType := by
  have evaluated := scalar_read (C := C) emptyScope
  have same : (native (C := C)).toEmpty emptyScope.1 = (native (C := C)).toCwf.idS emptyScope.1 :=
    ((native (C := C)).toEmpty_unique _ _).symm
  change (model (C := C)).evaluateType emptyScope (Controls.scalar 0) =
    some ((native (C := C)).toCwf.tySub scalarType ((native (C := C)).toEmpty emptyScope.1)) at evaluated
  rw [same, (native (C := C)).toCwf.tySub_id] at evaluated
  exact evaluated

theorem scalar_context_read :
    (model (C := C)).evaluateContext (.snoc .nil (Controls.scalar 0)) = some scalarScope :=
  (model (C := C)).evaluateContext_snoc .nil (Controls.scalar 0) emptyScope scalarType rfl scalar_empty_read

theorem realization : SignatureRealization (model (C := C)) Controls.signature where
  typeHeader := by
    intro symbol
    cases symbol
    · rfl
    · exact scalar_context_read
  termHeader := fun symbol => nomatch symbol
  predicateHeader := fun _ => scalar_context_read
  termResult := fun symbol => nomatch symbol

theorem positive_scalar_read : (model (C := C)).evaluatePredicate scalarScope (Controls.positive 0) = some positivity := by
  have read := (model (C := C)).evaluate_predicateAtom scalarScope .positive
    (Controls.singletonArgument (.var 0)) (𝟙 scalarScope.1) (by
      intro index
      cases index using Fin.cases with
      | zero =>
          change some (scalarScope.2.lookup 0) =
            some ((scalarScope.2.lookup 0).substitute ((native (C := C)).toCwf.idS scalarScope.1))
          rw [Value.substitute_identity]
      | succ impossible => exact Fin.elim0 impossible)
  change (model (C := C)).evaluatePredicate scalarScope (Controls.positive 0) =
    some (positivity.preimage (𝟙 scalarScope.1)) at read
  rw [Subfunctor.preimage_id] at read
  exact read

set_option backward.isDefEq.respectTransparency false in
theorem fibre_scalar_read : (model (C := C)).evaluateType scalarScope (Controls.fibre 0) = some fibreType := by
  have read := (model (C := C)).evaluate_family scalarScope .fibre
    (Controls.singletonArgument (.var 0)) (𝟙 scalarScope.1) (by
      intro index
      cases index using Fin.cases with
      | zero =>
          change some (scalarScope.2.lookup 0) =
            some ((scalarScope.2.lookup 0).substitute ((native (C := C)).toCwf.idS scalarScope.1))
          rw [Value.substitute_identity]
      | succ impossible => exact Fin.elim0 impossible)
  change (model (C := C)).evaluateType scalarScope (Controls.fibre 0) =
    some ((native (C := C)).toCwf.tySub fibreType ((native (C := C)).toCwf.idS scalarScope.1)) at read
  rw [(native (C := C)).toCwf.tySub_id] at read
  exact read

def scalarVariableType : NativeType (scalarScope (C := C)).1 :=
  (native (C := C)).toCwf.tySub scalarType ((native (C := C)).toCwf.wk scalarType)

def scalarVariable : (scalarVariableType (C := C)).decoded.sections := (native (C := C)).toCwf.vz scalarType

theorem scalar_variable_type_read : (model (C := C)).evaluateType scalarScope (Controls.scalar 1) =
    some scalarVariableType := by
  have read := scalar_read (C := C) scalarScope
  have same : (native (C := C)).toEmpty scalarScope.1 = (native (C := C)).toCwf.wk scalarType :=
    ((native (C := C)).toEmpty_unique _ _).symm
  rw [same] at read
  exact read

theorem scalar_variable_read : (model (C := C)).evaluateTerm scalarScope (.var 0) =
    some ⟨scalarVariableType, scalarVariable⟩ := rfl

abbrev doubleScope : Scope C 2 := scalarScope.snoc scalarVariableType

def newestScalar : (doubleScope (C := C)).1 ⟶ scalarScope.1 where
  app _ := TypeCat.ofHom fun value => ⟨PUnit.unit, value.2⟩
  naturality := by intros; rfl

def newestRenaming : ModelRenaming (doubleScope (C := C)) scalarScope (fun _ => 0) where
  arrow := newestScalar
  readout index := by
    cases index using Fin.cases with
    | zero => rfl
    | succ impossible => exact Fin.elim0 impossible

theorem newest_positive_read : (model (C := C)).evaluatePredicate doubleScope (Controls.positive 1) =
    some (positivity.preimage newestScalar) := by
  have read := (model (C := C)).evaluatePredicate_rename (NativeLocalTypeOperations.products_substitution C)
    (Controls.positive 0) doubleScope scalarScope (fun _ => 0) newestRenaming positivity positive_scalar_read
  exact read

theorem unrestricted_refinement_rejected (world : Cᵒᵖ) : (model (C := C)).evaluateTerm scalarScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) = none := by
  change External.bindResult ((model (C := C)).evaluateType scalarScope (Controls.scalar 1)) _ = _
  rw [scalar_variable_type_read]
  change External.bindResult ((model (C := C)).evaluatePredicate doubleScope (Controls.positive 1)) _ = _
  rw [newest_positive_read]
  change ModelData.refine? scalarVariableType (positivity.preimage newestScalar)
    ((model (C := C)).evaluateTerm scalarScope (.var 0)) = none
  rw [scalar_variable_read]
  apply ModelData.refine?_rejected
  intro allPositive
  have zeroPositive := allPositive world ⟨PUnit.unit, (0 : Nat)⟩
  exact Nat.not_lt_zero 0 zeroPositive

theorem varying_fibre_readout (world : Cᵒᵖ) (number : Nat) :
    fibreType.decoded.obj ⟨world, (⟨PUnit.unit, (number : Nat)⟩ : scalarScope.1.obj world)⟩ =
      Fin (Nat.succ number) := rfl

theorem positivity_is_proper (world : Cᵒᵖ) : (positivity (C := C)) ≠ ⊤ := by
  intro equality
  have member : (⟨PUnit.unit, (0 : Nat)⟩ : scalarScope.1.obj world) ∈ positivity.obj world := by
    rw [equality]
    trivial
  exact Nat.not_lt_zero 0 member

abbrev conditionalScope : Scope C 1 := scalarScope.assume positivity

def conditionalType : NativeType (conditionalScope (C := C)).1 := scalarVariableType.reindex positivity.ι

def conditionalValue : (conditionalType (C := C)).decoded.sections :=
  (native (C := C)).toCwf.tmSub scalarVariable positivity.ι

theorem conditional_context_read : (model (C := C)).evaluateContext Controls.conditionalContext =
    some conditionalScope :=
  (model (C := C)).evaluateContext_assume _ _ scalarScope positivity scalar_context_read positive_scalar_read

theorem conditional_type_read : (model (C := C)).evaluateType conditionalScope (Controls.scalar 1) =
    some conditionalType :=
  (model (C := C)).evaluateType_restrict (NativeLocalTypeOperations.products_substitution C)
    scalarScope positivity (Controls.scalar 1) scalarVariableType scalar_variable_type_read

theorem conditional_variable_read : (model (C := C)).evaluateTerm conditionalScope (.var 0) =
    some ⟨conditionalType, conditionalValue⟩ := rfl

def conditionalNewest : ((conditionalScope (C := C)).snoc conditionalType).1 ⟶ scalarScope.1 where
  app _ := TypeCat.ofHom fun value => ⟨PUnit.unit, value.2⟩
  naturality := by intros; rfl

def conditionalNewestRenaming : ModelRenaming ((conditionalScope (C := C)).snoc conditionalType)
    scalarScope (fun _ => 0) where
  arrow := conditionalNewest
  readout index := by
    cases index using Fin.cases with
    | zero => rfl
    | succ impossible => exact Fin.elim0 impossible

def conditionalPredicate : Subfunctor ((conditionalScope (C := C)).snoc conditionalType).1 :=
  positivity.preimage conditionalNewest

theorem conditional_predicate_read : (model (C := C)).evaluatePredicate
    (conditionalScope.snoc conditionalType) (Controls.positive 1) = some conditionalPredicate :=
  (model (C := C)).evaluatePredicate_rename (NativeLocalTypeOperations.products_substitution C)
    (Controls.positive 0) (conditionalScope.snoc conditionalType) scalarScope (fun _ => 0)
      conditionalNewestRenaming positivity positive_scalar_read

theorem conditional_satisfies : ∀ world (base : (conditionalScope (C := C)).1.obj world),
    (⟨base, conditionalValue.val ⟨world, base⟩⟩ : (conditionalScope.snoc conditionalType).1.obj world) ∈
      conditionalPredicate.obj world := by
  intro world base
  exact base.property

def conditionalRefined : (chosen (conditionalType (C := C)) conditionalPredicate).decoded.sections :=
  intro conditionalType conditionalPredicate conditionalValue conditional_satisfies

theorem conditional_refinement_read : (model (C := C)).evaluateTerm conditionalScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) =
      some ⟨chosen conditionalType conditionalPredicate, conditionalRefined⟩ :=
  (model (C := C)).evaluate_refine conditionalScope _ _ _ conditionalType conditionalPredicate conditionalValue
    conditional_type_read conditional_predicate_read conditional_variable_read conditional_satisfies

set_option backward.isDefEq.respectTransparency false in
theorem conditional_forgetting_read : (model (C := C)).evaluateTerm conditionalScope
    (.forget (Controls.scalar 1) (Controls.positive 1)
      (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0))) =
      some ⟨conditionalType, conditionalValue⟩ := by
  have read := (model (C := C)).evaluate_forget conditionalScope _ _ _ conditionalType conditionalPredicate conditionalRefined
    conditional_type_read conditional_predicate_read conditional_refinement_read
  rw [conditionalRefined, PresheafNativeStableRefinement.beta] at read
  exact read

def positiveBase (world : Cᵒᵖ) (number : Nat) (positive : 0 < number) :
    conditionalScope.1.obj world := ⟨⟨PUnit.unit, number⟩, positive⟩

set_option backward.isDefEq.respectTransparency false in
theorem supplied_number_retained (world : Cᵒᵖ) (number : Nat) (positive : 0 < number) :
    (forget conditionalType conditionalPredicate conditionalRefined).val
      ⟨world, positiveBase world number positive⟩ = number := by
  rw [conditionalRefined, PresheafNativeStableRefinement.beta]
  rfl

theorem distinct_numbers_retained (world : Cᵒᵖ) :
    (forget conditionalType conditionalPredicate conditionalRefined).val
        ⟨world, positiveBase world 1 (by decide)⟩ ≠
      (forget conditionalType conditionalPredicate conditionalRefined).val
        ⟨world, positiveBase world 2 (by decide)⟩ := by
  rw [supplied_number_retained, supplied_number_retained]
  exact (by decide : (1 : Nat) ≠ 2)

abbrev finiteScope : Scope C 2 := scalarScope.snoc fibreType

def finiteVariableType : NativeType (finiteScope (C := C)).1 :=
  fibreType.reindex ((native (C := C)).toCwf.wk fibreType)

def finiteVariable : (finiteVariableType (C := C)).decoded.sections := (native (C := C)).toCwf.vz fibreType

theorem finite_context_read : (model (C := C)).evaluateContext
    (.snoc (.snoc .nil (Controls.scalar 0)) (Controls.fibre 0)) = some finiteScope :=
  (model (C := C)).evaluateContext_snoc _ _ scalarScope fibreType scalar_context_read fibre_scalar_read

theorem finite_variable_type_read : (model (C := C)).evaluateType finiteScope
    ((Controls.fibre 0).rename Fin.succ) = some finiteVariableType :=
  (model (C := C)).evaluateType_rename (NativeLocalTypeOperations.products_substitution C)
    (Controls.fibre 0) finiteScope scalarScope Fin.succ
    (ModelRenaming.weaken scalarScope fibreType) fibreType fibre_scalar_read

theorem finite_variable_read : (model (C := C)).evaluateTerm finiteScope (.var 0) =
    some ⟨finiteVariableType, finiteVariable⟩ := rfl

def finiteBase (world : Cᵒᵖ) (number : Nat) (witness : Fin (Nat.succ number)) :
    finiteScope.1.obj world := ⟨⟨PUnit.unit, number⟩, witness⟩

theorem supplied_finite_witness_retained (world : Cᵒᵖ) (number : Nat)
    (witness : Fin (Nat.succ number)) :
    (finiteVariable (C := C)).val ⟨world, finiteBase world number witness⟩ = witness := rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.NativeDeclarationModels
