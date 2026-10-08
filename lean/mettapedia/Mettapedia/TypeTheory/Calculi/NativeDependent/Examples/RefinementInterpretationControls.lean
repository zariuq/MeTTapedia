import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementEvidenceExtraction
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementJudgmentControls
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Native interpretation of conditional refinements and varying fibres

An independently supplied natural-number family realizes the scalar header.
Its finite fibre depends on the supplied number, and its positive predicate
is a proper subobject. Conditional refinement retains that exact number;
removing the positivity assumption rejects the same authored introduction.
The generated higher-order proposition quantifies over genuine native
function and proposition values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.InterpretationControls

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations
open PresheafNativePropositionReadout PresheafNativeStableRefinement

noncomputable section

abbrev World := WalkingParallelPair
abbrev native := NativeModel World
abbrev emptyScope : Scope World 0 := Scope.nil World

def naturalFamily (base : Worldᵒᵖ ⥤ Type) : DisplayedFamily base :=
  (Functor.const base.Elements).obj Nat

def scalarType : NativeType emptyScope.1 := LocalType.present (naturalFamily emptyScope.1)

abbrev scalarScope : Scope World 1 := emptyScope.snoc scalarType

def naturals : Worldᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def finiteFamily : DisplayedFamily naturals where
  obj point := Fin (Nat.succ point.2)
  map arrow := TypeCat.ofHom (Fin.cast (congrArg Nat.succ arrow.property))
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

def scalarName : scalarScope.1 ⟶ naturals where
  app _ := TypeCat.ofHom fun value => value.2
  naturality := by intros; rfl

def fibreType : NativeType scalarScope.1 := ⟨naturals, finiteFamily, scalarName⟩

def positivity : Subfunctor scalarScope.1 where
  obj _ := {value | 0 < (show Nat from value.2)}
  map _ := by intro value positive; exact positive

def model : ModelData Controls.symbols World where
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

theorem scalar_read {n : Nat} (Γ : Scope World n) :
    model.evaluateType Γ (Controls.scalar n) =
      some (scalarType.reindex (native.toEmpty Γ.1)) :=
  model.evaluate_family Γ .scalar Fin.elim0 (native.toEmpty Γ.1)
    (fun position => Fin.elim0 position)

set_option backward.isDefEq.respectTransparency false in
theorem scalar_empty_read : model.evaluateType emptyScope (Controls.scalar 0) = some scalarType := by
  have evaluated := scalar_read emptyScope
  have same : native.toEmpty emptyScope.1 = native.toCwf.idS emptyScope.1 :=
    (native.toEmpty_unique _ _).symm
  change model.evaluateType emptyScope (Controls.scalar 0) =
    some (native.toCwf.tySub scalarType (native.toEmpty emptyScope.1)) at evaluated
  rw [same, native.toCwf.tySub_id] at evaluated
  exact evaluated

theorem scalar_context_read :
    model.evaluateContext (.snoc .nil (Controls.scalar 0)) = some scalarScope :=
  model.evaluateContext_snoc .nil (Controls.scalar 0) emptyScope scalarType rfl scalar_empty_read

theorem realization : SignatureRealization model Controls.signature where
  typeHeader := by
    intro symbol
    cases symbol
    · rfl
    · exact scalar_context_read
  termHeader := fun symbol => nomatch symbol
  predicateHeader := fun _ => scalar_context_read
  termResult := fun symbol => nomatch symbol

theorem positive_scalar_read : model.evaluatePredicate scalarScope (Controls.positive 0) = some positivity := by
  have read := model.evaluate_predicateAtom scalarScope .positive
    (Controls.singletonArgument (.var 0)) (𝟙 scalarScope.1) (by
      intro index
      cases index using Fin.cases with
      | zero =>
          change some (scalarScope.2.lookup 0) =
            some ((scalarScope.2.lookup 0).substitute (native.toCwf.idS scalarScope.1))
          rw [Value.substitute_identity]
      | succ impossible => exact Fin.elim0 impossible)
  change model.evaluatePredicate scalarScope (Controls.positive 0) =
    some (positivity.preimage (𝟙 scalarScope.1)) at read
  rw [Subfunctor.preimage_id] at read
  exact read

set_option backward.isDefEq.respectTransparency false in
theorem fibre_scalar_read : model.evaluateType scalarScope (Controls.fibre 0) = some fibreType := by
  have read := model.evaluate_family scalarScope .fibre
    (Controls.singletonArgument (.var 0)) (𝟙 scalarScope.1) (by
      intro index
      cases index using Fin.cases with
      | zero =>
          change some (scalarScope.2.lookup 0) =
            some ((scalarScope.2.lookup 0).substitute (native.toCwf.idS scalarScope.1))
          rw [Value.substitute_identity]
      | succ impossible => exact Fin.elim0 impossible)
  change model.evaluateType scalarScope (Controls.fibre 0) =
    some (native.toCwf.tySub fibreType (native.toCwf.idS scalarScope.1)) at read
  rw [native.toCwf.tySub_id] at read
  exact read

def scalarVariableType : NativeType scalarScope.1 :=
  native.toCwf.tySub scalarType (native.toCwf.wk scalarType)

def scalarVariable : scalarVariableType.decoded.sections := native.toCwf.vz scalarType

theorem scalar_variable_type_read : model.evaluateType scalarScope (Controls.scalar 1) =
    some scalarVariableType := by
  have read := scalar_read scalarScope
  have same : native.toEmpty scalarScope.1 = native.toCwf.wk scalarType :=
    (native.toEmpty_unique _ _).symm
  rw [same] at read
  exact read

theorem scalar_variable_read : model.evaluateTerm scalarScope (.var 0) =
    some ⟨scalarVariableType, scalarVariable⟩ := rfl

abbrev doubleScope : Scope World 2 := scalarScope.snoc scalarVariableType

def newestScalar : doubleScope.1 ⟶ scalarScope.1 where
  app _ := TypeCat.ofHom fun value => ⟨PUnit.unit, value.2⟩
  naturality := by intros; rfl

def newestRenaming : ModelRenaming doubleScope scalarScope (fun _ => 0) where
  arrow := newestScalar
  readout index := by
    cases index using Fin.cases with
    | zero => rfl
    | succ impossible => exact Fin.elim0 impossible

theorem newest_positive_read : model.evaluatePredicate doubleScope (Controls.positive 1) =
    some (positivity.preimage newestScalar) := by
  have read := model.evaluatePredicate_rename (NativeLocalTypeOperations.products_substitution World)
    (Controls.positive 0) doubleScope scalarScope (fun _ => 0) newestRenaming positivity positive_scalar_read
  exact read

theorem unrestricted_refinement_rejected : model.evaluateTerm scalarScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) = none := by
  change External.bindResult (model.evaluateType scalarScope (Controls.scalar 1)) _ = _
  rw [scalar_variable_type_read]
  change External.bindResult (model.evaluatePredicate doubleScope (Controls.positive 1)) _ = _
  rw [newest_positive_read]
  change ModelData.refine? scalarVariableType (positivity.preimage newestScalar)
    (model.evaluateTerm scalarScope (.var 0)) = none
  rw [scalar_variable_read]
  apply ModelData.refine?_rejected
  intro allPositive
  have zeroPositive := allPositive (Opposite.op WalkingParallelPair.zero) ⟨PUnit.unit, (0 : Nat)⟩
  exact Nat.not_lt_zero 0 zeroPositive

theorem varying_fibre_readout (world : Worldᵒᵖ) (number : Nat) :
    fibreType.decoded.obj ⟨world, (⟨PUnit.unit, (number : Nat)⟩ : scalarScope.1.obj world)⟩ =
      Fin (Nat.succ number) := rfl

theorem positivity_is_proper : positivity ≠ ⊤ := by
  intro equality
  have member : (⟨PUnit.unit, (0 : Nat)⟩ : scalarScope.1.obj (Opposite.op WalkingParallelPair.zero)) ∈
      positivity.obj (Opposite.op WalkingParallelPair.zero) := by
    rw [equality]
    trivial
  exact Nat.not_lt_zero 0 member

abbrev conditionalScope : Scope World 1 := scalarScope.assume positivity

def conditionalType : NativeType conditionalScope.1 := scalarVariableType.reindex positivity.ι

def conditionalValue : conditionalType.decoded.sections :=
  native.toCwf.tmSub scalarVariable positivity.ι

theorem conditional_context_read : model.evaluateContext Controls.conditionalContext =
    some conditionalScope :=
  model.evaluateContext_assume _ _ scalarScope positivity scalar_context_read positive_scalar_read

theorem conditional_type_read : model.evaluateType conditionalScope (Controls.scalar 1) =
    some conditionalType :=
  model.evaluateType_restrict (NativeLocalTypeOperations.products_substitution World)
    scalarScope positivity (Controls.scalar 1) scalarVariableType scalar_variable_type_read

theorem conditional_variable_read : model.evaluateTerm conditionalScope (.var 0) =
    some ⟨conditionalType, conditionalValue⟩ := rfl

def conditionalNewest : (conditionalScope.snoc conditionalType).1 ⟶ scalarScope.1 where
  app _ := TypeCat.ofHom fun value => ⟨PUnit.unit, value.2⟩
  naturality := by intros; rfl

def conditionalNewestRenaming : ModelRenaming (conditionalScope.snoc conditionalType)
    scalarScope (fun _ => 0) where
  arrow := conditionalNewest
  readout index := by
    cases index using Fin.cases with
    | zero => rfl
    | succ impossible => exact Fin.elim0 impossible

def conditionalPredicate : Subfunctor (conditionalScope.snoc conditionalType).1 :=
  positivity.preimage conditionalNewest

theorem conditional_predicate_read : model.evaluatePredicate
    (conditionalScope.snoc conditionalType) (Controls.positive 1) = some conditionalPredicate :=
  model.evaluatePredicate_rename (NativeLocalTypeOperations.products_substitution World)
    (Controls.positive 0) (conditionalScope.snoc conditionalType) scalarScope (fun _ => 0)
      conditionalNewestRenaming positivity positive_scalar_read

theorem conditional_satisfies : ∀ world (base : conditionalScope.1.obj world),
    (⟨base, conditionalValue.val ⟨world, base⟩⟩ : (conditionalScope.snoc conditionalType).1.obj world) ∈
      conditionalPredicate.obj world := by
  intro world base
  exact base.property

def conditionalRefined : (chosen conditionalType conditionalPredicate).decoded.sections :=
  intro conditionalType conditionalPredicate conditionalValue conditional_satisfies

theorem conditional_refinement_read : model.evaluateTerm conditionalScope
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)) =
      some ⟨chosen conditionalType conditionalPredicate, conditionalRefined⟩ :=
  model.evaluate_refine conditionalScope _ _ _ conditionalType conditionalPredicate conditionalValue
    conditional_type_read conditional_predicate_read conditional_variable_read conditional_satisfies

set_option backward.isDefEq.respectTransparency false in
theorem conditional_forgetting_read : model.evaluateTerm conditionalScope
    (.forget (Controls.scalar 1) (Controls.positive 1)
      (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0))) =
      some ⟨conditionalType, conditionalValue⟩ := by
  have read := model.evaluate_forget conditionalScope _ _ _ conditionalType conditionalPredicate conditionalRefined
    conditional_type_read conditional_predicate_read conditional_refinement_read
  rw [conditionalRefined, PresheafNativeStableRefinement.beta] at read
  exact read

def positiveBase (world : Worldᵒᵖ) (number : Nat) (positive : 0 < number) :
    conditionalScope.1.obj world := ⟨⟨PUnit.unit, number⟩, positive⟩

set_option backward.isDefEq.respectTransparency false in
theorem supplied_number_retained (world : Worldᵒᵖ) (number : Nat) (positive : 0 < number) :
    (forget conditionalType conditionalPredicate conditionalRefined).val
      ⟨world, positiveBase world number positive⟩ = number := by
  rw [conditionalRefined, PresheafNativeStableRefinement.beta]
  rfl

theorem distinct_numbers_retained (world : Worldᵒᵖ) :
    (forget conditionalType conditionalPredicate conditionalRefined).val
        ⟨world, positiveBase world 1 (by decide)⟩ ≠
      (forget conditionalType conditionalPredicate conditionalRefined).val
        ⟨world, positiveBase world 2 (by decide)⟩ := by
  rw [supplied_number_retained, supplied_number_retained]
  exact (by decide : (1 : Nat) ≠ 2)

theorem conditional_generated_sound : Interprets model
    (.term Controls.conditionalContext
      (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0))
      (.comprehension (Controls.scalar 1) (Controls.positive 1))) :=
  Controls.conditionalRefinement.native_sound model realization

theorem conditional_beta_sound : Interprets model
    (.termEq Controls.conditionalContext
      (.forget (Controls.scalar 1) (Controls.positive 1)
        (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0)))
      (.var 0) (Controls.scalar 1)) :=
  Controls.conditionalBeta.native_sound model realization

theorem higher_order_generated_sound : Interprets model
    (.entails .nil (.all (Controls.predicateFunctionAt 0)
      (.all (Controls.scalar 1)
        (.implies Controls.appliedPredicate Controls.appliedPredicate)))) :=
  Controls.quantifiedPredicateFunction.native_sound model realization

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.InterpretationControls
