import Mettapedia.CategoryTheory.ElementaryToposDependentProducts
import Mettapedia.CategoryTheory.TypeSubobjectClassifier
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Varying fibres and complete dependent-function controls

The constructed function object retains a genuinely varying finite output
and reads its entire supplied argument. Actual source substitution changes
the chosen fibre. The dependent-product adjunction recovers the complete
supplied dependent body. A second profile has a function on one fibre but
has no global base-preserving function, excluding a global-extension model
of slice exponentials.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposDependentClosureControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open ElementaryToposSliceFunctionSpace ElementaryToposSliceExponentials
open ElementaryToposDependentProducts

abbrev classifier := TypeSubobjectClassifier.classifier

abbrev Source := Nat × Nat
abbrev Result := (number : Nat) × Fin (number + 1)

def sourceBase : Source ⟶ Nat := TypeCat.ofHom Prod.fst
def resultBase : Result ⟶ Nat := TypeCat.ofHom Sigma.fst
def shifted : Nat ⟶ Nat := TypeCat.ofHom Nat.succ
def doubled : Nat ⟶ Nat := TypeCat.ofHom fun number => 2 * number

def resultOf (input : Source) : Result :=
  ⟨input.1, ⟨min input.2 input.1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

def fibreBody : pullback sourceBase shifted ⟶ Result :=
  TypeCat.ofHom fun point => resultOf (pullback.fst sourceBase shifted point)

theorem fibreBody_base : fibreBody ≫ resultBase = pullback.fst sourceBase shifted ≫ sourceBase := rfl

def suppliedPoint (number input : Nat) : PUnit ⟶ pullback sourceBase shifted :=
  pullback.lift (TypeCat.ofHom fun _ => (number + 1, input))
    (TypeCat.ofHom fun _ => number) rfl

theorem suppliedPoint_source (number input : Nat) :
    pullback.fst sourceBase shifted (suppliedPoint number input PUnit.unit) =
      (number + 1, input) :=
  congrArg (fun arrow : PUnit ⟶ Source => arrow PUnit.unit) (pullback.lift_fst _ _ _)

def fibreFunction : Nat ⟶ functionSpace classifier sourceBase resultBase :=
  transpose classifier sourceBase resultBase shifted fibreBody fibreBody_base

theorem fibreFunction_base : fibreFunction ≫ functionBase classifier sourceBase resultBase = shifted :=
  transpose_base classifier sourceBase resultBase shifted fibreBody fibreBody_base

theorem complete_function_readout (number input : Nat) :
    untranspose classifier sourceBase resultBase shifted fibreFunction fibreFunction_base
        (suppliedPoint number input PUnit.unit) =
      resultOf (number + 1, input) := by
  have beta := congrArg
    (fun arrow : pullback sourceBase shifted ⟶ Result =>
      arrow (suppliedPoint number input PUnit.unit))
    (untranspose_transpose classifier sourceBase resultBase shifted fibreBody fibreBody_base)
  change untranspose classifier sourceBase resultBase shifted fibreFunction fibreFunction_base
    (suppliedPoint number input PUnit.unit) = _ at beta
  exact beta.trans (congrArg resultOf (suppliedPoint_source number input))

theorem full_argument_changes_output :
    (untranspose classifier sourceBase resultBase shifted fibreFunction fibreFunction_base
      (suppliedPoint 0 0 PUnit.unit)).2.val = 0 ∧
    (untranspose classifier sourceBase resultBase shifted fibreFunction fibreFunction_base
      (suppliedPoint 0 1 PUnit.unit)).2.val = 1 := by
  rw [complete_function_readout, complete_function_readout]
  constructor <;> rfl

attribute [local instance] Over.cartesianMonoidalCategory

def sourceObject : Over Nat := Over.mk sourceBase
def resultObject : Over Nat := Over.mk resultBase
def shiftedContext : Over Nat := Over.mk shifted
def substitutedContext : Over Nat := Over.mk (doubled ≫ shifted)
def actualSubstitution : substitutedContext ⟶ shiftedContext := Over.homMk doubled rfl
def suppliedBody : sourceObject ⊗ shiftedContext ⟶ resultObject :=
  Over.homMk fibreBody fibreBody_base

theorem actual_substitution_is_nonidentity : doubled ≠ 𝟙 Nat := by
  intro same
  have atOne := congrArg (fun arrow : Nat ⟶ Nat => arrow 1) same
  change 2 = 1 at atOne
  contradiction

theorem whole_function_substitution :
    overCurry classifier (sourceObject ◁ actualSubstitution ≫ suppliedBody) =
      actualSubstitution ≫ overCurry classifier suppliedBody :=
  homEquiv_naturality classifier sourceObject resultObject actualSubstitution suppliedBody

abbrev DependentResult := (input : Source) × Fin (input.1 + 1)
def dependentBase : DependentResult ⟶ Source := TypeCat.ofHom Sigma.fst
def dependentResult : Over Source := Over.mk dependentBase

def dependentBody : (Over.pullback sourceBase).obj shiftedContext ⟶ dependentResult :=
  Over.homMk (TypeCat.ofHom fun point =>
    let input := pullback.snd shifted sourceBase point
    (⟨input, ⟨min input.2 input.1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩ : DependentResult)) rfl

/-- The actual dependent product recovers both the chosen source and its
genuinely dependent `Fin` witness, before and after arbitrary arguments. -/
theorem dependent_complete_readout :
    dependentUncurry classifier sourceBase (dependentCurry classifier sourceBase dependentBody) =
      dependentBody := dependent_beta classifier sourceBase dependentBody

theorem dependent_complete_substitution :
    dependentCurry classifier sourceBase
      ((Over.pullback sourceBase).map actualSubstitution ≫ dependentBody) =
      actualSubstitution ≫ dependentCurry classifier sourceBase dependentBody :=
  dependentCurry_substitution classifier sourceBase actualSubstitution dependentBody

def fibreSource : Bool ⟶ Bool := 𝟙 Bool
def oneFibreTarget : PUnit ⟶ Bool := TypeCat.ofHom fun _ => true
def trueContext : PUnit ⟶ Bool := TypeCat.ofHom fun _ => true
def oneFibreBody : pullback fibreSource trueContext ⟶ PUnit := TypeCat.ofHom fun _ => PUnit.unit

theorem oneFibreBody_base :
    oneFibreBody ≫ oneFibreTarget = pullback.fst fibreSource trueContext ≫ fibreSource := by
  rw [pullback.condition]
  rfl

def genuinelyFibrewise : PUnit ⟶ functionSpace classifier fibreSource oneFibreTarget :=
  transpose classifier fibreSource oneFibreTarget trueContext oneFibreBody oneFibreBody_base

theorem fibrewise_function_exists :
    ∃ function : PUnit ⟶ functionSpace classifier fibreSource oneFibreTarget,
      function ≫ functionBase classifier fibreSource oneFibreTarget = trueContext :=
  ⟨genuinelyFibrewise,
    transpose_base classifier fibreSource oneFibreTarget trueContext oneFibreBody oneFibreBody_base⟩

/-- A valid function on the true fibre cannot be forced to extend to the
false fibre, where the target has no values. -/
theorem no_global_extension :
    ¬ ∃ function : Bool ⟶ PUnit, function ≫ oneFibreTarget = fibreSource := by
  rintro ⟨function, overBase⟩
  have impossible := congrArg (fun arrow : Bool ⟶ Bool => arrow false) overBase
  change true = false at impossible
  contradiction

end Mettapedia.CategoryTheory.ElementaryToposDependentClosureControls
