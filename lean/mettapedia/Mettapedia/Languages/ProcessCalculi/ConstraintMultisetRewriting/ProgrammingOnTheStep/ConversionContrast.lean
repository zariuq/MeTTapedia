import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerArithmetic

/-!
# One equation, two verdicts: computation in conversion against computation by firings

The recursion equation of addition, `add 1 (succ 0) ≐ succ (add 1 0)`, as a store of the knowledge:

* in the tree's package with addition as a declared computation (`TowerArithmeticModel`, where
  `add a (succ b)` computes to `succ (add a b)` in conversion), the store is solved by the identity:
  the two sides are equal terms (`computed_solvable`);
* in the all-rigid package of `VectorPackage`, where `add` is a head of calls evaluated by firings,
  the same store has no solution: its sides are spines of different rigid constants
  (`fired_unsolvable`).

So the knowledge of the step sees exactly the computation the package puts into conversion. A
function whose values a program computes by firings never meets its values in the knowledge, and
the types that mention it never meet the types of its results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.ConversionContrast

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

/-! ## Addition in conversion -/

namespace Computed

open TowerArithmeticModel
open TowerNumbersModel (num zero succ u)

/-- The package with the natural numbers and addition computed in conversion. -/
abbrev arith : Rules Tower.Head := TowerArithmeticModel.rules Tower.zero

abbrev arithLevels : LevelModel arith ℕ := TowerArithmeticModel.levels Tower.zero (fun _ => 0)

theorem num_typed' {n : Nat} (Γ : Tower.Ctx n) : Typed arith Γ (.const num) (.head u) :=
  TowerNumbersModel.num_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort (declaredNum Tower.zero)

theorem zero_typed' {n : Nat} (Γ : Tower.Ctx n) : Typed arith Γ (.const zero) (.const num) :=
  .const (declaredZero Tower.zero) (num_typed' .nil) (.sort _)

theorem succ_typed' {n : Nat} (Γ : Tower.Ctx n) :
    Typed arith Γ (.const succ) (.pi (.const num) (.const num)) :=
  .const (declaredSucc Tower.zero) (.piForm (num_typed' _) (.sort _) (num_typed' _) (.sort _) (.sorts _ _))
    (.sort _)

theorem add_typed' {n : Nat} (Γ : Tower.Ctx n) :
    Typed arith Γ (.const add) (.pi (.const num) (.pi (.const num) (.const num))) :=
  .const (declaredAdd Tower.zero)
    (.piForm (num_typed' _) (.sort _) (.piForm (num_typed' _) (.sort _) (num_typed' _) (.sort _) (.sorts _ _))
      (.sort _) (.sorts _ _)) (.sort _)

def oneC : Tower.Tm 0 := .app (.const succ) (.const zero)

/-- `add 1 (succ 0)`. -/
def lhs : Tower.Tm 0 := .app (.app (.const add) oneC) (.app (.const succ) (.const zero))

/-- `succ (add 1 0)`. -/
def rhs : Tower.Tm 0 := .app (.const succ) (.app (.app (.const add) oneC) (.const zero))

theorem one_typed' : Typed arith .nil oneC (.const num) := .appElim (succ_typed' _) (zero_typed' _)

theorem lhs_typed : Typed arith .nil lhs (.const num) :=
  .appElim (.appElim (add_typed' _) one_typed') (.appElim (succ_typed' _) (zero_typed' _))

theorem rhs_typed : Typed arith .nil rhs (.const num) :=
  .appElim (succ_typed' _) (.appElim (.appElim (add_typed' _) one_typed') (zero_typed' _))

/-- `num`, as a formed type of the empty frame. -/
def numType : TypeOver (empty arith) := ⟨.const num, u, .sort _, num_typed' _⟩

/-- `add 1 (succ 0) ≐ succ (add 1 0)`, in the package where addition computes. -/
def store : EquationStore (TotalTerm (empty arith)) :=
  [(⟨numType, ⟨lhs, lhs_typed⟩⟩, ⟨numType, ⟨rhs, rhs_typed⟩⟩)]

/-- **The two sides are equal terms**, by the declared computation of addition. -/
theorem sides_equal : Equal arith .nil lhs rhs (.const num) :=
  .root (add_succ_step Tower.zero oneC (.const zero)) lhs_typed rhs_typed

/-- **The equation holds in the knowledge**: the identity solves it. -/
theorem computed_solvable : (frames arithLevels).Solvable store := by
  refine ⟨empty arith, 𝟙 _, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames arithLevels).E (TotalTerm.reindex _ (𝟙 _)) (TotalTerm.reindex _ (𝟙 _))
  rw [reindex_id, reindex_id]
  exact (equivalent_iff arithLevels _ _).mpr ⟨⟨u, .sort _, .refl (num_typed' _)⟩, sides_equal⟩

end Computed

/-! ## Addition by firings -/

namespace Fired

open VectorPackage VectorPrograms

/-- `add 1 (succ 0) ≐ succ (add 1 0)`, in the all-rigid package. -/
def store : EquationStore (TotalTerm (empty rules)) :=
  [(natTerm (addC one (succC zeroC)) (add_typed (one_typed _) (succ_typed (zero_typed _))),
    natTerm (succC (addC one zeroC)) (succ_typed (add_typed (one_typed _) (zero_typed _))))]

/-- **The same equation has no solution** where `add` is evaluated by firings. -/
theorem fired_unsolvable : ¬ (frames levels).Solvable store :=
  ContextualDependentRigid.not_solvable_of_storeClashes (S := setting) rigid facts complete (by decide)

end Fired

end ProgrammingOnTheStep.ConversionContrast

#print axioms ProgrammingOnTheStep.ConversionContrast.Computed.sides_equal
#print axioms ProgrammingOnTheStep.ConversionContrast.Computed.computed_solvable
#print axioms ProgrammingOnTheStep.ConversionContrast.Fired.fired_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
