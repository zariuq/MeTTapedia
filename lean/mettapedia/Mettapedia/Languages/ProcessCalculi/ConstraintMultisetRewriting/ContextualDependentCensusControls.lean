import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeadsProjectionsControls

/-!
# The census rows still unread

Each store below is in the dynamic pattern fragment, and the projections solver leaves it suspended at budget
16 and eight rounds. These are runs at one budget, not proofs at every budget; each names a shape that no
rule up to the projections round reads. The occurrences in spine arguments are read by the arguments round
(`ContextualDependentIdEndpointsArgumentsControls`); the first three rows stay unread there too.

* **A spine of a local at a flexible base type.** Over `A X : U0`, `λ g. g X ≐ λ g. g A` at
  `(U0 → A) → A`, solvable by `X := A`. The spine decompositions read spines at rigid base types only:
  at an instantiation of `A` by a Π type the comparison η-expands.
* **Nested projections.** `λ g. fst (fst (g X)) ≐ λ g. fst (fst (g A))` at
  `(U0 → Σ (Σ U0 U0) U0) → U0`, solvable by `X := A`.
* **A projection applied to arguments.** `λ g. fst (g X) A ≐ λ g. fst (g A) A` at
  `(U0 → Σ (U0 → U0) U0) → U0`, solvable by `X := A`.
* **An occurrence in a spine argument under an abstraction.** Over `A : U0, F : (U0 → U0) → U0`,
  `λ g. F g ≐ λ g. g (F g)` and `λ g. F g ≐ λ g. g (g (F g))` at `(U0 → U0) → U0`, unsolvable.

**Control.** A nested projection with different skeletons, `λ p. fst (fst p) ≐ λ p. snd (fst p)`, is
refuted by the head clash.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCensus.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentSpinesMany.Controls ContextualDependentFragmentDecisive.ClashControls
open ContextualDependentConstantHeads.Controls ContextualDependentConstantHeadsProjections.Controls

/-- A type over `A X : U0`, by its code. -/
abbrev typeAt (code : Tower.Tm 2)
    (accepted : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes code).isSome) :
    TypeOver twoTypes :=
  formedAt code accepted

/-! ## A spine at a flexible base type -/

/-- `(U0 → A) → A`. -/
def flexibleBase : TypeOver twoTypes :=
  typeAt (.pi (.pi (.head (.sort Tower.zero)) (.var 2)) (.var 2)) (by decide +kernel)

/-- `λ g. g X ≐ λ g. g A`. -/
def flexibleBaseStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 flexibleBase (.lam (.app (.var 0) (.var 1))) (by decide +kernel),
    at16 flexibleBase (.lam (.app (.var 0) (.var 2))) (by decide +kernel))]

theorem flexibleBase_in_fragment : InFragmentStore flexibleBaseStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem flexibleBase_suspended : (run projectionsOnly flexibleBaseStore 8).readout = .suspended := by decide +kernel

/-! ## Nested projections -/

/-- `(U0 → Σ (Σ U0 U0) U0) → U0`. -/
def nestedGenerator : TypeOver twoTypes :=
  typeAt (.pi (.pi (.head (.sort Tower.zero)) (.sigma (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
    (.head (.sort Tower.zero)))) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `λ g. fst (fst (g X)) ≐ λ g. fst (fst (g A))`. -/
def nestedStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 nestedGenerator (.lam (.fst (.fst (.app (.var 0) (.var 1))))) (by decide +kernel),
    at16 nestedGenerator (.lam (.fst (.fst (.app (.var 0) (.var 2))))) (by decide +kernel))]

theorem nested_in_fragment : InFragmentStore nestedStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem nested_suspended : (run projectionsOnly nestedStore 8).readout = .suspended := by decide +kernel

/-- `Σ (Σ U0 U0) U0 → U0`. -/
def nestedPairs : TypeOver twoTypes :=
  typeAt (.pi (.sigma (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))
    (.head (.sort Tower.zero))) (by decide +kernel)

/-- `λ p. fst (fst p) ≐ λ p. snd (fst p)`. -/
def nestedClashStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 nestedPairs (.lam (.fst (.fst (.var 0)))) (by decide +kernel),
    at16 nestedPairs (.lam (.snd (.fst (.var 0)))) (by decide +kernel))]

/-- **Control: different skeletons are refuted.** -/
theorem nestedClash_refuted : (run projectionsOnly nestedClashStore 8).readout = .refuted := by decide +kernel

/-! ## A projection applied to arguments -/

/-- `(U0 → Σ (U0 → U0) U0) → U0`. -/
def appliedGenerator : TypeOver twoTypes :=
  typeAt (.pi (.pi (.head (.sort Tower.zero)) (.sigma (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
    (.head (.sort Tower.zero)))) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `λ g. fst (g X) A ≐ λ g. fst (g A) A`. -/
def appliedStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 appliedGenerator (.lam (.app (.fst (.app (.var 0) (.var 1))) (.var 2))) (by decide +kernel),
    at16 appliedGenerator (.lam (.app (.fst (.app (.var 0) (.var 2))) (.var 2))) (by decide +kernel))]

theorem applied_in_fragment : InFragmentStore appliedStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem applied_suspended : (run projectionsOnly appliedStore 8).readout = .suspended := by decide +kernel

/-! ## An occurrence in a spine argument -/

theorem higher_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
    ContextualDependentInversion.Controls.typeContext
    (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `(U0 → U0) → U0`, over `A : U0`. -/
def higherType : TypeOver ContextualDependentInversion.Controls.typeContext :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 ContextualDependentInversion.Controls.typeContext
    (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))).get higher_formed).val

/-- `A : U0, F : (U0 → U0) → U0`. -/
abbrev withHigher := extend ContextualDependentInversion.Controls.typeContext higherType

theorem higherHere_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 withHigher
    (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `(U0 → U0) → U0`, over `A, F`. -/
def higherHere : TypeOver withHigher :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withHigher
    (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))).get
      higherHere_formed).val

/-- A checked term over `A, F` at a formed type. -/
def checkedHigher (type : TypeOver withHigher) (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 withHigher.raw code type.code).isSome = true) :
    TotalTerm withHigher :=
  ⟨type, ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 withHigher.raw code type.code).get accepted).down withHigher.formed type.isType⟩⟩

/-- `λ g. F g ≐ λ g. g (F g)`. -/
def argumentStore : EquationStore (TotalTerm withHigher) :=
  [(checkedHigher higherHere (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    checkedHigher higherHere (.lam (.app (.var 0) (.app (.var 1) (.var 0)))) (by decide +kernel))]

/-- `λ g. F g ≐ λ g. g (g (F g))`. -/
def deepArgumentStore : EquationStore (TotalTerm withHigher) :=
  [(checkedHigher higherHere (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    checkedHigher higherHere (.lam (.app (.var 0) (.app (.var 0) (.app (.var 1) (.var 0))))) (by decide +kernel))]

theorem argumentStore_length : argumentStore.length = 1 := rfl

def argumentEquation : Equation (TotalTerm withHigher) :=
  argumentStore.head (List.ne_nil_of_length_pos (by rw [argumentStore_length]; decide))

theorem argumentStore_eq : argumentStore = [argumentEquation] := rfl

theorem argument_in_fragment : InFragmentStore argumentStore := by
  rw [argumentStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl argumentEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem argument_suspended : (run projectionsOnly argumentStore 8).readout = .suspended := by decide +kernel
theorem deepArgument_suspended : (run projectionsOnly deepArgumentStore 8).readout = .suspended := by decide +kernel

end ContextualDependentCensus.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
