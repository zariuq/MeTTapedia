import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeControls

/-!
# The twin witness: a fragment store whose first progress leaves `StratifiedShort`

Over `A : U0, X : U0, F : X, K : Π A A`, the store `twinStore` is the single equation

`λ g. g (Π A A) (λ z. K z) ≐ λ g. g X F` at `Π (g : Π (T : U0). T → A). A`.

* It is in the dynamic pattern fragment (`twin_in_fragment`): the locals are rigid, `K` is applied to its one
  argument, and `X` and `F` have arity zero.
* The first round of the cumulative family, at budget 16, decomposes the local spine `g`. The residual store is
  `λ g. Π A A ≐ λ g. X` at `Π D U0`, then the twin `λ g. λ z. K z ≐ λ g. F` at `Π D (Π A A)` on the left and `Π D X` on
  the right. Opened at depth two, the twin's right side is `F z`: `F : X` takes one argument while its declaration has
  no Π binder. The residual store is neither `StratifiedShort` nor `Stratified`, and it is `StratifiedMiller`
  (`twin_first_round`).
* The family commits on the store (`twin_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentShortClosure.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentWorklist ContextualDependentClosure ContextualDependentInPlaceClosure
open ContextualDependentPatternFiring.Controls ContextualDependentCumulative.Controls

/-! ## Executable readings of opened sides -/

/-- A side's computed normal form, with Miller occurrences. -/
def sideMiller {Θ : Context setting.R} (count : Nat) (code : Tower.Tm (Θ.arity + count)) : Bool :=
  match ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | some result => (step Tower.rules (fun _ => none) result.val).isNone && miller (openedFlexible count) result.val
  | none => false

theorem sideMiller_sound {Θ : Context setting.R} {count : Nat} {code : Tower.Tm (Θ.arity + count)}
    (check : sideMiller (Θ := Θ) count code = true) :
    ∀ other, Star (R := Tower.rules) code other → Normal Tower.rules other → miller (openedFlexible count) other = true := by
  unfold sideMiller at check
  cases computed : ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | none =>
      rw [computed] at check
      cases check
  | some result =>
      rw [computed] at check
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at check
      intro other reduces normal
      have toResult := ContextualDependentExecutableConversion.normalize_star 64 computed
      have resultNormal := (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr check.1
      rw [normal_reduct_unique rfl toResult resultNormal reduces normal]
      exact check.2

/-- Both opened sides of an equation have Miller occurrences. -/
def sidesMiller {Θ : Context setting.R} (equation : Equation (TotalTerm Θ)) : Bool :=
  sideMiller (Θ := Θ) (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) &&
    sideMiller (Θ := Θ) (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code)

theorem sidesMiller_sound {Θ : Context setting.R} {equation : Equation (TotalTerm Θ)}
    (check : sidesMiller equation = true) : FragmentSidesMiller equation := by
  simp only [sidesMiller, Bool.and_eq_true] at check
  exact ⟨sideMiller_sound check.1, sideMiller_sound check.2⟩

/-- A side's computed normal form, with a metavariable outside the η-short arities or the Miller occurrences. -/
def sideOutsideShort {Θ : Context setting.R} (count : Nat) (code : Tower.Tm (Θ.arity + count)) : Bool :=
  match ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | some result => (step Tower.rules (fun _ => none) result.val).isNone &&
      !decide (InFragmentCodeShort Θ.raw count result.val)
  | none => false

theorem sideOutsideShort_spec {Θ : Context setting.R} {count : Nat} {code : Tower.Tm (Θ.arity + count)}
    (check : sideOutsideShort (Θ := Θ) count code = true) :
    ∃ other, Star (R := Tower.rules) code other ∧ Normal Tower.rules other ∧
      ¬ InFragmentCodeShort Θ.raw count other := by
  unfold sideOutsideShort at check
  cases computed : ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | none =>
      rw [computed] at check
      cases check
  | some result =>
      rw [computed] at check
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true', decide_eq_false_iff_not] at check
      exact ⟨result.val, ContextualDependentExecutableConversion.normalize_star 64 computed,
        (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr check.1, check.2⟩

theorem sideOutside_spec {Θ : Context setting.R} {count : Nat} {code : Tower.Tm (Θ.arity + count)}
    (check : sideOutside (Θ := Θ) count code = true) :
    ∃ other, Star (R := Tower.rules) code other ∧ Normal Tower.rules other ∧
      ¬ InFragmentCode Θ.raw count other := by
  unfold sideOutside at check
  cases computed : ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | none =>
      rw [computed] at check
      cases check
  | some result =>
      rw [computed] at check
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true', decide_eq_false_iff_not] at check
      exact ⟨result.val, ContextualDependentExecutableConversion.normalize_star 64 computed,
        (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr check.1, check.2⟩

/-- The shape of a twin after its domain equation `λ x. P ≐ λ x. Q` at `Π D U`. -/
def twinShape {Θ : Context setting.R} (first second : Equation (TotalTerm Θ)) : Bool :=
  match first.1.2.code, first.2.2.code, first.1.1.code with
  | .lam p, .lam x, .pi D (.head u) => decide (setting.R.isUniverse u) && decide (second.1.1.code = .pi D p) &&
      decide (second.2.1.code = .pi D x)
  | _, _, _ => false

theorem twinShape_sound {Θ : Context setting.R} {first second : Equation (TotalTerm Θ)}
    (check : twinShape first second = true) : StratifiedAt setting.levels [first] second := by
  unfold twinShape at check
  split at check
  next p x D u firstLeft firstRight firstType =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at check
      exact twin_stratifiedAt TowerModel.facts first second check.1.1 firstLeft firstRight firstType check.1.2 check.2
  next => cases check

/-- The residual store of the witness: two equations with Miller sides, the first with equal annotation codes, the
second a twin after it whose opened right side leaves both the η-short arities and the fragment. -/
def residualCheck {Θ : Context setting.R} : EquationStore (TotalTerm Θ) → Bool
  | [first, second] => sidesMiller first && sidesMiller second && decide (first.1.1.code = first.2.1.code) &&
      sideOutsideShort (Θ := Θ) (ContextualDependentPatternSolver.lamDepth second.1.2.code)
        (openCode (ContextualDependentPatternSolver.lamDepth second.1.2.code) second.2.2.code) &&
      sideOutside (Θ := Θ) (ContextualDependentPatternSolver.lamDepth second.1.2.code)
        (openCode (ContextualDependentPatternSolver.lamDepth second.1.2.code) second.2.2.code) &&
      twinShape first second
  | _ => false

theorem residual_of_check {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (check : residualCheck problem = true) :
    ¬ StratifiedShort setting.levels problem ∧ ¬ Stratified setting.levels problem ∧
      StratifiedMiller setting.levels problem := by
  match problem, check with
  | [first, second], check =>
      simp only [residualCheck, Bool.and_eq_true, decide_eq_true_eq] at check
      obtain ⟨⟨⟨⟨⟨millerFirst, millerSecond⟩, same⟩, outsideShort⟩, outside⟩, twin⟩ := check
      have split : [first, second] = [first] ++ second :: [] := rfl
      obtain ⟨code, reduces, normal, notShort⟩ := sideOutsideShort_spec outsideShort
      obtain ⟨code', reduces', normal', notFragment⟩ := sideOutside_spec outside
      exact ⟨not_stratifiedShort_of_right split reduces normal notShort,
        not_stratified_of_right split reduces' normal' notFragment,
        stratifiedMiller_pair first second (sidesMiller_sound millerFirst) (sidesMiller_sound millerSecond) same
          (twinShape_sound twin)⟩

/-! ## The witness -/

/-- `F : X`, over `A, X`. -/
def twinX : TypeOver withX := formIn withX (.var 0) (by decide +kernel)

/-- `A : U0, X : U0, F : X`. -/
abbrev withTwinF := extend withX twinX

/-- `K : Π A A`, over `A, X, F`. -/
def twinK : TypeOver withTwinF := formIn withTwinF (.pi (.var 2) (.var 3)) (by decide +kernel)

/-- `A : U0, X : U0, F : X, K : Π A A`. -/
abbrev withTwin := extend withTwinF twinK

/-- `Π (g : Π (T : U0). T → A). A`. -/
def twinAnnotation : TypeOver withTwin :=
  formIn withTwin (.pi (.pi (.head (.sort Tower.zero)) (.pi (.var 0) (.var 5))) (.var 4)) (by decide +kernel)

/-- `λ g. g (Π A A) (λ z. K z) ≐ λ g. g X F`. -/
def twinSource : Equation (TotalTerm withTwin) :=
  (termIn withTwin twinAnnotation
      (.lam (.app (.app (.var 0) (.pi (.var 4) (.var 5))) (.lam (.app (.var 2) (.var 0))))) (by decide +kernel),
    termIn withTwin twinAnnotation (.lam (.app (.app (.var 0) (.var 3)) (.var 2))) (by decide +kernel))

/-- **The twin witness store.** -/
def twinStore : EquationStore (TotalTerm withTwin) := [twinSource]

theorem twinSource_in_fragment : InFragment twinSource := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl twinSource.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The witness is in the dynamic pattern fragment.** -/
theorem twin_in_fragment : InFragmentStore twinStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  exact twinSource_in_fragment

noncomputable def firstRoundCheck : Bool :=
  match run cumulativeOnly twinStore 1 with
  | .cutoff state => residualCheck state.remaining
  | _ => false

theorem firstRoundCheck_true : firstRoundCheck = true := by decide +kernel

/-- **The first progress of the cumulative family leaves `StratifiedShort` and `Stratified`, and stays in
`StratifiedMiller`.** At budget 16 the first round on the fragment store `twinStore` is a progress (the run of one
round is cut off at an update), and its residual store is outside both classes and inside the Miller class. -/
theorem twin_first_round :
    ∃ state : ContextualDependentUpdate.Update setting.levels twinStore,
      run cumulativeOnly twinStore 1 = .cutoff state ∧
      ¬ StratifiedShort setting.levels state.remaining ∧ ¬ Stratified setting.levels state.remaining ∧
      StratifiedMiller setting.levels state.remaining := by
  have key := firstRoundCheck_true
  unfold firstRoundCheck at key
  generalize ran : run cumulativeOnly twinStore 1 = outcome at key
  cases outcome with
  | cutoff state => exact ⟨state, rfl, residual_of_check key⟩
  | solved _ _ => simp at key
  | refuted _ => simp at key
  | stuck _ => simp at key

/-- The first round at a budget leaves `StratifiedShort` and `Stratified`, into the Miller class. -/
noncomputable def firstRoundCheckAt (budget : Nat) : Bool :=
  match run (cumulativeTower.solver budget) twinStore 1 with
  | .cutoff state => residualCheck state.remaining
  | _ => false

theorem firstRoundCheckAt_true : ∀ budget ∈ [17, 24, 32, 64], firstRoundCheckAt budget = true := by
  decide +kernel

/-- **The same at larger budgets**: at budgets 17, 24, 32 and 64 the first progress on the witness also leaves
`StratifiedShort` and `Stratified` into the Miller class. This is evidence at these budgets, not a statement about
every budget. -/
theorem twin_first_round_at {budget : Nat} (listed : budget ∈ [17, 24, 32, 64]) :
    ∃ state : ContextualDependentUpdate.Update setting.levels twinStore,
      run (cumulativeTower.solver budget) twinStore 1 = .cutoff state ∧
      ¬ StratifiedShort setting.levels state.remaining ∧ ¬ Stratified setting.levels state.remaining ∧
      StratifiedMiller setting.levels state.remaining := by
  have key := firstRoundCheckAt_true budget listed
  unfold firstRoundCheckAt at key
  generalize ran : run (cumulativeTower.solver budget) twinStore 1 = outcome at key
  cases outcome with
  | cutoff state => exact ⟨state, rfl, residual_of_check key⟩
  | solved _ _ => simp at key
  | refuted _ => simp at key
  | stuck _ => simp at key

/-- **The cumulative family commits on the witness.** -/
theorem twin_committed : (run cumulativeOnly twinStore 8).readout = .commit := by decide +kernel

end ContextualDependentShortClosure.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
