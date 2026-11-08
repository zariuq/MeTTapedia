import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureElims

/-!
# Closure of the cumulative round: R75's dispatcher

R75's dispatcher (`ContextualDependentDispatch.search`) looks for an equation `X ≐ t` at the newest declaration `X`,
in either orientation, after aligning both annotations with `X`'s type (`align`). It recovers `t` without `X`
(`recoverRight`: by direct strengthening, or by strengthening the reducer's result), defines `X := t`, instantiates the
rest of the store and runs the conversion scan (`ContextualDependentFlex.solveNewest`).

On a strongly normalizing package without root computation, and with a reducer whose results are reducts:

* the recovered value has a closed normal Miller reduct, since its weakening is a reduct of `t` (`body_reduct`,
  `recoverRight_reduces`), so the definition is an answer reducing to a pattern answer (`instantiate_reducing`);
* the defined equation holds under the definition at every substitution (`definition_valid`), so the definition is a
  drop (`solveNewest_stable`);
* the conversion scan drops only valid equations, from any position (`PermutedMiller.filter_valid_after`,
  `conversion_stable`);
* the alignment and the swap replace an equation by one with its solutions, its codes and one annotation
  (`orient_stable`).

So the dispatcher keeps the class (`dispatch_keeps`), which completes R99's decomposition round. The tower's reducer is
the executable normalizer, whose results are reducts (`normalize_star`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentHereditary
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Dropping valid equations anywhere -/

section Drop

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Dropping one valid equation keeps the permuted class.** -/
theorem PermutedMiller.drop_valid {Θ : Context S.R} {before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)}
    (valid : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (frames S.levels).Solves σ equation)
    (permuted : PermutedMiller S.levels (before ++ equation :: after)) : PermutedMiller S.levels (before ++ after) := by
  have front : PermutedMiller S.levels (equation :: (before ++ after)) := permuted.perm List.perm_middle
  have spliced := front.splice_of (pieces := []) fun _ _ stratified =>
    StratifiedMiller.splice stratified (fun σ => ⟨fun _ => valid σ, fun _ _ member => by cases member⟩)
      (fun _ member => by cases member) (fun first last piece split => by simp at split)
  simpa using spliced

/-- **Dropping valid equations after a fixed prefix keeps the permuted class.** -/
theorem PermutedMiller.filter_valid_after {Θ : Context S.R} (keep : Equation (TotalTerm Θ) → Bool)
    (valid : ∀ equation, keep equation = false → ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Solves σ equation) :
    ∀ (problem before : EquationStore (TotalTerm Θ)), PermutedMiller S.levels (before ++ problem) →
      PermutedMiller S.levels (before ++ problem.filter keep)
  | [], before, permuted => by simpa using permuted
  | equation :: rest, before, permuted => by
      by_cases kept : keep equation = true
      · rw [List.filter_cons_of_pos kept]
        have moved := PermutedMiller.filter_valid_after keep valid rest (before ++ [equation])
          (by simpa using permuted)
        simpa using moved
      · rw [List.filter_cons_of_neg kept]
        exact PermutedMiller.filter_valid_after keep valid rest before
          (PermutedMiller.drop_valid (fun σ => valid equation (by simpa using kept) σ) permuted)

end Drop

/-! ## Recovered values -/

section Values

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A value whose weakening is a reduct of a code with a closed normal Miller reduct has one too.** -/
theorem body_reduct (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Γ : Context S.R} {type : TypeOver Γ}
    (body : Term Γ type) {code : Tm Head (Γ.arity + 1)}
    (reduces : Star (R := S.R) code (Presentation.rename wk body.code))
    (closed : MarkedReduct S.R (fun _ => true) code) : MarkedReduct S.R (fun _ => true) body.code := by
  have empty := computation_empty rigid
  obtain ⟨N, toN, normalN⟩ := ContextualDependentOpenedNormal.term_normal sn body
  have renamed := star_rename (R := S.R) wk toN
  have normalRenamed : Normal S.R (Presentation.rename wk N) :=
    (ContextualDependentNormalizing.normal_rename_iff empty wk N).mpr normalN
  have millerRenamed := all_miller_of_one empty closed _ (reduces.trans renamed) normalRenamed
  exact ⟨N, toN, normalN, miller_rename_reflect N (Fin.succ_injective _) (fun _ => rfl) millerRenamed⟩

/-- **A definition by a value with a closed normal Miller reduct reduces to a pattern answer.** -/
theorem instantiate_reducing {Γ : Context S.R} {type : TypeOver Γ} (value : Term Γ type)
    (closed : MarkedReduct S.R (fun _ => true) value.code) :
    ReducingAnswer S.R (Elimination.instantiate Γ value).substitution := by
  obtain ⟨N, toN, normalN, millerN⟩ := closed
  refine ⟨consSub N Presentation.ids, fun i => ?_, ⟨?_⟩⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · change Star (R := S.R) (value.cast type.reindex_id.symm).code N
      rw [Term.cast_code]
      exact toN
    · exact .refl
  · exact
      { target := 0
        flexibleTarget := rfl
        rename := fun i hi => i.pred hi
        injective := fun i j hi hj same => (Fin.pred_inj).mp same
        respects := fun _ _ => rfl
        others := fun i hi => by
          obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
          simp [Presentation.ids]
        outerArity := Γ.arity
        outer := idRen
        outerInjective := fun _ _ same => same
        outerFlexible := fun _ => rfl
        value := N
        solution := by simp
        valueMiller := millerN
        valueNormal := normalN }

/-- **The defined equation holds under the definition at every substitution.** -/
theorem definition_valid {Γ : Context S.R} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (leftIsVariable : (frames S.levels).E (⟨_, left⟩ : TotalTerm _) (Elimination.last Γ type))
    (body : Term Γ type)
    (solves : (frames S.levels).E (TotalTerm.reindex (⟨type, body⟩ : TotalTerm Γ) (projectionHom Γ type))
      (⟨_, right⟩ : TotalTerm (extend Γ type)))
    {Δ : Context S.R} (τ : Δ ⟶ Γ) :
    (frames S.levels).Solves τ
      (TotalTerm.reindex (⟨_, left⟩ : TotalTerm (extend Γ type)) (Elimination.instantiate Γ body),
        TotalTerm.reindex (⟨_, right⟩ : TotalTerm (extend Γ type)) (Elimination.instantiate Γ body)) := by
  have first : (frames S.levels).E
      (TotalTerm.reindex (⟨_, left⟩ : TotalTerm (extend Γ type)) (Elimination.instantiate Γ body))
      ((Elimination.last Γ type).reindex (Elimination.instantiate Γ body)) :=
    (frames S.levels).preserves (Elimination.instantiate Γ body) leftIsVariable
  have second : (frames S.levels).E
      ((TotalTerm.reindex (⟨type, body⟩ : TotalTerm Γ) (projectionHom Γ type)).reindex
        (Elimination.instantiate Γ body))
      (TotalTerm.reindex (⟨_, right⟩ : TotalTerm (extend Γ type)) (Elimination.instantiate Γ body)) :=
    (frames S.levels).preserves (Elimination.instantiate Γ body) solves
  rw [Elimination.instantiate_last] at first
  rw [Elimination.instantiate_value] at second
  exact (frames S.levels).preserves τ (((frames S.levels).equivalence Γ).trans first second)

end Values

/-! ## The dispatcher -/

section Dispatch

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

omit [DecidableRel S.R.cumulative] in
/-- **The conversion scan is stable**: it drops only valid equations, after any prefix. -/
theorem conversion_stable (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    StableKeeps (ContextualDependentUpdate.conversion facts roots heads algebra reducer fuel problem) := by
  intro before permuted
  change PermutedMiller S.levels ((frames S.levels).applyStore (𝟙 Γ) before ++
    Conversion.scan facts roots heads algebra reducer fuel problem)
  rw [applyStore_identity, scan_eq_filter]
  refine PermutedMiller.filter_valid_after _ (fun equation dropped Δ σ => ?_) problem before permuted
  cases checked : Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2 with
  | none => simp [checked] at dropped
  | some certificate => exact (frames S.levels).preserves σ certificate.down

variable (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
  reducer fuel term = some result → Star (R := S.R) term result.val)

include directed in
/-- **A recovered value's weakening is a reduct of the recovered side.** -/
theorem recoverRight_reduces (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ}
    (right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    {recovered : ContextualDependentProjectionInversion.Recovery S.levels (projectionHom Γ type) type
      (⟨_, right⟩ : TotalTerm (extend Γ type))}
    (found : ContextualDependentFlex.recoverRight facts roots heads algebra declared choices reducer fuel right =
      some recovered) :
    Star (R := S.R) right.code (Presentation.rename wk recovered.body.code) := by
  unfold ContextualDependentFlex.recoverRight at found
  split at found
  · rename_i direct _
    cases found
    change Star (R := S.R) right.code (Presentation.rename (ContextualDependentFlex.withoutNewest Γ type).forward
      direct.body.code)
    rw [direct.recovers]
  · obtain ⟨projected, computed, same⟩ := Option.bind_eq_some_iff.mp found
    cases same
    unfold ContextualDependentProjectionInversion.recover at computed
    obtain ⟨normal, normalComputed, computed⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨proposed, _, computed⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨checked, _, computed⟩ := Option.bind_eq_some_iff.mp computed
    cases computed
    have toNormal := directed fuel _ normal normalComputed
    change Star (R := S.R) right.code (Presentation.rename (ContextualDependentFlex.withoutNewest Γ type).forward
      proposed.body.code)
    rw [proposed.recovers]
    change Star (R := S.R) (subst Presentation.ids right.code) normal.val at toNormal
    rwa [subst_ids] at toNormal

variable (rigid : ∀ name, S.roles name = .rigid) (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R)
include directed rigid sn

/-- **R75's flexible-variable rule is stable** on an equation with Miller sides. -/
theorem solveNewest_stable (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (sides : FragmentSidesMiller (ContextualDependentFlex.equation left right))
    {update : Update S.levels (ContextualDependentFlex.equation left right :: rest)}
    (found : ContextualDependentFlex.solveNewest facts roots heads algebra declared choices reducer fuel left right
      rest = some update) :
    StableKeeps update := by
  unfold ContextualDependentFlex.solveNewest at found
  obtain ⟨leftIsVariable, _, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨recovered, recoveredComputed, found⟩ := Option.bind_eq_some_iff.mp found
  cases found
  have bodyClosed := body_reduct rigid sn recovered.body
    (recoverRight_reduces facts roots heads algebra declared choices reducer directed fuel right recoveredComputed)
    (side_reduct rigid sn sides).2
  refine StableKeeps.then (stableKeeps_of_reducingDrop rigid sn
    ⟨ContextualDependentFlex.equation left right, rest, List.Perm.refl _, rfl,
      fun τ => definition_valid left right leftIsVariable.down recovered.body recovered.solves τ,
      instantiate_reducing recovered.body bodyClosed⟩)
    (conversion_stable facts roots heads algebra reducer fuel _)

omit directed rigid sn [DecidableRel S.R.cumulative] in
theorem align_codes (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) (original : Equation (TotalTerm Γ))
    {aligned : ContextualDependentDispatch.Aligned S.levels type original}
    (found : ContextualDependentDispatch.align facts roots heads algebra reducer fuel type original = some aligned) :
    aligned.left.code = original.1.2.code ∧ aligned.right.code = original.2.2.code := by
  unfold ContextualDependentDispatch.align at found
  obtain ⟨first, _, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨second, _, found⟩ := Option.bind_eq_some_iff.mp found
  cases found
  exact ⟨rfl, rfl⟩

/-- **R75's oriented rule is stable** on an equation with Miller sides. -/
theorem orient_stable (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (original : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type)))
    (sides : FragmentSidesMiller original) {update : Update S.levels (original :: rest)}
    (found : ContextualDependentDispatch.orient facts roots heads algebra declared choices reducer fuel type original
      rest = some update) :
    StableKeeps update := by
  have empty := computation_empty rigid
  obtain ⟨originalLeft, originalRight⟩ := side_reduct rigid sn sides
  unfold ContextualDependentDispatch.orient at found
  obtain ⟨aligned, alignedComputed, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨leftCode, rightCode⟩ := align_codes facts roots heads algebra reducer fuel _ original alignedComputed
  have leftReduct : MarkedReduct S.R (fun _ => true) aligned.left.code := by
    rw [leftCode]
    exact originalLeft
  have rightReduct : MarkedReduct S.R (fun _ => true) aligned.right.code := by
    rw [rightCode]
    exact originalRight
  split at found
  · rename_i updated computed
    cases found
    intro before permuted
    have replaced := replaced_stable [ContextualDependentFlex.equation aligned.left aligned.right]
      (fun σ => ((aligned.models_iff [] _ σ).symm.trans (models_singleton σ original)))
      (fun piece member => by
        rw [List.mem_singleton.mp member]
        exact sides_of_reducts empty leftReduct rightReduct)
      (fun piece member => by
        rw [List.mem_singleton.mp member]
        rfl)
      (aligned.models_iff rest) before permuted
    change PermutedMiller S.levels ((frames S.levels).applyStore (𝟙 (extend Γ type)) before ++
      ([ContextualDependentFlex.equation aligned.left aligned.right] ++ rest)) at replaced
    rw [applyStore_identity] at replaced
    exact solveNewest_stable facts roots heads algebra declared choices reducer directed rigid sn fuel aligned.left
      aligned.right rest (sides_of_reducts empty leftReduct rightReduct) computed before replaced
  · obtain ⟨updated, computed, same⟩ := Option.bind_eq_some_iff.mp found
    cases same
    intro before permuted
    have swapped : ∀ (later : EquationStore (TotalTerm (extend Γ type))), (frames S.levels).Equivalent
        (original :: later) (ContextualDependentFlex.equation aligned.right aligned.left :: later) :=
      fun later Δ solution => (aligned.models_iff later Δ solution).trans
        (ContextualDependentDispatch.swap_models (levels := S.levels) ⟨_, aligned.left⟩ ⟨_, aligned.right⟩ later Δ
          solution)
    have replaced := replaced_stable [ContextualDependentFlex.equation aligned.right aligned.left]
      (fun σ => ((swapped [] _ σ).symm.trans (models_singleton σ original)))
      (fun piece member => by
        rw [List.mem_singleton.mp member]
        exact sides_of_reducts empty rightReduct leftReduct)
      (fun piece member => by
        rw [List.mem_singleton.mp member]
        rfl)
      (swapped rest) before permuted
    change PermutedMiller S.levels ((frames S.levels).applyStore (𝟙 (extend Γ type)) before ++
      ([ContextualDependentFlex.equation aligned.right aligned.left] ++ rest)) at replaced
    rw [applyStore_identity] at replaced
    exact solveNewest_stable facts roots heads algebra declared choices reducer directed rigid sn fuel aligned.right
      aligned.left rest (sides_of_reducts empty rightReduct leftReduct) computed before replaced

/-- **R75's dispatcher search is stable** on stores with Miller sides. -/
theorem search_stable (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      ∀ update, ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel type
        problem = some update → StableKeeps update
  | [], _, _, found => by cases found
  | original :: rest, sides, update, found => by
      simp only [ContextualDependentDispatch.search] at found
      split at found
      · rename_i updated computed
        cases found
        exact orient_stable facts roots heads algebra declared choices reducer directed rigid sn fuel type original rest
          (sides original List.mem_cons_self) computed
      · obtain ⟨inner, innerComputed, same⟩ := Option.bind_eq_some_iff.mp found
        cases same
        exact StableKeeps.keepLeft original (search_stable fuel type rest
          (fun other member => sides other (List.mem_cons_of_mem _ member)) inner innerComputed)

/-- **R75's dispatcher keeps the permuted class** on a strongly normalizing package with a directed reducer. -/
theorem dispatch_keeps (fuel : Nat) : DispatchKeeps facts roots heads algebra declared choices reducer fuel :=
  fun type problem permuted updated found =>
    (search_stable facts roots heads algebra declared choices reducer directed rigid sn fuel type problem
      (fun _ member => permuted.sides_of_mem member) updated found).keeps permuted

end Dispatch

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
