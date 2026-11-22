import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureDispatch

/-!
# Closure of the cumulative round: the rules that continue on a decomposed store

R94's rigid formers (`formerSearch`), η-expansion (`etaSearch`), the spine rule (`twoSearch`) and deep decomposition
(`deepSearch`) replace one equation by an equivalent store and continue there (`afterParts`): a rigid clash among the
pieces refutes, else R76's first rule runs, else R86's in-place rule runs, and the outcome is moved back.

An outcome moved back is stable as soon as the replacement is and the outcome on the pieces is
(`moveFound_stable`); R76's first rule is stable (`firstRule_stable`), so `afterParts` is stable whenever R86's in-place
rule is (`afterParts_stable`, under `InPlaceStable`). The replacements keep the class: R94's pieces through R116's
splice without normality hypotheses (`formerEquation_stable`), and the exchange of the two sides, whose annotations are
equal types under the solutions before it (`swapped_stable`). So the rigid formers and η-expansion keep the class
wherever the in-place rule is stable (`formerSearch_keeps_of_inPlace`, `etaSearch_keeps_of_inPlace`).
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
open ContextualDependentExecutableJoin ContextualDependentClosure
open ContextualDependentRigidFormers (moveFound parts_equivalent)

section Moved

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **An outcome moved back to the original store is stable** when the replacement and the outcome are. -/
theorem moveFound_stable {Θ : Context S.R} {problem parts : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent problem parts)
    (replace : StableKeeps ((Update.pending S.levels parts).rephrase same)) {found : Option (Found parts)}
    (stable : SolvedStable found) : SolvedStable (found.map (moveFound same)) := by
  intro update smaller fired
  cases found with
  | none => cases fired
  | some outcome =>
      cases outcome with
      | solved inner innerSmaller =>
          cases fired
          exact StableKeeps.then replace (stable inner innerSmaller rfl)
      | refuted absent => cases fired

/-- **Exchanging the two sides of an equation is stable** on a strongly normalizing package. -/
theorem swapped_stable (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    StableKeeps ((Update.pending S.levels (ContextualDependentEtaExpansion.swap equation :: rest)).rephrase
      (ContextualDependentEtaExpansion.swap_equivalent equation rest)) := by
  have empty := computation_empty rigid
  intro before permuted
  change PermutedMiller S.levels ((frames S.levels).applyStore (𝟙 Θ) before ++
    (ContextualDependentEtaExpansion.swap equation :: rest))
  rw [applyStore_identity]
  have front : PermutedMiller S.levels (equation :: (before ++ rest)) := permuted.perm List.perm_middle
  have spliced := front.splice_of (pieces := [ContextualDependentEtaExpansion.swap equation])
    fun before' after' stratified => by
      obtain ⟨sides, annotations⟩ := stratified before' after' equation rfl
      obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn sides
      refine StratifiedMiller.splice stratified
        (fun σ => (models_singleton σ _).trans (ContextualDependentEtaExpansion.solves_swap σ equation)) ?_ ?_
      · intro piece member
        rw [List.mem_singleton.mp member]
        exact sides_of_reducts empty rightReduct leftReduct
      · intro first last piece split
        rcases first with _ | ⟨one, first⟩
        · simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, -⟩ := split
          intro Δ σ solved
          rw [List.append_nil] at solved
          exact TypeEq.symm (annotations σ solved)
        · simp at split
  exact spliced.perm (by simpa using (List.perm_middle (a := ContextualDependentEtaExpansion.swap equation)
    (l₁ := before) (l₂ := rest)).symm)

end Moved

section After

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **R86's in-place rule is stable on every store**, at one budget. -/
def InPlaceStable (fuel : Nat) : Prop :=
  ∀ ⦃Θ : Context S.R⦄ (parts : EquationStore (TotalTerm Θ)),
    SolvedStable (ContextualDependentInPlace.inPlaceRule facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel parts)

/-- **A stable in-place rule keeps the class.** -/
theorem inPlace_keeps_of_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentInPlace.inPlaceRule facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted (inPlace problem)

variable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R)

include sn in
/-- **Continuing on an equivalent store is stable** when the replacement is and R86's in-place rule is. -/
theorem afterParts_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} {problem parts : EquationStore (TotalTerm Θ)} (same : (frames S.levels).Equivalent problem parts)
    (replace : StableKeeps ((Update.pending S.levels parts).rephrase same)) :
    SolvedStable (ContextualDependentRigidFormers.afterParts facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel parts same) := by
  intro update smaller fired
  unfold ContextualDependentRigidFormers.afterParts at fired
  split at fired
  · cases fired
  · split at fired
    · rename_i found computed
      have first : SolvedStable (some found) := by
        rw [← computed]
        exact firstRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel parts
      exact moveFound_stable same replace (found := some found) first update smaller fired
    · exact moveFound_stable same replace (inPlace parts) update smaller fired

include sn in
/-- **R94's rigid-former decomposition of one equation is stable** when R86's in-place rule is. -/
theorem formerEquation_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    SolvedStable (ContextualDependentRigidFormers.formerEquation facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal headTypingUnique fuel equation rest) := by
  intro update smaller fired
  unfold ContextualDependentRigidFormers.formerEquation at fired
  obtain ⟨parts, computed, fired⟩ := Option.bind_eq_some_iff.mp fired
  refine afterParts_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique sn fuel inPlace (parts_equivalent parts rest) ?_ update smaller fired
  intro before permuted
  change PermutedMiller S.levels ((frames S.levels).applyStore (𝟙 Θ) before ++ (parts.val ++ rest))
  rw [applyStore_identity]
  exact PermutedMiller.splice_underReducts rigid sn facts algebra permuted
    (formerParts_codes facts roots heads algebra complete declared choices reducer fuel computed) parts.val rfl
    fun σ => (parts.property σ).symm

include sn in
theorem formerSearch_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), SolvedStable (ContextualDependentRigidFormers.formerSearch facts roots
      heads algebra declared choices reducer rigid complete root normalizes certifyNormal headTypingUnique fuel problem)
  | [] => fun _ _ fired => by cases fired
  | equation :: rest => by
      intro update smaller fired
      simp only [ContextualDependentRigidFormers.formerSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact formerEquation_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel inPlace equation rest update smaller computed
      · exact solvedStable_keepLeft equation (formerSearch_stable fuel inPlace rest) update smaller fired

include sn in
/-- **R94's rigid formers keep the class** wherever R86's in-place rule is stable. -/
theorem formerSearch_keeps_of_inPlace (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentRigidFormers.formerSearch facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted
    (formerSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel inPlace problem)

include sn in
theorem etaEquation_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    SolvedStable (ContextualDependentEtaExpansion.etaEquation facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel equation rest) := by
  intro update smaller fired
  unfold ContextualDependentEtaExpansion.etaEquation at fired
  split at fired
  · exact afterParts_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel inPlace (ContextualDependentEtaExpansion.swap_equivalent equation rest)
      (swapped_stable rigid sn equation rest) update smaller fired
  · cases fired

include sn in
theorem etaSearch_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), SolvedStable (ContextualDependentEtaExpansion.etaSearch facts roots heads
      algebra declared choices reducer rigid complete root normalizes certifyNormal headTypingUnique fuel problem)
  | [] => fun _ _ fired => by cases fired
  | equation :: rest => by
      intro update smaller fired
      simp only [ContextualDependentEtaExpansion.etaSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact etaEquation_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel inPlace equation rest update smaller computed
      · exact solvedStable_keepLeft equation (etaSearch_stable fuel inPlace rest) update smaller fired

include sn in
/-- **η-expansion keeps the class** wherever R86's in-place rule is stable. -/
theorem etaSearch_keeps_of_inPlace (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentEtaExpansion.etaSearch facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted
    (etaSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel inPlace problem)

end After

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
