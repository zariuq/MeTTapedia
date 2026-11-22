import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureRotate

/-!
# Closure of the cumulative round: updates that keep the class under any prefix

Several rules chain updates (prune, then exchange, then solve) and search the store keeping earlier equations in
front. An update **keeps the class stably** (`StableKeeps`) when, for every prefix of equations kept in front, the
instantiated prefix followed by the residual store is in the permuted class whenever the prefix followed by the store
is. Stable updates compose (`StableKeeps.then`), survive keeping an equation in front (`StableKeeps.keepLeft`), and
include:

* every reindexing of the whole store along an answer that reduces to a pattern answer (`stableKeeps_applyStore`),
  such as R76's pruning (`prune_stable`) and the exchange of independent metavariables (`exchange_stable`);
* every drop under such an answer (`stableKeeps_of_reducingDrop`).

A stable update with the empty prefix keeps the class (`StableKeeps.keeps`).
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
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentHereditary
open ContextualDependentDynamicFragment

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **An update keeps the permuted class under every prefix.** -/
def StableKeeps {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (update : Update S.levels problem) : Prop :=
  ∀ before : EquationStore (TotalTerm Θ), PermutedMiller S.levels (before ++ problem) →
    PermutedMiller S.levels ((frames S.levels).applyStore update.answer before ++ update.remaining)

theorem StableKeeps.keeps {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (stable : StableKeeps update) (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels update.remaining :=
  stable [] permuted

theorem StableKeeps.then {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {first : Update S.levels problem}
    {second : Update S.levels first.remaining} (keepsFirst : StableKeeps first) (keepsSecond : StableKeeps second) :
    StableKeeps (first.then second) := by
  intro before permuted
  have middle := keepsSecond _ (keepsFirst before permuted)
  change PermutedMiller S.levels
    ((frames S.levels).applyStore (second.answer ≫ first.answer) before ++ second.remaining)
  rw [← applyStore_comp]
  exact middle

theorem StableKeeps.keepLeft {Θ : Context S.R} {rest : EquationStore (TotalTerm Θ)} (equation : Equation (TotalTerm Θ))
    {update : Update S.levels rest} (stable : StableKeeps update) : StableKeeps (update.keepLeft [equation]) := by
  intro before permuted
  have moved := stable (before ++ [equation]) (by simpa only [List.append_assoc, List.singleton_append] using permuted)
  change PermutedMiller S.levels ((frames S.levels).applyStore update.answer before ++
    ((frames S.levels).applyStore update.answer [equation] ++ update.remaining))
  simpa only [Interface.Frames.applyStore, List.map_append, List.append_assoc] using moved

/-- **Reindexing the whole store along an answer that reduces to a pattern answer is stable.** -/
theorem stableKeeps_applyStore (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (update : Update S.levels problem)
    (remaining : update.remaining = (frames S.levels).applyStore update.answer problem)
    (answer : ReducingAnswer S.R update.answer.substitution) : StableKeeps update := by
  intro before permuted
  rw [remaining]
  have moved := ContextualDependentCumulativeClosure.PermutedMiller.applyStore_of_sides update.answer permuted
    fun equation member => fragmentSidesMiller_reindex_reducing (computation_empty rigid) update.answer answer
      (permuted.sides_of_mem member)
      (ContextualDependentOpenedNormal.openedNormal_of_sn (computation_empty rigid) sn _ equation member).1
      (ContextualDependentOpenedNormal.openedNormal_of_sn (computation_empty rigid) sn _ equation member).2
  simpa only [Interface.Frames.applyStore, List.map_append] using moved

/-- **A drop under an answer that reduces to a pattern answer is stable.** -/
theorem stableKeeps_of_reducingDrop (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem} (drops : ReducingDrop problem update) :
    StableKeeps update := by
  intro before permuted
  obtain ⟨first, rest, perm, remaining, valid, answer⟩ := drops
  rw [remaining]
  have whole : (first :: (before ++ rest)).Perm (before ++ problem) :=
    List.perm_middle.symm.trans (List.Perm.append_left before perm)
  have moved := permutedMiller_reducing_drop (computation_empty rigid) update.answer answer
    (permuted.perm whole.symm)
    (fun equation member => ContextualDependentOpenedNormal.openedNormal_of_sn (computation_empty rigid) sn _ equation
      member) valid
  simpa only [Interface.Frames.applyStore, List.map_append] using moved

/-- A pattern answer reduces to itself. -/
theorem ReducingAnswer.of_pattern {n m : Nat} {σ : Sub Head n m}
    (answer : PatternAnswer S.R (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) σ) : ReducingAnswer S.R σ :=
  ⟨σ, fun _ => .refl, ⟨answer⟩⟩

/-- **R76's pruning is stable.** -/
theorem prune_stable (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Γ : Context S.R} {type keptType : TypeOver Γ}
    {spine : ContextualDependentPiSpine.Spine type} {kept : ContextualDependentPiSpine.Spine keptType}
    (restriction : ContextualDependentPrune.Restriction spine kept)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    ∀ forced, StableKeeps (ContextualDependentPrune.prune S.levels restriction problem forced) :=
  fun _ => stableKeeps_applyStore rigid sn _ rfl (.of_pattern (pruneAnswer (computation_empty rigid) restriction))

/-- **The exchange of independent metavariables is stable.** -/
theorem exchange_stable (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Γ : Context S.R} (first next : TypeOver Γ)
    (problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))) :
    StableKeeps (ContextualDependentPrune.exchange S.levels first next problem) := by
  have renames : ∀ i, (ContextualDependentParameterExchange.swap next first).substitution i = .var (swapRen i) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact ContextualDependentParameterExchange.swap_zero next first
    · exact ContextualDependentParameterExchange.swap_one next first
    · exact ContextualDependentParameterExchange.swap_older next first i
  exact stableKeeps_applyStore rigid sn _ rfl
    (.of_pattern (PatternAnswer.ofRenaming (computation_empty rigid) swapRen swapRen_injective renames 0))

/-- **Every solved outcome of a rule is stable.** -/
def SolvedStable {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (found : Option (Found problem)) : Prop :=
  ∀ update smaller, found = some (.solved update smaller) → StableKeeps update

theorem foundKeeps_of_stable {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {found : Option (Found problem)}
    (permuted : PermutedMiller S.levels problem) (stable : SolvedStable found) :
    FoundKeeps (fun problem => PermutedMiller S.levels problem) found :=
  fun update smaller fired => (stable update smaller fired).keeps permuted

theorem solvedStable_keepLeft {Θ : Context S.R} {rest : EquationStore (TotalTerm Θ)} (equation : Equation (TotalTerm Θ))
    {found : Option (Found rest)} (stable : SolvedStable found) : SolvedStable (found.map (Found.keepLeft equation)) := by
  intro update smaller fired
  obtain ⟨inner, computed, same⟩ := Option.map_eq_some_iff.mp fired
  cases inner with
  | solved moved movedSmaller =>
      cases same
      exact (stable moved movedSmaller computed).keepLeft equation
  | refuted absent => cases same

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
