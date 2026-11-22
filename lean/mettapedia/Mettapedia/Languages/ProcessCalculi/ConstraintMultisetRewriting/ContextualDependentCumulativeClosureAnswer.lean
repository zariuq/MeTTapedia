import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4Rules

/-!
# Closure of the cumulative round: dropping an equation under an answer with a normal reduct

R116's and R119's closure under answer-and-drop asks the answer to be a **pattern answer**: one metavariable solved by
a normal term with Miller occurrences. The solver's pattern rules answer `F := λ z̄. u` with `u` read off the right
side, which need not be normal. This file closes the class under answers that **reduce pointwise** to a pattern answer
(`ReducingAnswer`):

* the instantiated sides reduce to the sides instantiated by the pattern answer, so they share its normal forms, and
  R116's hereditary substitution gives those Miller occurrences (`fragmentSidesMiller_reindex_reducing`);
* the stratified annotations move along any context morphism (`stratifiedMiller_applyStore_of_sides`);
* so dropping an equation that the answer makes valid keeps the permuted class (`permutedMiller_reducing_drop`,
  `permutedMiller_of_reducingDrop`).

The newest metavariable answered by a value with a normal reduct of Miller occurrences is such an answer
(`newestReducing`). Drops survive keeping an equation in front (`ReducingDrop.keepLeft`) and the transport to the
newest declaration (`throughNewest_drops`).
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
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentClosure
open ContextualDependentDynamicFragment ContextualDependentHereditary ExecutableReduction
open ContextualDependentExecutableJoin

/-! ## Answers that reduce to pattern answers -/

section Answers

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **An answer that reduces pointwise to a pattern answer.** -/
def ReducingAnswer (rules : Rules Head) {n m : Nat} (σ : Sub Head n m) : Prop :=
  ∃ σ' : Sub Head n m, (∀ i, Star (R := rules) (σ i) (σ' i)) ∧
    Nonempty (PatternAnswer rules (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) σ')

/-- **Miller sides under an answer that reduces to a pattern answer.** -/
theorem fragmentSidesMiller_reindex_reducing (empty : rules.computation = RootComputation.empty) {Θ Δ : Context rules}
    (σ : Δ ⟶ Θ) (answer : ReducingAnswer rules σ.substitution) {equation : Equation (TotalTerm Θ)}
    (sides : FragmentSidesMiller equation)
    (normalLeft : ∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) equation.1.2.code) opened ∧
      Normal rules opened)
    (normalRight : ∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) equation.2.2.code) opened ∧
      Normal rules opened) :
    FragmentSidesMiller (equation.1.reindex σ, equation.2.reindex σ) := by
  obtain ⟨σ', reduces, ⟨pattern⟩⟩ := answer
  have side : ∀ {code : Tm Head Θ.arity},
      (∀ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) code) opened → Normal rules opened →
        miller (openedFlexible (lamDepth equation.1.2.code)) opened = true) →
      (∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) code) opened ∧ Normal rules opened) →
      ∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) (subst σ.substitution code)) opened ∧
        Normal rules opened ∧ miller (openedFlexible (lamDepth equation.1.2.code)) opened = true := by
    intro code inside normalizes
    obtain ⟨N, toN, normalN, millerN⟩ := answered_side_miller empty pattern _ inside normalizes
    exact ⟨N, (ContextualDependentOpenedNormal.star_openCode (star_substitute reduces code) _).trans toN, normalN,
      millerN⟩
  unfold FragmentSidesMiller
  change (∀ code, Star (R := rules) (openCode (lamDepth (subst σ.substitution equation.1.2.code))
        (subst σ.substitution equation.1.2.code)) code → Normal rules code →
      miller (openedFlexible (lamDepth (subst σ.substitution equation.1.2.code))) code = true) ∧
    (∀ code, Star (R := rules) (openCode (lamDepth (subst σ.substitution equation.1.2.code))
        (subst σ.substitution equation.2.2.code)) code → Normal rules code →
      miller (openedFlexible (lamDepth (subst σ.substitution equation.1.2.code))) code = true)
  obtain ⟨k, deeper⟩ := Nat.exists_eq_add_of_le (lamDepth_le_subst σ.substitution equation.1.2.code)
  rw [deeper]
  exact ⟨all_miller_of_one empty (miller_deeper empty k (side sides.1 normalLeft)),
    all_miller_of_one empty (miller_deeper empty k (side sides.2 normalRight))⟩

/-- **Dropping an equation under an answer that reduces to a pattern answer keeps the permuted class**, wherever the
equation sits in the stratified order. -/
theorem permutedMiller_reducing_drop (empty : rules.computation = RootComputation.empty) {Θ Δ : Context rules}
    (σ : Δ ⟶ Θ) (answer : ReducingAnswer rules σ.substitution) {first : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller levels (first :: rest))
    (normalizes : ∀ equation ∈ first :: rest,
      (∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) equation.1.2.code) opened ∧
        Normal rules opened) ∧
      (∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) equation.2.2.code) opened ∧
        Normal rules opened))
    (valid : ∀ {Δ' : Context rules} (τ : Δ' ⟶ Δ), (frames levels).Solves τ (first.1.reindex σ, first.2.reindex σ)) :
    PermutedMiller levels ((frames levels).applyStore σ rest) := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  obtain ⟨before, after, rfl⟩ := List.append_of_mem (perm.symm.subset List.mem_cons_self)
  have restPerm : (before ++ after).Perm rest := (List.perm_middle.symm.trans perm).cons_inv
  have applied := stratifiedMiller_applyStore_of_sides σ stratified fun equation member =>
    fragmentSidesMiller_reindex_reducing empty σ answer (StratifiedMiller.sides_of_mem stratified member)
      (normalizes equation (perm.subset member)).1 (normalizes equation (perm.subset member)).2
  have split : (frames levels).applyStore σ (before ++ first :: after) =
      (frames levels).applyStore σ before ++ (first.1.reindex σ, first.2.reindex σ) ::
        (frames levels).applyStore σ after := by
    simp only [Interface.Frames.applyStore, List.map_append, List.map_cons]
    rfl
  rw [split] at applied
  refine ⟨_, ?_, stratifiedMiller_drop applied valid⟩
  have mapped := restPerm.map fun equation : Equation (TotalTerm Θ) => (equation.1.reindex σ, equation.2.reindex σ)
  simp only [List.map_append] at mapped
  exact mapped

end Answers

/-! ## Drops, through the solver's plumbing -/

section Drops

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **An update drops an equation of the store under an answer that reduces to a pattern answer.** -/
def ReducingDrop {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem) : Prop :=
  ∃ (first : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)),
    (first :: rest).Perm problem ∧ update.remaining = (frames S.levels).applyStore update.answer rest ∧
    (∀ {Δ : Context S.R} (τ : Δ ⟶ update.target),
      (frames S.levels).Solves τ (first.1.reindex update.answer, first.2.reindex update.answer)) ∧
    ReducingAnswer S.R update.answer.substitution

/-- **A drop under a reducing answer keeps the permuted class** on a strongly normalizing package. -/
theorem permutedMiller_of_reducingDrop (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (permuted : PermutedMiller S.levels problem) (drops : ReducingDrop problem update) :
    PermutedMiller S.levels update.remaining := by
  obtain ⟨first, rest, perm, remaining, valid, answer⟩ := drops
  rw [remaining]
  exact permutedMiller_reducing_drop (computation_empty rigid) update.answer answer (permuted.perm perm.symm)
    (fun equation member => ContextualDependentOpenedNormal.openedNormal_of_sn (computation_empty rigid) sn
      (first :: rest) equation member) valid

/-- **Every solved outcome of a rule drops an equation under a reducing answer.** -/
def SolvedDrops {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (found : Option (Found problem)) : Prop :=
  ∀ update smaller, found = some (.solved update smaller) → ReducingDrop problem update

theorem foundKeeps_of_drops (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {found : Option (Found problem)} (permuted : PermutedMiller S.levels problem)
    (drops : SolvedDrops found) : FoundKeeps (fun problem => PermutedMiller S.levels problem) found :=
  fun update smaller fired => permutedMiller_of_reducingDrop rigid sn permuted (drops update smaller fired)

/-- **A drop survives keeping an equation in front.** -/
theorem ReducingDrop.keepLeft {Θ : Context S.R} {rest : EquationStore (TotalTerm Θ)} (equation : Equation (TotalTerm Θ))
    {update : Update S.levels rest} (drops : ReducingDrop rest update) :
    ReducingDrop (equation :: rest) (update.keepLeft [equation]) := by
  obtain ⟨first, others, perm, remaining, valid, answer⟩ := drops
  refine ⟨first, equation :: others, ?_, ?_, valid, answer⟩
  · exact (List.Perm.swap equation first others).trans (List.Perm.cons equation perm)
  · change (frames S.levels).applyStore update.answer [equation] ++ update.remaining = _
    rw [remaining]
    rfl

theorem solvedDrops_keepLeft {Θ : Context S.R} {rest : EquationStore (TotalTerm Θ)} (equation : Equation (TotalTerm Θ))
    {found : Option (Found rest)} (drops : SolvedDrops found) : SolvedDrops (found.map (Found.keepLeft equation)) := by
  intro update smaller fired
  obtain ⟨inner, computed, same⟩ := Option.map_eq_some_iff.mp fired
  cases inner with
  | solved moved movedSmaller =>
      cases same
      exact (drops moved movedSmaller computed).keepLeft equation
  | refuted absent => cases same

/-- **Drops survive the transport to the newest declaration.** -/
theorem throughNewest_drops {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : (stored : EquationStore (TotalTerm (extend view.base view.type))) → Option (Found stored))
    (drops : ∀ stored, SolvedDrops (solve stored)) : SolvedDrops (throughNewest view problem solve) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact drops problem

end Drops

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
