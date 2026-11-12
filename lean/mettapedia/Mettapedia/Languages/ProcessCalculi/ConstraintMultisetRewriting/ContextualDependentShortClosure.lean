import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance2Cumulative

/-!
# `StratifiedShort` is not closed under decomposition at dependent twins; the stratified Miller class

R110's class `StratifiedShort` opens both sides of an equation at the number of leading abstractions of the left
side, and asks every metavariable to be applied to **at most** the number of leading Π binders of its declaration.
A dependent decomposition breaks the second condition.

**The witness** (`ContextualDependentShortClosure.Controls`), over `A : U0, X : U0, F : X, K : Π A A`:

* `λ g. g (Π A A) (λ z. K z) ≐ λ g. g X F` at `Π (g : Π (T : U0). T → A). A`, in the dynamic pattern fragment;
* the first round of the cumulative family decomposes the local spine into `λ g. Π A A ≐ λ g. X` and the twin
  `λ g. λ z. K z ≐ λ g. F`, at `Π D (Π A A)` on the left and `Π D X` on the right;
* the twin is opened at depth two, so its right side is `F z`, with `F : X` applied to one argument while its
  declaration has no Π binder: the residual store is neither `StratifiedShort` nor `Stratified`.

The twin is well formed: its annotations are equal types under every solution of the equation before it
(`twin_stratifiedAt`), which forces `X` to be `Π A A`. The over-application is an artefact of opening the right side at
the left side's depth before the earlier equation is solved, which is how Gundry and McBride's twins arise.

**The corrected class** (`StratifiedMiller`) keeps the stratified annotations and the Miller condition on every normal
form of each opened side, and drops the condition on the number of arguments. It contains `StratifiedShort`
(`stratifiedMiller_of_short`), hence the fragment (`stratifiedMiller_of_fragment`), and it contains the witness's
residual store. A conditional decision follows from settling on it exactly as on `StratifiedShort`
(`decided_of_settling_miller`). Its closure under every progress is not proved here, and at the tower the settling
hypothesis fails: the conclusion would decide `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentShortClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure ContextualDependentInPlaceClosure

/-! ## The stratified Miller class -/

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)

/-- **Fragment sides with Miller occurrences**: every normal form of each opened side has Miller occurrences, with no
condition on the number of arguments of a metavariable. -/
def FragmentSidesMiller {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Prop :=
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.1.2.code) code → Normal rules code →
    miller (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code)) code = true) ∧
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.2.2.code) code → Normal rules code →
    miller (openedFlexible (ContextualDependentPatternSolver.lamDepth equation.1.2.code)) code = true)

/-- **The stratified Miller class**: at every position of the store, Miller sides, and annotations equal under every
solution of the equations before it. -/
def StratifiedMiller {Θ : Context rules} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ∀ (before after : EquationStore (TotalTerm Θ)) (equation : Equation (TotalTerm Θ)),
    problem = before ++ equation :: after → FragmentSidesMiller equation ∧ StratifiedAt levels before equation

variable {levels}

/-- **The Miller class contains `StratifiedShort`.** -/
theorem stratifiedMiller_of_short {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (short : StratifiedShort levels problem) : StratifiedMiller levels problem := by
  intro before after equation split
  obtain ⟨sides, annotations⟩ := short before after equation split
  exact ⟨⟨fun code reduces normal => (sides.1 code reduces normal).1,
    fun code reduces normal => (sides.2 code reduces normal).1⟩, annotations⟩

/-- **The Miller class contains the dynamic pattern fragment.** -/
theorem stratifiedMiller_of_fragment {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFragmentStore problem) : StratifiedMiller levels problem :=
  stratifiedMiller_of_short (stratifiedShort_of_fragment inside)

/-- **A store leaves `StratifiedShort`** when a normal reduct of an opened right side of one of its equations has a
metavariable applied beyond its declared arity, or leaves the Miller occurrences. -/
theorem not_stratifiedShort_of_right {Θ : Context rules} {problem before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (split : problem = before ++ equation :: after)
    {code : Tm Head (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)}
    (reduces : Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.2.2.code) code) (normal : Normal rules code)
    (outside : ¬ InFragmentCodeShort Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code) :
    ¬ StratifiedShort levels problem :=
  fun short => outside ((short before after equation split).1.2 code reduces normal)

/-- **A store leaves `Stratified`** when a normal reduct of an opened right side leaves the fragment. -/
theorem not_stratified_of_right {Θ : Context rules} {problem before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (split : problem = before ++ equation :: after)
    {code : Tm Head (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)}
    (reduces : Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.2.2.code) code) (normal : Normal rules code)
    (outside : ¬ InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code) :
    ¬ Stratified levels problem :=
  fun stratified => outside ((stratified before after equation split).1.2 code reduces normal)

/-- A store whose equations all have Miller sides, the first one with equal annotation codes and the second
stratified after the first, is in the Miller class. -/
theorem stratifiedMiller_pair {Θ : Context rules} (first second : Equation (TotalTerm Θ))
    (firstSides : FragmentSidesMiller first) (secondSides : FragmentSidesMiller second)
    (annotations : first.1.1.code = first.2.1.code) (twin : StratifiedAt levels [first] second) :
    StratifiedMiller levels [first, second] := by
  intro before after equation split
  match before, split with
  | [], split =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨same, -⟩ := split
      subst same
      refine ⟨firstSides, fun σ _ => ?_⟩
      rw [annotations]
      exact (first.2.1.reindex σ).isType.refl
  | [one], split =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at split
      obtain ⟨sameFirst, sameSecond, -⟩ := split
      subst sameFirst sameSecond
      exact ⟨secondSides, twin⟩
  | _ :: _ :: _, split => simp at split

end General

/-! ## Twins are stratified -/

section Twins

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} (facts : FormFacts S.R S.roles)
include facts

/-- **A twin after its domain equation.** If the first equation is `λ x. P ≐ λ x. Q` at `Π D U` with `U` a universe,
then annotations `Π D P` and `Π D Q` are equal types under every solution of it. -/
theorem twin_stratifiedAt {Θ : Context S.R} (first second : Equation (TotalTerm Θ)) {D : Tm Head Θ.arity}
    {p x : Tm Head (Θ.arity + 1)} {u : Head} (hu : S.R.isUniverse u)
    (firstLeft : first.1.2.code = .lam p) (firstRight : first.2.2.code = .lam x)
    (firstType : first.1.1.code = .pi D (.head u))
    (secondLeft : second.1.1.code = .pi D p) (secondRight : second.2.1.code = .pi D x) :
    StratifiedAt S.levels [first] second := by
  intro Δ σ solved
  have held := ((models_iff S.levels σ [first]).mp solved first List.mem_cons_self).2
  have domain := (first.1.1.reindex σ).isType.refl
  change TypeEq S.R Δ.raw (subst σ.substitution first.1.1.code) (subst σ.substitution first.1.1.code) at domain
  rw [firstLeft, firstRight, firstType] at held
  rw [firstType] at domain
  change Equal S.R Δ.raw (.lam (subst (liftSub σ.substitution) p)) (.lam (subst (liftSub σ.substitution) x))
    (.pi (subst σ.substitution D) (.head u)) at held
  change TypeEq S.R Δ.raw (.pi (subst σ.substitution D) (.head u)) (.pi (subst σ.substitution D) (.head u)) at domain
  have bodies := ContextualDependentOccursFull.lam_equal_inv facts Δ.formed held
  rw [secondLeft, secondRight]
  change TypeEq S.R Δ.raw (.pi (subst σ.substitution D) (subst (liftSub σ.substitution) p))
    (.pi (subst σ.substitution D) (subst (liftSub σ.substitution) x))
  exact (ContextualDependentRigid.typeEq_pi_iff facts Δ.formed).mpr
    ⟨((ContextualDependentRigid.typeEq_pi_iff facts Δ.formed).mp domain).1, ⟨u, hu, bodies⟩⟩

end Twins

/-! ## A conditional decision from settling on the Miller class -/

section Reduction

open ContextualDependentUpdate ContextualDependentWorklist ContextualDependentRank ContextualDependentConversionBudget
open ContextualDependentCumulative

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
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **Conditional decision from settling on the Miller class.** If, at each nonempty store of `StratifiedMiller` and
from some budget on, the cumulative round is not stuck and keeps every residual store in `StratifiedMiller`, then the
cumulative family decides every store of the dynamic pattern fragment at one joint budget, with a principal answer or
a certified refutation, and the same outcome at every larger joint budget. At the tower's setting the conclusion fails
on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there the hypothesis
fails. For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem decided_of_settling_miller
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, StratifiedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            StratifiedMiller S.levels update.remaining)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (cumulativeSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable (fun problem => StratifiedMiller S.levels problem)
    eventual).decided (stratifiedMiller_of_fragment inside)

end Reduction

end ContextualDependentShortClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
