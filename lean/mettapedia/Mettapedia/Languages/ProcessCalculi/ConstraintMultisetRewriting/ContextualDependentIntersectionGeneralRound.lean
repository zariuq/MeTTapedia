import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneral
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosure

/-!
# The general round: conservativity, eventual constancy, settling

The general intersection rule reads the scoped reading, `G`'s spine and the recognized pattern, the right side's
arguments, the agreeing binders, the pruned type and its spine, and the conversion test of the instantiated equation.
Type formation, spine discovery, the scoped reading and the conversion test keep their results at larger budgets, and
every other step reads no budget, so the rule is **eventually constant on every store** (`generalIntersectRule_const`),
and so is the round (`generalRound_const`). The round makes the cumulative round's move wherever that round moves
(`generalRound_eq_of_cumulative`, `general_decided_of_cumulative`).

A conditional decision follows from settling on the Miller class for this family exactly as for the cumulative
family (`general_decided_of_settling_miller`). At the tower its hypothesis fails: the conclusion would decide
`crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentFlexReorder
open ContextualDependentIntersection ContextualDependentCumulative ContextualDependentDynamicFragment

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

/-! ## Conservativity over the cumulative family -/

/-- **The general round makes the move of the cumulative round wherever that round moves.** -/
theorem generalRound_eq_of_cumulative (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold generalRound
  cases computed : cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the cumulative family decides, the general family decides with the same outcome.** -/
theorem general_run_of_cumulative (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => generalRound_eq_of_cumulative facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the cumulative family decides at a joint budget, the general family decides at that budget**,
with the same outcome at every larger joint budget. -/
theorem general_decided_of_cumulative {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => general_run_of_cumulative facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-- **The general round is not stuck where the general intersection rule fires.** -/
theorem generalRound_not_stuck_of_rule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome) :
    generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold generalRound
  cases cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **General intersection on one recognized pattern is eventually constant.** -/
theorem generalIntersect_const {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer)))
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    EventuallyConst fun fuel =>
      generalIntersect facts roots heads algebra rigid complete declared choices reducer normalizes headTypingUnique fuel
        newer scope active equation view rest spine recognized := by
  have discovering : ∀ (Γ : Context S.R) (count : Nat) (whole : TypeOver Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole =
        ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer threshold count
          whole :=
    fun _ count whole => (discover_const facts roots heads algebra declared choices reducer stable count whole).spec
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have comparing : ∀ (Γ : Context S.R) (first second : TotalTerm Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      Conversion.compare facts roots heads algebra reducer fuel first second =
        Conversion.compare facts roots heads algebra reducer threshold first second :=
    fun _ first second => (compare_const facts roots heads algebra reducer stable first second).spec
  choose discoverAt discoverSame using discovering
  choose formAt formSame using forming
  choose compareAt compareSame using comparing
  unfold generalIntersect
  try dsimp only
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  split
  · exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  split
  swap
  · exact EventuallyConst.const _
  try dsimp only
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by erw [compareSame _ _ _ fuel enough]) ?_
  split <;> exact EventuallyConst.const _

include stable in
/-- **General intersection on one store equation is eventually constant.** -/
theorem generalIntersectEquation_const {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer))) :
    EventuallyConst fun fuel =>
      generalIntersectEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel newer equation rest := by
  have viewing : ∀ {Θ : Context S.R} (equation : Equation (TotalTerm Θ)), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      viewEquation facts roots heads algebra declared choices reducer root fuel equation =
        viewEquation facts roots heads algebra declared choices reducer root threshold equation :=
    fun equation => (viewEquation_const facts roots heads algebra declared choices reducer root stable equation).spec
  have discovering : ∀ (Γ : Context S.R) (count : Nat) (whole : TypeOver Γ), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel count whole =
        ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer threshold count
          whole :=
    fun _ count whole => (discover_const facts roots heads algebra declared choices reducer stable count whole).spec
  obtain ⟨t₁, viewSame⟩ := viewing equation
  choose discoverAt discoverSame using discovering
  unfold generalIntersectEquation
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by erw [viewSame fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [discoverSame _ _ _ fuel enough]) ?_
  split
  · exact EventuallyConst.const _
  split
  · exact EventuallyConst.const _
  exact generalIntersect_const facts roots heads algebra rigid complete declared choices reducer normalizes
    headTypingUnique stable _ _ _ _ _ _ _ _

include stable in
/-- **The general intersection rule is eventually constant on every store.** -/
theorem generalIntersectRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem := by
  obtain ⟨t₁, viewSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases viewed : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold generalIntersectRule
      erw [viewSame fuel enough, viewed]
  | some view =>
      have constant : ∀ {Γ₀ : Context S.R} (newer : TypeOver Γ₀) (stored : EquationStore (TotalTerm (extend Γ₀ newer))),
          EventuallyConst fun fuel => (match stored with
            | [] => none
            | equation :: rest => generalIntersectEquation facts roots heads algebra rigid complete declared choices
                reducer root normalizes headTypingUnique fuel newer equation rest :
              Option (Progress facts roots heads algebra rigid complete stored)) := by
        intro Γ₀ newer stored
        cases stored with
        | nil => exact EventuallyConst.const _
        | cons equation rest =>
            exact generalIntersectEquation_const facts roots heads algebra rigid complete declared choices reducer root
              normalizes headTypingUnique stable newer equation rest
      obtain ⟨t₂, solved⟩ := (throughNewestProgress_const facts roots heads algebra rigid complete view problem
        (fun fuel {_} newer stored => match stored with
          | [] => none
          | equation :: rest => generalIntersectEquation facts roots heads algebra rigid complete declared choices
              reducer root normalizes headTypingUnique fuel newer equation rest)
        constant).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      unfold generalIntersectRule
      erw [viewSame fuel (le_of_max_le_left enough), viewed, viewSame _ (le_max_left _ _), viewed]
      exact (solved fuel (le_of_max_le_right enough)).trans (solved _ (le_max_right _ _)).symm

theorem generalRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (progressView facts roots heads algebra rigid complete (generalIntersectRule facts roots heads algebra rigid
          complete declared choices reducer root normalizes headTypingUnique fuel problem)) := by
  unfold generalRound
  cases cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The general round is eventually constant on every store.** -/
theorem generalRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => generalRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => generalRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (cumulativeRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp (progressView facts roots heads algebra rigid complete) (generalIntersectRule_const facts
        roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique stable problem)))

include stable in
/-- **The general family settles** on every class of stores on which, at each nonempty store and from some budget on,
its round is not stuck and keeps every residual store in the class. -/
noncomputable def generalSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (generalFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => generalRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

include stable in
/-- **Conditional decision for the general family, from settling on the Miller class.** At the tower's setting the
conclusion fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there
the hypothesis fails. For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem general_decided_of_settling_miller
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)},
      ContextualDependentShortClosure.StratifiedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            ContextualDependentShortClosure.StratifiedMiller S.levels update.remaining)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (generalSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable
    (fun problem => ContextualDependentShortClosure.StratifiedMiller S.levels problem) eventual).decided
    (ContextualDependentShortClosure.stratifiedMiller_of_fragment inside)

end ContextualDependentIntersectionGeneral
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
