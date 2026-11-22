import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeRule

/-!
# The cumulative round: conservativity, firing, eventual constancy

The cumulative round makes the move of the flexible-base round wherever that round moves
(`cumulativeRound_eq_of_flex`, `cumulative_decided_of_flex`), is not stuck where the cumulative rule decides
(`cumulativeRound_not_stuck_of_rule`), is eventually constant (`cumulativeRound_const`), and settles where it is not
stuck (`cumulativeSettledOfConst`). Retyping reads the budget only through type formation and checking, which keep
their results (`retypeAt_const`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulative

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentRecognitionConversion
open ContextualDependentSpineEta ContextualDependentPruneSolve ContextualDependentPatternFiring

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

/-! ## Conservativity over the flexible-base family -/

/-- **The cumulative round makes the move of the flexible-base round wherever that round moves.** -/
theorem cumulativeRound_eq_of_flex (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold cumulativeRound
  cases computed : flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the flexible-base family decides, the cumulative family decides with the same outcome.** -/
theorem cumulative_run_of_flex (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => cumulativeRound_eq_of_flex facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the flexible-base family decides at a joint budget, the cumulative family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem cumulative_decided_of_flex {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => cumulative_run_of_flex facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-! ## Firing -/

/-- **The cumulative round is not stuck where the cumulative rule decides.** -/
theorem cumulativeRound_not_stuck_of_rule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (cumulativeRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal fuel problem).isSome) :
    cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold cumulativeRound
  cases flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      cases found with
      | solved update smaller => exact fun impossible => by cases impossible
      | refuted absent => exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- Checking keeps its results. -/
theorem checkAt_const {C : Context S.R} (type : TypeOver C) (code : Tm Head C.arity) :
    EventuallyConst fun fuel => checkAt facts roots heads algebra declared choices reducer fuel type code :=
  EventuallyConst.comp (ofChecked facts roots heads algebra declared type code)
    (EventuallyConst.of_mono fun computed enough =>
      ContextualDependentCheckingBudget.check_success_mono S.R choices reducer stable computed enough)

include stable in
/-- **Retyping is eventually constant.** -/
theorem retypeAt_const {Θ : Context S.R} (domain : TypeOver Θ) (opened : Active (extend Θ domain)) (u : Head) :
    EventuallyConst fun fuel =>
      retypeAt facts roots heads algebra rigid complete declared choices reducer fuel domain opened u := by
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have checking : ∀ (C : Context S.R) (type : TypeOver C) (code : Tm Head C.arity), ∃ threshold, ∀ fuel,
      threshold ≤ fuel →
        checkAt facts roots heads algebra declared choices reducer fuel type code =
          checkAt facts roots heads algebra declared choices reducer threshold type code :=
    fun _ type code => (checkAt_const facts roots heads algebra declared choices reducer stable type code).spec
  choose formAt formSame using forming
  choose checkThreshold checkSame using checking
  unfold retypeAt
  split <;> try exact EventuallyConst.const _
  refine eventually_dite (fun _ => ?_) (fun _ => EventuallyConst.const _)
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq (max (checkThreshold _ _ _) (checkThreshold _ _ _)) (fun fuel enough => by
    rw [checkSame _ _ _ fuel (le_of_max_le_left enough), checkSame _ _ _ fuel (le_of_max_le_right enough)]) ?_
  exact EventuallyConst.const _

include stable in
/-- **The cumulative rule on one scoped reading is eventually constant.** -/
theorem cumulativeActive_const {Γ : Context S.R} (type : TypeOver Γ) {whole : TypeOver (extend Γ type)}
    (scope : Spine whole) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      cumulativeActive facts roots heads algebra rigid complete declared choices reducer normalizes certifyNormal fuel
        type scope active equation view rest := by
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have retyping : ∀ (Θ : Context S.R) (domain : TypeOver Θ) (opened : Active (extend Θ domain)) (u : Head),
      ∃ threshold, ∀ fuel, threshold ≤ fuel →
        retypeAt facts roots heads algebra rigid complete declared choices reducer fuel domain opened u =
          retypeAt facts roots heads algebra rigid complete declared choices reducer threshold domain opened u :=
    fun _ domain opened u => (retypeAt_const facts roots heads algebra rigid complete declared choices reducer stable
      domain opened u).spec
  choose formAt formSame using forming
  choose retypeThreshold retypeSame using retyping
  unfold cumulativeActive
  split <;> try exact EventuallyConst.const _
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [retypeSame _ _ _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  rename_i readOpened _ _ _ _ same _ _ _ _
  apply tryActiveConv_const facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal
    stable
  exact fun solution => (view solution).trans ((readOpened solution).trans (same solution))

include stable in
theorem cumulativeEquation_const {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      cumulativeEquation facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel type equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases reading : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold cumulativeEquation
      erw [viewed fuel enough, reading]
  | some found =>
      obtain ⟨scope, active, view⟩ := found
      obtain ⟨t₂, first⟩ := (cumulativeActive_const facts roots heads algebra rigid complete declared choices reducer
        normalizes certifyNormal stable type scope active equation view rest).spec
      obtain ⟨t₃, second⟩ := (cumulativeActive_const facts roots heads algebra rigid complete declared choices reducer
        normalizes certifyNormal stable type scope ⟨active.type, active.right, active.left⟩ equation
        (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      dsimp only
      unfold cumulativeEquation
      erw [viewed fuel e₁, reading, viewed _ f₁, reading]
      dsimp only
      erw [first fuel e₂, first _ f₂, second fuel e₃, second _ f₃]

include stable in
theorem cumulativeSearch_const {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), EventuallyConst fun fuel =>
      cumulativeSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel type problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (cumulativeEquation_const facts roots heads algebra rigid complete declared choices reducer
        root normalizes certifyNormal stable type equation rest).spec
      obtain ⟨t₂, later⟩ := (cumulativeSearch_const type rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [cumulativeSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

include stable in
/-- **The cumulative rule is eventually constant on every store.** -/
theorem cumulativeRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      cumulativeRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel problem := by
  obtain ⟨t₁, newest⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases found : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold cumulativeRule
      erw [newest fuel enough, found]
  | some view =>
      obtain ⟨t₂, searched⟩ := (ContextualDependentDecisiveFragment.throughNewest_const view problem
        (fun fuel => cumulativeSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal fuel view.type)
        (cumulativeSearch_const facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal stable view.type)).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      unfold cumulativeRule
      erw [newest fuel (le_of_max_le_left enough), found, newest _ (le_max_left _ _), found]
      dsimp only
      exact (searched fuel (le_of_max_le_right enough)).trans (searched _ (le_max_right _ _)).symm

theorem cumulativeRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (ContextualDependentPatternFiring.foundView (cumulativeRule facts roots heads algebra rigid complete declared
          choices reducer root normalizes certifyNormal fuel problem)) := by
  unfold cumulativeRound
  cases flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases cumulativeRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal fuel problem with
      | some found =>
          cases found with
          | solved update smaller => rfl
          | refuted absent => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The cumulative round is eventually constant on every store.** -/
theorem cumulativeRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => cumulativeRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => cumulativeRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (flexRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp ContextualDependentPatternFiring.foundView (cumulativeRule_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal stable problem)))

include stable in
/-- **The cumulative family settles** on every class of stores on which, at each nonempty store and from some budget
on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def cumulativeSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (cumulativeFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => cumulativeRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentCumulative
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
