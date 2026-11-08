import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralInPlace

/-!
# The in-place round: conservativity, eventual constancy, settling

The in-place intersection rule reads the newest declaration, the strengthening of the first equation, and the general
intersection rule on the strengthened equation, at each depth. All of these keep their results at larger budgets, so the
rule is **eventually constant on every store** (`inPlaceIntersectRule_const`), and so is the round
(`inPlaceRound_const`). The round makes the older round's move wherever that round moves
(`inPlaceRound_eq_of_older`, `inPlace_run_of_older`), and acceptance reduces to settling on the Miller class for this
family as for the others (`inPlace_decided_of_settling_miller`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget
open ContextualDependentIntersection ContextualDependentDynamicFragment ContextualDependentInPlace

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

/-! ## Conservativity over the older family -/

/-- **The in-place round makes the move of the older round wherever that round moves.** -/
theorem inPlaceRound_eq_of_older (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold inPlaceRound
  cases computed : olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the older family decides, the in-place family decides with the same outcome.** -/
theorem inPlace_run_of_older (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((olderFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((olderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => inPlaceRound_eq_of_older facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **The in-place round is not stuck where the in-place intersection rule fires.** -/
theorem inPlaceRound_not_stuck_of_rule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (inPlaceIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome) :
    inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold inPlaceRound
  cases olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
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

/-- Forget the site of a sited progress. -/
def forgetSite {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : SitedProgress facts roots heads algebra rigid complete problem) :
    Progress facts roots heads algebra rigid complete problem :=
  ⟨found.val, found.property.1⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem forgetSite_injective {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Function.Injective (forgetSite facts roots heads algebra rigid complete (problem := problem)) := by
  intro first second same
  exact Subtype.ext (congrArg (fun progress : Progress facts roots heads algebra rigid complete problem =>
    progress.val) same)

theorem sitedRule_forget (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (sitedRule facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique fuel
      problem).map (forgetSite facts roots heads algebra rigid complete) =
      generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem := by
  unfold sitedRule
  split
  · rename_i found fired
    exact fired.symm
  · rename_i fired
    exact fired.symm

include stable in
theorem sitedRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => sitedRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes headTypingUnique fuel problem :=
  EventuallyConst.of_injective (Option.map_injective (forgetSite_injective facts roots heads algebra rigid complete))
    (EventuallyConst.of_eq (fun fuel => sitedRule_forget facts roots heads algebra rigid complete declared choices
      reducer root normalizes headTypingUnique fuel problem)
      (generalIntersectRule_const facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique stable problem))

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem throughNewestSited_const {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : Nat → (stored : EquationStore (TotalTerm (extend view.base view.type))) →
      Option (SitedProgress facts roots heads algebra rigid complete stored))
    (constant : ∀ stored, EventuallyConst fun fuel => solve fuel stored) :
    EventuallyConst fun fuel => throughNewestSited facts roots heads algebra rigid complete view problem (solve fuel) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact constant problem

include stable in
/-- **Strengthening the first equation is eventually constant.** -/
theorem headSplit_const {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), EventuallyConst fun fuel =>
      headSplit facts roots heads algebra rigid complete declared choices reducer fuel type problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, s₁⟩ := (strengthen_const facts roots heads algebra declared choices reducer stable type equation.1).spec
      obtain ⟨t₂, s₂⟩ := (strengthen_const facts roots heads algebra declared choices reducer stable type equation.2).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [headSplit]
      erw [s₁ fuel (le_of_max_le_left enough), s₁ _ (le_max_left _ _), s₂ fuel (le_of_max_le_right enough),
        s₂ _ (le_max_right _ _)]

include stable in
/-- **In-place intersection at every depth is eventually constant on every store.** -/
theorem inPlaceIntersectAt_const : ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel =>
      inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel depth problem
  | 0, _, problem => sitedRule_const facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique stable problem
  | depth + 1, Θ, problem => by
      obtain ⟨t₁, viewed⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
      cases viewRun : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          simp only [inPlaceIntersectAt]
          erw [viewed fuel enough, viewRun]
      | some view =>
          obtain ⟨t₂, solved⟩ := (throughNewestSited_const facts roots heads algebra rigid complete view problem
            (fun fuel stored =>
              carryHead facts roots heads algebra rigid complete view.type stored
                (fun strong => inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root
                  normalizes headTypingUnique fuel depth strong)
                (headSplit facts roots heads algebra rigid complete declared choices reducer fuel view.type stored))
            (fun stored => EventuallyConst.dep
              (h := fun fuel => headSplit facts roots heads algebra rigid complete declared choices reducer fuel
                view.type stored)
              (k := fun fuel split => carryHead facts roots heads algebra rigid complete view.type stored
                (fun strong => inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root
                  normalizes headTypingUnique fuel depth strong) split)
              (headSplit_const facts roots heads algebra rigid complete declared choices reducer stable view.type stored)
              (fun split => by
                cases split with
                | none => exact EventuallyConst.const _
                | some split =>
                    exact EventuallyConst.comp (Option.map (carrySited facts roots heads algebra rigid complete
                      view.type split.property.1 split.property.2)) (inPlaceIntersectAt_const depth split.val.1)))).spec
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          simp only [inPlaceIntersectAt]
          erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
          exact (solved fuel (le_of_max_le_right enough)).trans (solved _ (le_max_right _ _)).symm

include stable in
theorem inPlaceIntersectSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, EventuallyConst fun fuel =>
      inPlaceIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem depths
  | [] => EventuallyConst.const _
  | depth :: rest => by
      obtain ⟨t₁, first⟩ := (inPlaceIntersectAt_const facts roots heads algebra rigid complete declared choices reducer
        root normalizes headTypingUnique stable depth problem).spec
      obtain ⟨t₂, later⟩ := (inPlaceIntersectSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [inPlaceIntersectSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- The view of a sited progress. -/
def sitedView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Option (SitedProgress facts roots heads algebra rigid complete problem) → Option (Option (Update S.levels problem))
  | some found => some (some found.val)
  | none => none

theorem inPlaceRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (sitedView facts roots heads algebra rigid complete (inPlaceIntersectRule facts roots heads algebra rigid
          complete declared choices reducer root normalizes headTypingUnique fuel problem)) := by
  unfold inPlaceRound
  cases olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases inPlaceIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The in-place round is eventually constant on every store.** -/
theorem inPlaceRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => inPlaceRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => inPlaceRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (olderRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp (sitedView facts roots heads algebra rigid complete)
        (inPlaceIntersectSearch_const facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique stable problem _)))

include stable in
/-- **The in-place family settles** on every class of stores on which, at each nonempty store and from some budget
on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def inPlaceSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => inPlaceRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

include stable in
/-- **Acceptance for the in-place family, reduced to settling on the Miller class.** -/
theorem inPlace_decided_of_settling_miller
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)},
      ContextualDependentShortClosure.StratifiedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            ContextualDependentShortClosure.StratifiedMiller S.levels update.remaining)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((inPlaceFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (inPlaceSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable
    (fun problem => ContextualDependentShortClosure.StratifiedMiller S.levels problem) eventual).decided
    (ContextualDependentShortClosure.stratifiedMiller_of_fragment inside)

end ContextualDependentIntersectionGeneral
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
