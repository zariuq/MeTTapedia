import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringReading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance

/-!
# The firing round: the rigid out-of-scope refutation over the arguments round

The **rigid rule** reads every store equation under its local telescope (`viewEquation`), in both
orientations, and refutes it when the left code is a metavariable applied to locals and a local outside those
arguments occurs in the rigid support of a normal Miller right code (`readingRefute`). Every refutation is
certified (`ContextualDependentPatternFiring.reading_refuted`). The rule reads every metavariable, not only the
newest one, and no pattern is recognized.

The **firing round** runs R99's arguments round and, when it is stuck, R94's conversion pattern rule on the store as
it is, then the rigid rule. A pattern answer removes the newest declaration, so it lowers the weight rank by its
first component. Running the pattern rule at the top makes its firing a statement about this round alone
(`firingRound_not_stuck_of_pattern`): inside the chain, a progress that keeps the arity is not committed by R97's
abstraction round. The round is eventually constant (`firingRound_const`), so the firing family settles on every
class where it fires and stays (`firingSettledOfConst`). It is **conservative** over the arguments family: wherever the arguments round
moves, the firing round makes the same move (`firingRound_eq_of_arguments`), so every store R99's family
decides, the firing family decides with the same outcome (`firing_decided_of_arguments`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentPatternSolver
open ContextualDependentDecisiveFragment ContextualDependentFragment ContextualDependentRank
open ContextualDependentIdEndpointsArguments ContextualDependentConversionBudget

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

/-! ## The rigid rule -/

/-- The scoped reading of an equation, as `viewEquation` returns it. -/
abbrev Reading {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :=
  (scope : Spine equation.1.1) × (active : Active scope.target) ×'
    ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution

/-- The rigid rule on a reading, in both orientations, carried to the store. -/
def refuteReading {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    Option (Reading equation) → Option (PLift (¬ (frames S.levels).Solvable (equation :: rest)))
  | none => none
  | some ⟨scope, active, view⟩ =>
      match readingRefute facts roots heads rigid complete normalizes certifyNormal scope active with
      | some absent => some ⟨View.refutes (S := S) ⟨scope.toScoped active, view⟩
          (fun solution held => absent.down solution held) rest⟩
      | none =>
          (readingRefute facts roots heads rigid complete normalizes certifyNormal scope
              ⟨active.type, active.right, active.left⟩).map fun absent =>
            ⟨View.refutes (S := S) ⟨scope.toScoped active, view⟩
              (fun solution held => absent.down solution ((toScoped_swap scope active solution).mpr held)) rest⟩

/-- The rigid rule on one store equation. -/
def tryEquationCode (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (PLift (¬ (frames S.levels).Solvable (equation :: rest))) :=
  refuteReading facts roots heads rigid complete normalizes certifyNormal equation rest
    (viewEquation facts roots heads algebra declared choices reducer root fuel equation)

/-- A refutation of the rest of a store refutes the store. -/
def keepRefuted {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {rest : EquationStore (TotalTerm Θ)}
    (absent : PLift (¬ (frames S.levels).Solvable rest)) : PLift (¬ (frames S.levels).Solvable (equation :: rest)) :=
  ⟨fun ⟨Δ, solution, modeled⟩ =>
    absent.down ⟨Δ, solution, fun other member => modeled other (List.mem_cons_of_mem _ member)⟩⟩

/-- **The rigid rule**: the first equation of the store that it refutes. -/
def rigidRule (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (PLift (¬ (frames S.levels).Solvable problem))
  | [] => none
  | equation :: rest =>
      (tryEquationCode facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          fuel equation rest).or
        ((rigidRule fuel rest).map (keepRefuted equation))

/-! ## The firing round -/

/-- The pattern rule and the rigid rule on the store as it is, after the arguments round is stuck. -/
def flexibleRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal fuel problem with
  | some (.solved update smaller) => .progress update (below_of_arity facts roots heads algebra rigid complete smaller)
  | some (.refuted absent) => .refuted absent
  | none =>
      match rigidRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          fuel problem with
      | some absent => .refuted absent.down
      | none => .stuck

/-- **One firing round**: the arguments round; when it is stuck, the conversion pattern rule on the store as it is,
then the rigid rule. -/
def firingRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck => flexibleRest facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal fuel problem
  | other => other

/-- **The firing family**, at the weight rank. -/
noncomputable def firingFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Conservativity over the arguments family -/

/-- **The firing round makes the move of the arguments round wherever that round moves.** -/
theorem firingRound_eq_of_arguments (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold firingRound
  cases computed : argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the arguments family decides, the firing family decides with the same outcome.** -/
theorem firing_run_of_arguments (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((argumentsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((firingFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((argumentsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => firingRound_eq_of_arguments facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the arguments family decides at a joint budget, the firing family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem firing_decided_of_arguments {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((argumentsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((firingFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((argumentsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => firing_run_of_arguments facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-- The firing round is not stuck where the arguments round is not. -/
theorem firingRound_not_stuck_of_arguments (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  rw [firingRound_eq_of_arguments facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel moving]
  exact moving

/-- **The rigid-occurrence row.** When the rigid rule refutes, the firing round is not stuck. -/
theorem firingRound_not_stuck_of_rigid (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (rigidRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      fuel problem).isSome) :
    firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold firingRound
  cases argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      unfold flexibleRest
      cases ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer
          rigid complete root normalizes certifyNormal fuel problem with
      | some found =>
          cases found with
          | solved update smaller => exact fun impossible => by cases impossible
          | refuted absent => exact fun impossible => by cases impossible
      | none =>
          obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp read
          simp only [computed]
          exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The pattern rows.** When the conversion pattern rule decides on the store as it is, the firing round is not
stuck. -/
theorem firingRound_not_stuck_of_pattern (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal fuel problem).isSome) :
    firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold firingRound
  cases argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      unfold flexibleRest
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
theorem tryEquationCode_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      tryEquationCode facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel equation rest :=
  EventuallyConst.comp (refuteReading facts roots heads rigid complete normalizes certifyNormal equation rest)
    (viewEquation_const facts roots heads algebra declared choices reducer root stable equation)

include stable in
/-- **The rigid rule is eventually constant on every store.** -/
theorem rigidRule_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      rigidRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal fuel
        problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (fun pair : Option (PLift (¬ (frames S.levels).Solvable (equation :: rest))) ×
          Option (PLift (¬ (frames S.levels).Solvable rest)) => pair.1.or (pair.2.map (keepRefuted equation)))
        (EventuallyConst.pair
          (tryEquationCode_const facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal stable equation rest)
          (rigidRule_const rest))

/-- What the pattern rule commits to, as a round view. -/
def foundView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Option (Found problem) → Option (Option (Update S.levels problem))
  | some (.solved update _) => some (some update)
  | some (.refuted _) => some none
  | none => none

theorem firingRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        ((foundView (ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices
            reducer rigid complete root normalizes certifyNormal fuel problem)).or
          (if (rigidRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
              fuel problem).isSome then some none else none)) := by
  unfold firingRound
  cases argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      unfold flexibleRest
      cases ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer
          rigid complete root normalizes certifyNormal fuel problem with
      | some found =>
          cases found with
          | solved update smaller => rfl
          | refuted absent => rfl
      | none =>
          cases rigidRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            fuel problem <;> rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The firing round is eventually constant on every store.** -/
theorem firingRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => firingRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => firingRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun triple : Option (Option (Update S.levels problem)) ×
      (Option (Found problem) × Bool) =>
      triple.1.or ((foundView triple.2.1).or (if triple.2.2 then some none else none)))
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (argumentsRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.pair
        (ContextualDependentRecognitionConversion.patternRuleConv_const facts roots heads algebra declared choices
          reducer rigid complete root normalizes certifyNormal stable problem)
        (EventuallyConst.comp Option.isSome (rigidRule_const facts roots heads algebra rigid complete declared choices
          reducer root normalizes certifyNormal stable problem))))

include stable in
/-- **The firing family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def firingSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (firingFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => firingRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
