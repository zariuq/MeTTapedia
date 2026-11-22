import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralDeadBinder

/-!
# Dead binders in front of every rule

R119's dead-binder rule drops the dead binder of an equation only in front of in-place intersection. A pattern equation
behind a dead binder whose type mentions a later declaration is in the dynamic pattern fragment and solvable, yet every
rule of the dead-binder family leaves it alone (`ContextualDependentIntersectionGeneral.DeadControls.deadPattern_gap`).

**The every-rule family** runs the dead-binder round; when it is stuck, it reads each rotation of the store without the
dead binder of its first equation and runs the same round there, one level down (`everyRoundAt`). The recursion depth is
the number of abstractions on the left sides of the store (`deadDepth`). A round of the store read without the binder is
a round of the store (`undeadRound`): dropping a dead binder keeps the solutions where typed equality strengthens past an
unused variable, and keeps the weight; a round of a rotation is a round of the store (`unrotateRound`).

The family is conservative over the dead-binder family (`every_run_of_dead`) and eventually constant at every depth
(`everyRoundAt_const`), so it settles on every class on which, from some budget on, its round is not stuck and keeps the
class (`everySettledOfConst`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentEtaLong
open ContextualDependentIntersection ContextualDependentDynamicFragment ContextualDependentInPlace
open ContextualDependentIntersectionGeneral

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Rounds of equivalent stores -/

section Transfer

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **A round of a store with the same solutions and the same weight is a round of the store**, with the same residual
store. -/
def transferRound {Θ : Context S.R} {problem other : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent problem other)
    (weight : storeWeight facts roots heads algebra rigid complete other =
      storeWeight facts roots heads algebra rigid complete problem) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) other →
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem
  | .progress update smaller => .progress (update.rephrase same) (by
      have lower : ContextualDependentWorklist.Below
          (weightRank facts roots heads algebra rigid complete update.remaining)
          (Θ.arity, storeWeight facts roots heads algebra rigid complete other) := smaller
      rw [weight] at lower
      exact lower)
  | .refuted absent => .refuted fun solvable => by
      obtain ⟨Δ, σ, solved⟩ := solvable
      exact absent ⟨Δ, σ, (same Δ σ).mp solved⟩
  | .stuck => .stuck

/-- **Every progress of a transferred round leaves the residual store of a progress of the round.** -/
theorem transferRound_keeps (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    {Θ : Context S.R} {problem other : EquationStore (TotalTerm Θ)}
    {same : (frames S.levels).Equivalent problem other}
    {weight : storeWeight facts roots heads algebra rigid complete other =
      storeWeight facts roots heads algebra rigid complete problem}
    {round : Round S.levels (weightRank facts roots heads algebra rigid complete) other}
    (inner : ∀ (update : Update S.levels other)
      (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
        (weightRank facts roots heads algebra rigid complete other)),
      round = .progress update smaller → holds update.remaining)
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem)}
    (fired : transferRound facts roots heads algebra rigid complete same weight round = .progress update smaller) :
    holds update.remaining := by
  cases round with
  | progress first firstSmaller =>
      cases fired
      exact inner first firstSmaller rfl
  | refuted absent => cases fired
  | stuck => cases fired

/-- A transferred round is stuck exactly when the round is. -/
theorem transferRound_stuck {Θ : Context S.R} {problem other : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent problem other)
    (weight : storeWeight facts roots heads algebra rigid complete other =
      storeWeight facts roots heads algebra rigid complete problem)
    (round : Round S.levels (weightRank facts roots heads algebra rigid complete) other) :
    transferRound facts roots heads algebra rigid complete same weight round = .stuck ↔ round = .stuck := by
  cases round <;> simp [transferRound]

/-- **A round of a rotation of the store is a round of the store.** -/
def unrotateRound {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (k : Nat) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) (problem.rotate k) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  transferRound facts roots heads algebra rigid complete (equivalent_perm (List.rotate_perm problem k).symm)
    (storeWeight_perm facts roots heads algebra rigid complete (List.rotate_perm problem k))

variable (strengthening : EqualStrengthening S.R)

/-- **A round of the store read without the dead binder of its first equation is a round of the store.** -/
def undeadRound {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (dead : DeadBinder equation) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) (dead.reduced :: rest) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) (equation :: rest) :=
  transferRound facts roots heads algebra rigid complete (equivalent_dead facts roots strengthening dead)
    (storeWeight_dead facts roots heads algebra rigid complete rest dead)

end Transfer

/-! ## The round, the family -/

section Rule

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
  (strengthening : EqualStrengthening S.R)

/-- An inner round on the first equation of a store, read without its dead binder. -/
def everyAt (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored) :
    (stored : EquationStore (TotalTerm Θ)) → Round S.levels (weightRank facts roots heads algebra rigid complete) stored
  | [] => .stuck
  | equation :: rest =>
      match deadBinder facts roots heads algebra declared choices reducer fuel equation with
      | none => .stuck
      | some dead => undeadRound facts roots heads algebra rigid complete strengthening dead (inner (dead.reduced :: rest))

/-- An inner round on the rotations of the store in turn, each read without the dead binder of its first equation. -/
def everySearch (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (problem : EquationStore (TotalTerm Θ)) :
    List Nat → Round S.levels (weightRank facts roots heads algebra rigid complete) problem
  | [] => .stuck
  | k :: ks =>
      match everyAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner
          (problem.rotate k) with
      | .stuck => everySearch fuel inner problem ks
      | found => unrotateRound facts roots heads algebra rigid complete k found

/-- One level of the every-rule round over a lower level: the dead-binder round; when it is stuck, the lower level on
each rotation of the store, read without the dead binder of its first equation. -/
def everyStep (fuel : Nat) {Θ : Context S.R}
    (lower : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | .stuck => everySearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel lower
      problem (List.range problem.length)
  | other => other

/-- **The every-rule round at a recursion depth**: the dead-binder round, then one level down in front of every dead
binder. -/
def everyRoundAt (fuel : Nat) : Nat → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem
  | 0, _, problem => deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem
  | depth + 1, _, problem => everyStep facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (fun stored => everyRoundAt fuel depth stored)
      problem

/-- The recursion depth of the family: the abstractions on the left sides of the store. -/
def deadDepth {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Nat :=
  (problem.map fun equation => lamDepth equation.1.2.code).sum

/-- **The every-rule round**, at the store's depth. -/
def everyRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  everyRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique rootComplete strengthening fuel (deadDepth problem) problem

/-- **The every-rule family**, at the weight rank. -/
noncomputable def everyFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ## Conservativity -/

/-- **The every-rule round makes the dead-binder round's move wherever that round moves**, at every depth. -/
theorem everyRoundAt_eq_of_dead (fuel : Nat) : ∀ (depth : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)}, deadRound facts roots heads algebra rigid complete declared choices reducer
      root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck →
    everyRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel depth problem =
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem
  | 0, _, _, _ => rfl
  | depth + 1, _, problem, moving => by
      change everyStep facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel _ problem = _
      unfold everyStep
      cases computed : deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem with
      | stuck => exact absurd computed moving
      | progress update smaller => rfl
      | refuted absent => rfl

/-- **Every run that the dead-binder family decides, the every-rule family decides with the same outcome.** -/
theorem every_run_of_dead (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((everyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => everyRoundAt_eq_of_dead facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel _ moving)
    rounds _ decided

/-- **The every-rule round fires wherever the dead-binder round does.** -/
theorem everyRound_not_stuck_of_dead (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold everyRound
  rw [everyRoundAt_eq_of_dead facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel _ moving]
  exact moving

/-! ## Eventual constancy -/

theorem everyRoundAt_view (fuel depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (everyRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (depth + 1) problem) =
      (roundView (deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (roundView (everySearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel
          (fun stored => everyRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel depth stored)
          problem (List.range problem.length))) := by
  change roundView (everyStep facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel _ problem) = _
  unfold everyStep
  cases deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem everyAt_const {Θ : Context S.R}
    (inner : Nat → (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (constant : ∀ stored, EventuallyConst fun fuel => inner fuel stored) :
    ∀ stored : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      everyAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel (inner fuel) stored
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.dep (h := fun fuel => deadBinder facts roots heads algebra declared choices reducer fuel equation)
        (k := fun fuel (found : Option (DeadBinder equation)) =>
          (match found with
            | none => .stuck
            | some dead => undeadRound facts roots heads algebra rigid complete strengthening dead
                (inner fuel (dead.reduced :: rest)) :
            Round S.levels (weightRank facts roots heads algebra rigid complete) (equation :: rest)))
        (deadBinder_const facts roots heads algebra declared choices reducer stable equation)
        (fun found => by
          cases found with
          | none => exact EventuallyConst.const _
          | some dead =>
              exact EventuallyConst.comp (undeadRound facts roots heads algebra rigid complete strengthening dead)
                (constant _))

include stable in
theorem everySearch_const {Θ : Context S.R}
    (inner : Nat → (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (constant : ∀ stored, EventuallyConst fun fuel => inner fuel stored) (problem : EquationStore (TotalTerm Θ)) :
    ∀ rotations : List Nat, EventuallyConst fun fuel =>
      everySearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel (inner fuel)
        problem rotations
  | [] => EventuallyConst.const _
  | k :: ks => by
      obtain ⟨t₁, first⟩ := (everyAt_const facts roots heads algebra rigid complete declared choices reducer
        strengthening stable inner constant (problem.rotate k)).spec
      obtain ⟨t₂, later⟩ := (everySearch_const inner constant problem ks).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [everySearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

include stable in
/-- **The every-rule round is eventually constant on every store, at every depth.** -/
theorem everyRoundAt_const : ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel => everyRoundAt facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel depth problem
  | 0, _, problem => EventuallyConst.of_eq (fun _ => rfl) (deadRound_const facts roots heads algebra rigid complete
      declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem)
  | depth + 1, _, problem => by
      refine round_const_of_view ?_
      refine EventuallyConst.of_eq (fun fuel => everyRoundAt_view facts roots heads algebra rigid complete declared
        choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel depth problem) ?_
      exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
          Option (Option (Update S.levels problem)) => pair.1.or pair.2)
        (EventuallyConst.pair
          (EventuallyConst.comp roundView (deadRound_const facts roots heads algebra rigid complete declared choices
            reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
          (EventuallyConst.comp roundView (everySearch_const facts roots heads algebra rigid complete declared choices
            reducer strengthening stable
            (fun fuel stored => everyRoundAt facts roots heads algebra rigid complete declared choices reducer root
              normalizes certifyNormal headTypingUnique rootComplete strengthening fuel depth stored)
            (fun stored => everyRoundAt_const depth stored) problem _)))

include stable in
/-- **The every-rule family settles** on every class on which, from some budget on, its round is not stuck and keeps
the class. -/
noncomputable def everySettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (everyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => everyRoundAt_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable (deadDepth problem)
    problem) holds eventual

end Rule

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
