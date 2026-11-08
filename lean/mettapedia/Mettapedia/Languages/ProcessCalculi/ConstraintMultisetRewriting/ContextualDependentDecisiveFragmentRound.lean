import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentPrune

/-!
# The rigid round settles wherever the pattern, prune or exchange rule fires

The full round tries the pattern rule, then the prune rule, then the exchange rule, and only then the
qualified worklist round. The first of the three rules that fires is eventually constant on every
store, because each of them is. Hence the rigid round **settles**, in the sense of `Settled`, on every
class of stores on which, at each nonempty store and from some budget on, either the distinct-locals
rule fires, or it does not and one of the pattern, prune and exchange rules fires with every solved
answer staying in the class.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentConversionBudget
open ContextualDependentGeneralPattern ContextualDependentWorklist ContextualDependentPatternSolver
open ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- The first of the pattern, prune and exchange rules that fires, in the full round's order. -/
def firstRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel problem with
  | some found => some found
  | none =>
      match pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel problem with
      | some found => some found
      | none =>
          exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            fuel problem

/-- The full round is the first rule that fires, and otherwise the worklist round. -/
theorem fullRound_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    fullRound rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem =
      match firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel problem with
      | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
      | some (.refuted absent) => .refuted absent
      | none => ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer
          fuel problem := by
  unfold fullRound firstRule
  cases patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel problem with
  | some found => cases found <;> rfl
  | none =>
      cases pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel problem with
      | some found => cases found <;> rfl
      | none =>
          cases exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes
              certifyNormal fuel problem with
          | some found => cases found <;> rfl
          | none => rfl

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The first rule that fires is eventually constant on every store.** -/
theorem firstRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem := by
  obtain ⟨t₁, pattern⟩ := (patternRule_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal stable problem).spec
  obtain ⟨t₂, pruned⟩ := (pruneRule_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal headTypingUnique stable problem).spec
  obtain ⟨t₃, exchanged⟩ := (exchangeRule_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal stable problem).spec
  refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
  have e₁ : t₁ ≤ fuel := by omega
  have e₂ : t₂ ≤ fuel := by omega
  have e₃ : t₃ ≤ fuel := by omega
  have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
  have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
  have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
  dsimp only
  unfold firstRule
  erw [pattern fuel e₁, pattern _ f₁, pruned fuel e₂, pruned _ f₂, exchanged fuel e₃, exchanged _ f₃]

include stable in
/-- **The rigid round settles wherever a rule fires.** Let a class of stores be given such that at
every nonempty store of it, from some budget on, either the distinct-locals rule fires, or it does not
and the first of the pattern, prune and exchange rules fires, with every solved answer staying in the
class. Then the rigid round settles on the class: eventually the same round at every larger budget,
not stuck, and staying in the class. -/
def settledWhereRuleFires (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
          reducer root larger problem).isSome ∨
        (ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
            reducer root larger problem = none ∧
          (firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            headTypingUnique larger problem).isSome ∧
          ∀ {update : Update S.levels problem} {smaller : update.target.arity < Γ.arity},
            firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
              headTypingUnique larger problem = some (.solved update smaller) → holds update.remaining)) :
    ContextualDependentDecisiveDriver.Settled
      (rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique) where
  holds := holds
  settles := by
    intro Γ problem inside nonempty
    obtain ⟨t₁, localsSame⟩ := (localsRule_const facts roots heads algebra declared choices reducer root stable rigid
      complete problem).spec
    obtain ⟨t₂, firstSame⟩ := (firstRule_const rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal headTypingUnique stable problem).spec
    obtain ⟨bound, firing⟩ := eventual inside nonempty
    let threshold := max bound (max t₁ t₂)
    have localsAt : ∀ larger, threshold ≤ larger →
        ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
          root larger problem =
        ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
          root threshold problem := fun larger enough =>
      (localsSame larger (by omega)).trans (localsSame threshold (by omega)).symm
    have firstAt : ∀ larger, threshold ≤ larger →
        firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger problem =
        firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique threshold problem := fun larger enough =>
      (firstSame larger (by omega)).trans (firstSame threshold (by omega)).symm
    have firingAt := firing threshold (le_max_left _ _)
    have roundAt : ∀ larger, threshold ≤ larger →
        (rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique).round larger problem =
        (rigidFamily rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique).round threshold problem := by
      intro larger enough
      change ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique larger problem =
        ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique threshold problem
      unfold ContextualDependentRigidDecomposition.rigidRound
      rw [localsAt larger enough]
      cases locals : ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
          choices reducer root threshold problem with
      | some absent => rfl
      | none =>
          dsimp only
          rw [fullRound_eq, fullRound_eq, firstAt larger enough]
          rcases firingAt with fired | ⟨_, fired, _⟩
          · rw [locals] at fired; cases fired
          · cases first : firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                certifyNormal headTypingUnique threshold problem with
            | none => rw [first] at fired; cases fired
            | some found => cases found <;> rfl
    refine ⟨threshold, ?_, roundAt, ?_⟩
    · change ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique threshold problem ≠ .stuck
      unfold ContextualDependentRigidDecomposition.rigidRound
      cases locals : ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
          choices reducer root threshold problem with
      | some absent => intro impossible; cases impossible
      | none =>
          dsimp only
          rw [fullRound_eq]
          rcases firingAt with fired | ⟨_, fired, _⟩
          · rw [locals] at fired; cases fired
          · cases first : firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                certifyNormal headTypingUnique threshold problem with
            | none => rw [first] at fired; cases fired
            | some found => cases found <;> (intro impossible; cases impossible)
    · intro update smaller progressed
      change ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique threshold problem = .progress update smaller at progressed
      unfold ContextualDependentRigidDecomposition.rigidRound at progressed
      cases locals : ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
          choices reducer root threshold problem with
      | some absent => rw [locals] at progressed; cases progressed
      | none =>
          rw [locals] at progressed
          dsimp only at progressed
          rw [fullRound_eq] at progressed
          rcases firingAt with fired | ⟨_, fired, closed⟩
          · rw [locals] at fired; cases fired
          · cases first : firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                certifyNormal headTypingUnique threshold problem with
            | none => rw [first] at fired; cases fired
            | some found =>
                cases found with
                | solved solved smaller' =>
                    rw [first] at progressed
                    cases progressed
                    exact closed first
                | refuted absent => rw [first] at progressed; cases progressed

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
