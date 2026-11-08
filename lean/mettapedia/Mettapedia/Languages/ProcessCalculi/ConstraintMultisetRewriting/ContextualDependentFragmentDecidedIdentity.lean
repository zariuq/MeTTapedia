import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentStoresPrepared
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentPruneKept

/-!
# A refutation by identity decomposition, found at one budget, is kept

When, at one budget, the scoped reading of an equation, the formation of the identity carrier, the
readings of both endpoint equations, and the distinct-locals test on the first endpoint equation
all finish, the identity decomposition refutes the equation at that budget and at every larger one
(`identityFirm_kept`). The firmness test is a boolean the kernel evaluates.

On a store whose context and codes are stopped, preparation is the pending update, so the identity
round then refutes the store at every larger budget, and the identity family **decides** it at one
joint budget (`identity_decided_of_firm`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentPatternSolver ContextualDependentGeneralPattern
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- The identity decomposition reads the budget only through the formation of its carrier. -/
theorem idDecomposeActive_congr {fuel larger : Nat} {Γ : Context S.R} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) (active : Active scope.target)
    (same : ∀ A a b, active.left.code = .id A a b →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel scope.target A =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer larger scope.target A) :
    idDecomposeActive facts roots heads algebra declared choices reducer fuel scope active =
      idDecomposeActive facts roots heads algebra declared choices reducer larger scope active := by
  unfold idDecomposeActive
  split
  · rename_i A a b A' a' b' u leftCode rightCode typeCode
    split
    · split
      · rw [same A a b leftCode]
      · rfl
    · rfl
  · rfl

/-- The carrier of an identity left side is formed at a budget. -/
def carrierFirm (budget : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) : Bool :=
  match active.left.code with
  | .id A _ _ => (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer budget
      scope.target A).isSome
  | _ => true

/-- **The identity refutation of one equation needs no more budget.** -/
def identityFirm (budget : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Bool :=
  readingFirm facts roots heads algebra declared choices reducer root budget equation &&
  match viewEquation facts roots heads algebra declared choices reducer root budget equation with
  | none => false
  | some ⟨scope, active, _⟩ =>
      carrierFirm facts roots heads algebra declared choices reducer budget scope active &&
      match idDecomposeActive facts roots heads algebra declared choices reducer budget scope active with
      | none => false
      | some ⟨(first, second), _⟩ =>
          match (scope.toScoped first).closeWith S.levels choices, (scope.toScoped second).closeWith S.levels choices with
          | some firstClosed, some secondClosed =>
              readingFirm facts roots heads algebra declared choices reducer root budget firstClosed.equation &&
              (ContextualDependentRigidDecomposition.localsClash rigid complete facts roots heads algebra declared choices
                reducer root budget firstClosed.equation (secondClosed.equation :: rest)).isSome
          | _, _ => false

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- A rule outcome that is a refutation. -/
def refutedB {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} : Option (Found problem) → Bool
  | some (.refuted _) => true
  | _ => false

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **A firm identity refutation is kept**: at every larger budget the identity decomposition of
the equation refutes it. -/
theorem identityFirm_kept {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ))
    {budget : Nat}
    (firm : identityFirm facts roots heads algebra declared choices reducer rigid complete root budget equation rest =
      true) :
    ∀ larger, budget ≤ larger →
      refutedB (idDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal larger equation rest) = true := by
  intro larger enough
  unfold identityFirm at firm
  simp only [Bool.and_eq_true] at firm
  obtain ⟨readFirm, afterRead⟩ := firm
  have viewKept := readingFirm_kept facts roots heads algebra declared choices reducer root stable equation readFirm
    larger enough
  unfold idDecomposeEquation
  rw [viewKept]
  cases viewed : viewEquation facts roots heads algebra declared choices reducer root budget equation with
  | none => rw [viewed] at afterRead; cases afterRead
  | some reading =>
      obtain ⟨scope, active, view⟩ := reading
      rw [viewed] at afterRead
      dsimp only at afterRead ⊢
      simp only [Bool.and_eq_true] at afterRead
      obtain ⟨formFirm, afterForm⟩ := afterRead
      have activeKept : idDecomposeActive facts roots heads algebra declared choices reducer larger scope active =
          idDecomposeActive facts roots heads algebra declared choices reducer budget scope active := by
        apply (idDecomposeActive_congr facts roots heads algebra declared choices reducer scope active ?_).symm
        intro A a b leftCode
        unfold carrierFirm at formFirm
        rw [leftCode] at formFirm
        obtain ⟨formed, formedRun⟩ := Option.isSome_iff_exists.mp formFirm
        rw [formedRun, ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer
          stable formedRun enough]
      rw [activeKept]
      cases decomposed : idDecomposeActive facts roots heads algebra declared choices reducer budget scope active with
      | none => rw [decomposed] at afterForm; cases afterForm
      | some found =>
          obtain ⟨⟨first, second⟩, split⟩ := found
          rw [decomposed] at afterForm
          dsimp only at afterForm ⊢
          split
          · rename_i firstClosed secondClosed firstComputed secondComputed
            rw [firstComputed, secondComputed] at afterForm
            dsimp only at afterForm
            simp only [Bool.and_eq_true] at afterForm
            obtain ⟨closedFirm, clash⟩ := afterForm
            have closedKept := readingFirm_kept facts roots heads algebra declared choices reducer root stable
              firstClosed.equation closedFirm larger enough
            obtain ⟨absent, clashRun⟩ := Option.isSome_iff_exists.mp clash
            have clashKept : ContextualDependentRigidDecomposition.localsClash rigid complete facts roots heads
                algebra declared choices reducer root larger firstClosed.equation (secondClosed.equation :: rest) =
                  some absent := by
              rw [← clashRun]
              unfold ContextualDependentRigidDecomposition.localsClash
              erw [closedKept]
            have localsFire : ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra
                declared choices reducer root larger (firstClosed.equation :: secondClosed.equation :: rest) =
                  some absent := by
              simp only [ContextualDependentRigidDecomposition.localsRule, clashKept]
            rw [localsFire]
            rfl
          · rename_i notBoth
            exfalso
            cases firstComputed : (scope.toScoped first).closeWith S.levels choices with
            | none => rw [firstComputed] at afterForm; cases afterForm
            | some firstClosed =>
                cases secondComputed : (scope.toScoped second).closeWith S.levels choices with
                | none => rw [firstComputed, secondComputed] at afterForm; cases afterForm
                | some secondClosed => exact notBoth firstClosed secondClosed firstComputed secondComputed

/-! ## The identity round on a stopped store -/

variable (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- What the identity round commits, from the prepared update, the identity search and the fragment
round. -/
def identityView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem)
    (found : Option (Found prepared.remaining)) (otherwise : Option (Option (Update S.levels problem))) :
    Option (Option (Update S.levels problem)) :=
  match foundView found with
  | some committed => some (committed.map fun update => prepared.then update)
  | none => otherwise

/-- The identity round, read through its view. -/
theorem identityRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem) =
      identityView (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem)
        (idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel
            problem).remaining)
        (roundView (fragmentRound rigid facts complete roots heads algebra declared choices reducer root
          rootComplete normalizes certifyNormal headTypingUnique fuel problem)) := by
  unfold identityRound identityView
  split
  · rename_i update smaller computed
    simp only [computed, roundView, foundView, Option.map_some]
  · rename_i absent computed
    simp only [computed, roundView, foundView, Option.map_none]
  · rename_i computed
    first | rfl | simp only [computed, foundView]

include stable in
/-- **On a stopped one-equation store, a firm identity refutation makes the identity round refute
at every larger budget.** -/
theorem identityRound_refuted_of_firm {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (context : StoppedContext root Θ.raw)
    (codes : ∀ other ∈ [equation], StoppedTerm root other.1 ∧ StoppedTerm root other.2) {budget : Nat}
    (firm : identityFirm facts roots heads algebra declared choices reducer rigid complete root budget equation [] =
      true) :
    ∀ larger, budget ≤ larger → ∃ absent,
      identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete larger [equation] = .refuted absent := by
  intro larger enough
  have refutes := identityFirm_kept facts roots heads algebra declared choices reducer rigid complete root
    normalizes certifyNormal stable equation [] firm larger enough
  obtain ⟨absent, refuted⟩ : ∃ absent, idDecomposeEquation facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal larger equation [] = some (.refuted absent) := by
    cases computed : idDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal larger equation [] with
    | none => rw [computed] at refutes; cases refutes
    | some found =>
        cases found with
        | solved update smaller => rw [computed] at refutes; cases refutes
        | refuted absent => exact ⟨absent, rfl⟩
  have searched : ∃ absent, idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal larger (ContextualDependentNormalizing.prepare root rootComplete facts roots heads larger
        [equation]).remaining = some (.refuted absent) := by
    rw [prepare_stopped root rootComplete facts roots heads larger [equation] context codes]
    exact ⟨absent, by simp only [Update.pending, idDecomposeSearch, refuted]⟩
  obtain ⟨absent', computed⟩ := searched
  unfold identityRound
  split
  · rename_i update smaller found
    rw [computed] at found
    cases found
  · rename_i absent'' _
    exact ⟨fun solvable => absent'' ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads larger
      [equation]).solvable_iff.mp solvable), rfl⟩
  · rename_i found
    rw [computed] at found
    cases found

include stable in
/-- **A stopped one-equation store with a firm identity refutation is decided by the identity
family at one joint budget**: from one budget on, the run refutes it with a certificate. -/
def identitySettled {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (context : StoppedContext root Θ.raw)
    (codes : ∀ other ∈ [equation], StoppedTerm root other.1 ∧ StoppedTerm root other.2) {budget : Nat}
    (firm : identityFirm facts roots heads algebra declared choices reducer rigid complete root budget equation [] =
      true) :
    ContextualDependentDecisiveDriver.Settled
      (identityFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) where
  holds := fun {Γ} problem => ∃ same : Γ = Θ, same ▸ problem = [equation]
  settles := by
    intro Γ problem inside _
    obtain ⟨same, isStore⟩ := inside
    subst same
    subst isStore
    have refutes := identityRound_refuted_of_firm facts roots heads algebra declared choices reducer rigid complete
      root normalizes certifyNormal headTypingUnique stable rootComplete equation context codes firm
    obtain ⟨absent, atBudget⟩ := refutes budget le_rfl
    refine ⟨budget, ?_, fun fuel enough => ?_, ?_⟩
    · change identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique rootComplete budget [equation] ≠ .stuck
      rw [atBudget]
      intro impossible
      cases impossible
    · change identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique rootComplete fuel [equation] =
          identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete budget [equation]
      obtain ⟨absent', atFuel⟩ := refutes fuel enough
      rw [atFuel, atBudget]
    · intro update smaller progressed
      change identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique rootComplete budget [equation] = .progress update smaller at progressed
      rw [atBudget] at progressed
      cases progressed

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
