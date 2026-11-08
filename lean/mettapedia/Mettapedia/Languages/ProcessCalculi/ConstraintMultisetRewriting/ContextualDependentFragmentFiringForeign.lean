import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentStoresPrepared

/-!
# The pattern and prune rules read only the newest metavariable

Recognition accepts a left side only when it is the pattern application of the newest
metavariable (`recognize_some_left`). For an equation read without leading abstractions, the
spine and the scope are both empty, and the newest metavariable is the variable `0`
(`stop_application_code`). So an equation whose two sides are other metavariables, or rigid
formers, is never read by the pattern or prune rule (`patternRule_foreign`, `pruneRule_foreign`).

This is the reach of newest-first elimination: a metavariable that a later declaration depends on
is solved neither directly nor after exchange or rotation, which both need it to be independent of
what comes after it.
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

section Recognition

variable {Head : Type} {rules : Rules Head} [DecidableEq Head]

/-- **Recognition reads exactly the pattern application**: a recognized left side is the pattern
application of the newest metavariable. -/
theorem recognize_some_left {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType) (active : Active scope.target)
    {recognized : Recognized spine scope active} (found : recognize spine scope active = some recognized) :
    ∃ pattern : Pattern spine scope, active.left.code = pattern.application.code := by
  unfold recognize at found
  split at found
  · cases found
  · split at found
    · cases found
    · split at found
      · cases found
      · split at found
        · split at found
          · dsimp only at found
            split at found
            · split at found
              · rename_i sameLeft
                exact ⟨_, sameLeft⟩
              · cases found
            · cases found
          · cases found
        · cases found

omit [DecidableEq Head] in
/-- Without leading abstractions and arguments, the pattern application is the newest variable. -/
theorem stop_application_code {Γ : Context rules} {type : TypeOver Γ} {scopeType : TypeOver (extend Γ type)}
    (pattern : Pattern (Spine.stop type) (Spine.stop scopeType)) :
    pattern.application.code = .var (0 : Fin (Γ.arity + 1)) := rfl

/-- **An argument-free left side that is not the newest variable is not recognized.** -/
theorem recognize_stop_foreign {Γ : Context rules} {type : TypeOver Γ} {scopeType : TypeOver (extend Γ type)}
    (active : Active (Spine.stop scopeType).target) {index : Fin (Γ.arity + 1)} (other : index ≠ 0)
    (leftCode : active.left.code = .var index) :
    recognize (Spine.stop type) (Spine.stop scopeType) active = none := by
  cases found : recognize (Spine.stop type) (Spine.stop scopeType) active with
  | none => rfl
  | some recognized =>
      obtain ⟨pattern, same⟩ := recognize_some_left _ _ active found
      rw [leftCode, stop_application_code] at same
      exact absurd (Tm.var.inj same) other

end Recognition

section Rules

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

/-- **A side the newest-variable rules cannot read**: silent, or a variable other than the newest. -/
def Foreign {n : Nat} (code : Tm Head n) : Prop :=
  Silent code ∨ ∃ index : Fin n, index.val ≠ 0 ∧ code = .var index

/-- **An equation read without leading abstractions**, with stopped sides that the
newest-variable rules cannot read. -/
def ForeignEquation {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Prop :=
  lamDepth equation.1.2.code = 0 ∧ ExecutableReduction.step S.R root equation.1.2.code = none ∧
    ExecutableReduction.step S.R root equation.2.2.code = none ∧ Foreign equation.1.2.code ∧ Foreign equation.2.2.code

/-- **The reading of an equation without leading abstractions and with stopped sides** is the
empty spine and the sides themselves. -/
theorem foreign_reading (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (foreign : ForeignEquation root equation) {reading}
    (read : viewEquation facts roots heads algebra declared choices reducer root fuel equation = some reading) :
    ∃ same : reading.1 = .stop equation.1.1, (same ▸ reading.2.1).left.code = equation.1.2.code ∧
      (same ▸ reading.2.1).right.code = equation.2.2.code := by
  obtain ⟨found, leftCode, right, rightSame, rightCode⟩ := viewEquation_codes facts roots heads algebra declared choices
    reducer root fuel equation read
  rw [foreign.1, ContextualDependentPiSpineDiscovery.discover_zero_arguments] at found
  obtain ⟨scope, active, view⟩ := reading
  change some (Spine.stop equation.1.1) = some scope at found
  cases found
  refine ⟨rfl, ?_, ?_⟩
  · change active.left.code = equation.1.2.code
    rw [leftCode]
    rcases normalizeAt_code facts roots heads root fuel ((Spine.stop equation.1.1).openFunction equation.1.2) with
      same | ⟨result, run, same⟩
    · exact same
    · rw [same]; exact normalize_stopped root foreign.2.1 run
  · change active.right.code = equation.2.2.code
    rw [rightCode]
    rcases normalizeAt_code facts roots heads root fuel ((Spine.stop equation.1.1).openFunction right) with
      same | ⟨result, run, same⟩
    · exact same.trans rightSame
    · have stoppedRight : ExecutableReduction.step S.R root right.code = none := by
        rw [rightSame]; exact foreign.2.2.1
      rw [same]; exact (normalize_stopped root stoppedRight run).trans rightSame

theorem tryActive_foreign (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (active : Active (Spine.stop scopeType).target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ ((Spine.stop scopeType).toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) (foreign : Foreign active.left.code) :
    tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel type
      (Spine.stop scopeType) active equation view rest = none := by
  rcases foreign with silent | ⟨index, other, isVar⟩
  · exact tryActive_silent rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
      fuel type _ active equation view rest silent
  · unfold tryActive
    split
    · rfl
    · rename_i head arguments read
      rw [isVar] at read
      simp only [readApplication, Option.some.injEq, Prod.mk.injEq] at read
      obtain ⟨_, rfl⟩ := read
      simp only [List.length_nil, ContextualDependentPiSpineDiscovery.discover_zero_arguments]
      rw [recognize_stop_foreign active (index := index) (fun same => other (congrArg Fin.val same)) isVar]

theorem pruneActive_foreign (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) {scopeType : TypeOver (extend (extend Γ₀ older) newer)}
    (active : Active (Spine.stop scopeType).target)
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ ((Spine.stop scopeType).toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) (foreign : Foreign active.left.code) :
    pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel older newer (Spine.stop scopeType) active equation view rest = none := by
  rcases foreign with silent | ⟨index, other, isVar⟩
  · exact pruneActive_unreadable rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer _ active equation view rest silent.unreadable
  · unfold pruneActive
    split
    · rfl
    · rename_i head arguments read
      rw [isVar] at read
      simp only [readApplication, Option.some.injEq, Prod.mk.injEq] at read
      obtain ⟨_, rfl⟩ := read
      simp only [List.length_nil, ContextualDependentPiSpineDiscovery.discover_zero_arguments]
      rw [recognize_stop_foreign active (index := index) (fun same => other (congrArg Fin.val same)) isVar]

theorem tryEquation_foreign (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type)))
    (foreign : ForeignEquation root equation) :
    tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel type
      equation rest = none := by
  unfold tryEquation
  split
  · rfl
  · rename_i scope active view read
    obtain ⟨same, leftIs, rightIs⟩ := foreign_reading facts roots heads algebra declared choices reducer root fuel equation
      foreign read
    change scope = Spine.stop equation.1.1 at same
    subst same
    change active.left.code = equation.1.2.code at leftIs
    change active.right.code = equation.2.2.code at rightIs
    rw [tryActive_foreign rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel
      type active equation view rest (by rw [leftIs]; exact foreign.2.2.2.1)]
    exact tryActive_foreign rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
      fuel type ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap _ active solution).symm) rest
      (by change Foreign active.right.code; rw [rightIs]; exact foreign.2.2.2.2)

/-- **The pattern rule never fires on a lone foreign equation.** -/
theorem patternRule_foreign (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (foreign : ForeignEquation root equation) :
    patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
      [equation] = none := by
  unfold patternRule
  split
  · rfl
  · rename_i view _
    rcases view with ⟨base, type, same⟩
    subst same
    show searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel type [equation] = none
    simp only [searchStore]
    rw [tryEquation_foreign rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel type equation [] foreign]
    rfl

/-- **The prune rule never fires on a lone foreign equation.** -/
theorem pruneRule_foreign (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (foreign : ForeignEquation root equation) :
    ContextualDependentPatternSolver.pruneRule rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal headTypingUnique fuel [equation] = none := by
  unfold ContextualDependentPatternSolver.pruneRule
  split
  · rfl
  · rename_i outer _
    split
    · rfl
    · rename_i inner _
      cases outer with
      | mk base newer same =>
          cases inner with
          | mk base₀ older same₀ =>
              change base = extend base₀ older at same₀
              subst same₀
              subst same
              show pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes
                certifyNormal headTypingUnique fuel older newer [equation] = none
              have single : pruneEquation rigid facts complete roots heads algebra declared choices reducer root
                  normalizes certifyNormal headTypingUnique fuel older newer equation [] = none := by
                unfold pruneEquation
                split
                · rfl
                · rename_i scope active view read
                  obtain ⟨same, leftIs, rightIs⟩ := foreign_reading facts roots heads algebra declared choices reducer
                    root fuel equation foreign read
                  change scope = Spine.stop equation.1.1 at same
                  subst same
                  change active.left.code = equation.1.2.code at leftIs
                  change active.right.code = equation.2.2.code at rightIs
                  rw [pruneActive_foreign rigid facts complete roots heads algebra declared choices reducer root
                    normalizes certifyNormal headTypingUnique fuel older newer active equation view []
                    (by rw [leftIs]; exact foreign.2.2.2.1)]
                  exact pruneActive_foreign rigid facts complete roots heads algebra declared choices reducer root
                    normalizes certifyNormal headTypingUnique fuel older newer ⟨active.type, active.right, active.left⟩
                    equation (fun solution => (view solution).trans (toScoped_swap _ active solution).symm) []
                    (by change Foreign active.right.code; rw [rightIs]; exact foreign.2.2.2.2)
              simp only [pruneSearch, single]
              rfl

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
theorem asLocal_foreign {Γ : Context S.R} (scopeType : TypeOver Γ) {code : Tm Head (Spine.stop scopeType).target.arity}
    (foreign : Foreign code) : ContextualDependentRigidDecomposition.asLocal (Spine.stop scopeType) code = none := by
  rcases foreign with silent | ⟨index, _, isVar⟩
  · exact asLocal_silent _ silent
  · rw [isVar]
    rfl

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
theorem asLocalApplication_foreign {Γ : Context S.R} (scopeType : TypeOver Γ)
    {code : Tm Head (Spine.stop scopeType).target.arity} (foreign : Foreign code) :
    ContextualDependentRigidDecomposition.asLocalApplication (Spine.stop scopeType) code = none := by
  rcases foreign with silent | ⟨index, _, isVar⟩
  · exact asLocalApplication_silent _ silent
  · rw [isVar]
    rfl

/-- **The distinct-locals rule never fires on a lone foreign equation.** -/
theorem localsRule_foreign (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (foreign : ForeignEquation root equation) :
    ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
      root fuel [equation] = none := by
  have single : ContextualDependentRigidDecomposition.localsClash rigid complete facts roots heads algebra declared
      choices reducer root fuel equation [] = none := by
    unfold ContextualDependentRigidDecomposition.localsClash
    split
    · rfl
    · rename_i scope active view read
      obtain ⟨same, leftIs, _⟩ := foreign_reading facts roots heads algebra declared choices reducer root fuel equation
        foreign read
      change scope = Spine.stop equation.1.1 at same
      subst same
      change active.left.code = equation.1.2.code at leftIs
      split
      · rename_i first second leftFound rightFound
        rw [asLocal_foreign _ (by rw [leftIs]; exact foreign.2.2.2.1)] at leftFound
        cases leftFound
      · rfl
  simp only [ContextualDependentRigidDecomposition.localsRule, single]
  rfl

/-- **Decomposition never fires on a lone foreign equation.** -/
theorem decomposeSearch_foreign (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (foreign : ForeignEquation root equation) :
    ContextualDependentRigidDecomposition.decomposeSearch rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel [equation] = none := by
  have single : ContextualDependentRigidDecomposition.decomposeEquation rigid facts complete roots heads algebra
      declared choices reducer root normalizes certifyNormal fuel equation [] = none := by
    unfold ContextualDependentRigidDecomposition.decomposeEquation
    split
    · rfl
    · rename_i scope active view read
      obtain ⟨same, leftIs, _⟩ := foreign_reading facts roots heads algebra declared choices reducer root fuel equation
        foreign read
      change scope = Spine.stop equation.1.1 at same
      subst same
      change active.left.code = equation.1.2.code at leftIs
      have none : ContextualDependentRigidDecomposition.decomposeActive facts complete roots heads algebra declared
          choices reducer fuel (Spine.stop equation.1.1) active = none := by
        unfold ContextualDependentRigidDecomposition.decomposeActive
        split
        · rename_i head left head' right leftFound rightFound
          rw [asLocalApplication_foreign _ (by rw [leftIs]; exact foreign.2.2.2.1)] at leftFound
          cases leftFound
        · rfl
      rw [none]
  simp only [ContextualDependentRigidDecomposition.decomposeSearch, single]
  rfl

/-- **The identity decomposition never fires on a lone equation whose left side is not an identity
type.** -/
theorem idDecomposeSearch_foreign (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (foreign : ForeignEquation root equation) (notIdentity : ∀ A a b, equation.1.2.code ≠ .id A a b) :
    idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      fuel [equation] = none := by
  have single : idDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal fuel equation [] = none := by
    unfold idDecomposeEquation
    split
    · rfl
    · rename_i scope active view read
      obtain ⟨same, leftIs, _⟩ := foreign_reading facts roots heads algebra declared choices reducer root fuel equation
        foreign read
      change scope = Spine.stop equation.1.1 at same
      subst same
      change active.left.code = equation.1.2.code at leftIs
      have none : idDecomposeActive facts roots heads algebra declared choices reducer fuel (Spine.stop equation.1.1)
          active = none := by
        unfold idDecomposeActive
        split
        · rename_i A a b A' a' b' u leftCode rightCode typeCode
          rw [leftIs] at leftCode
          exact absurd leftCode (notIdentity _ _ _)
        · rfl
      rw [none]
  simp only [idDecomposeSearch, single]
  rfl

/-- **Rotation never fires when no deep declaration can be moved past the later ones.** -/
theorem rotateRule_none (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (fixed : ∀ depth ∈ List.range' 2 (Θ.arity - 2), ContextualDependentPermutation.rotateRaw Θ.raw depth = none) :
    ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel problem = none := by
  unfold ContextualDependentPermutation.rotateRule
  suffices search : ∀ depths : List Nat, (∀ depth ∈ depths, ContextualDependentPermutation.rotateRaw Θ.raw depth = none) →
      ContextualDependentPermutation.rotateSearch rigid complete facts roots heads algebra declared choices reducer root
        normalizes certifyNormal fuel problem depths = none from search _ fixed
  intro depths
  induction depths with
  | nil => intro _; rfl
  | cons depth rest ih =>
      intro allFixed
      simp only [ContextualDependentPermutation.rotateSearch]
      have here : ContextualDependentPermutation.rotateAt rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal fuel depth problem = none := by
        unfold ContextualDependentPermutation.rotateAt
        rw [allFixed depth List.mem_cons_self]
      rw [here]
      exact ih fun other member => allFixed other (List.mem_cons_of_mem _ member)

/-- **The worklist round is stuck on a lone equation** without a clash, that the conversion scan
never discharges and from which the dispatcher never solves the newest declaration. -/
theorem worklistRound_stuck_of_scan (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (noClash : ContextualDependentRigid.storeClashes [equation] = false)
    (unequal : ¬ Equal S.R Θ.raw equation.1.2.code equation.2.2.code equation.1.1.code)
    (noSearch : ∀ view : Newest Θ, ∀ moved : Equation (TotalTerm (extend view.base view.type)), HEq moved equation →
      ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel view.type [moved] =
        none) :
    ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel [equation] =
      .stuck := by
  have kept : Conversion.scan facts roots heads algebra reducer fuel [equation] = [equation] := by
    simp only [Conversion.scan]
    cases compared : Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2 with
    | none => rfl
    | some same => exact absurd same.down.2 unequal
  unfold ContextualDependentWorklist.round
  rw [dif_neg (by rw [noClash]; decide), dif_neg (by rw [kept]; exact Nat.lt_irrefl _)]
  split
  · rfl
  · rename_i view _
    have none : ContextualDependentWorklist.throughNewest view [equation]
        (dispatchNewest facts roots heads algebra declared choices reducer fuel view.type) = none := by
      have searchNone := noSearch view
      rcases view with ⟨base, type, same⟩
      subst same
      show dispatchNewest facts roots heads algebra declared choices reducer fuel type [equation] = none
      have mapped := dispatchNewest_val facts roots heads algebra declared choices reducer fuel type [equation]
      rw [searchNone equation HEq.rfl, Option.map_none] at mapped
      exact Option.map_eq_none_iff.mp mapped
    rw [none]

end Rules

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
