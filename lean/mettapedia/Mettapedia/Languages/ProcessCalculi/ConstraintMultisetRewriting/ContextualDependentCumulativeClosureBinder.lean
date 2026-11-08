import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureIdentity

/-!
# Closure of the cumulative round: R98's decomposition of Π and Σ types

R98's binder rule (`ContextualDependentFragment.piDecomposeSearch`) reads `Π A B ≐ Π A B'` (or `Σ A B ≐ Σ A B'`) at a
universe, replaces the equation by the closed codomain equation `λ z̄ x. B ≐ λ z̄ x. B'` under the domain, and runs
R75's pattern rule. The codomains are the codomains of the reading's binder types (`binderDecomposeActive_reduct`); a
normal form of `Π A B` is a Π type of normal forms, so the codomains have Miller normal reducts with the new local rigid
(`codomain_reduct`). Closing a scoped body under the reading's locals keeps such reducts (`closeWith_scopedReduct`,
`scopeWith_scopedReduct`), and the rule keeps the permuted class (`piDecomposeSearch_keeps`).
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
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Scoped bodies with Miller normal reducts -/

section Scoped

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **A scoped constraint whose codes have Miller normal reducts**, each binder's local rigid. -/
def ScopedReduct : {Γ : Context rules} → (Fin Γ.arity → Bool) → Scoped Γ → Prop
  | _, mark, .active equation => MarkedReduct rules mark equation.left.code ∧ MarkedReduct rules mark equation.right.code
  | _, mark, .bind _ body => ScopedReduct (liftFlexible mark) body

variable (empty : rules.computation = RootComputation.empty) (choices : ExecutableChecking.HeadChoices rules)

include empty in
/-- **Closing a scoped constraint keeps Miller normal reducts.** -/
theorem closeWith_scopedReduct : ∀ {Γ : Context rules} (mark : Fin Γ.arity → Bool) (constraint : Scoped Γ)
    {closed : Active Γ}, constraint.closeWith levels choices = some closed → ScopedReduct mark constraint →
    MarkedReduct rules mark closed.left.code ∧ MarkedReduct rules mark closed.right.code
  | _, _, .active equation, closed, computed, reducts => by
      cases computed
      exact reducts
  | _, mark, .bind domain body, closed, computed, reducts => by
      unfold Scoped.closeWith at computed
      obtain ⟨inner, innerComputed, computed⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨result, _, computed⟩ := Option.bind_eq_some_iff.mp computed
      cases computed
      obtain ⟨left, right⟩ := closeWith_scopedReduct (liftFlexible mark) body innerComputed reducts
      exact ⟨MarkedReduct.lam empty left, MarkedReduct.lam empty right⟩

/-- **A body under a spine's binders**: Miller normal reducts at the scope's marking. -/
theorem scopeWith_scopedReduct : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (mark : Fin Γ.arity → Bool) (body : Scoped spine.target),
    ScopedReduct (scopeMark mark spine) body → ScopedReduct mark (ContextualDependentFragment.scopeWith spine body)
  | _, _, .stop _, _, _, reducts => reducts
  | _, _, .bind _ rest, mark, body, reducts => scopeWith_scopedReduct rest (liftFlexible mark) body reducts

include empty in
/-- **A closed body under a reading's locals has Miller sides.** -/
theorem closedBody_sides {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (body : Scoped scope.target)
    {closed : Active Γ}
    (computed : (ContextualDependentFragment.scopeWith scope body).closeWith levels choices = some closed)
    (reducts : ScopedReduct (ContextualDependentShortClosure.spineMark scope) body) :
    FragmentSidesMiller closed.equation := by
  have marking : scopeMark (fun _ => true) scope = ContextualDependentShortClosure.spineMark scope :=
    funext (scopeMark_spineMark scope)
  rw [← marking] at reducts
  obtain ⟨left, right⟩ := closeWith_scopedReduct empty choices (fun _ => true) _ computed
    (scopeWith_scopedReduct scope (fun _ => true) body reducts)
  exact sides_of_reducts empty left right

end Scoped

/-! ## The codomains of binder types -/

section Codomains

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The codomain of a Π type with Miller normal forms has a Miller normal reduct**, the new local rigid. -/
theorem pi_codomain_reduct (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R} {type : TypeOver Θ}
    (term : Term Θ type) {mark : Fin Θ.arity → Bool} {A : Tm Head Θ.arity} {B : Tm Head (Θ.arity + 1)}
    (code : term.code = .pi A B) (sides : ∀ N, Star (R := S.R) term.code N → Normal S.R N → miller mark N = true) :
    MarkedReduct S.R (liftFlexible mark) B := by
  have empty := computation_empty rigid
  obtain ⟨N, toN, normalN⟩ := ContextualDependentOpenedNormal.term_normal sn term
  have millerN := sides N toN normalN
  rw [code] at toN
  obtain ⟨A', B', rfl, _, toB⟩ := star_pi_inv empty toN
  obtain ⟨_, normalB⟩ := (normal_pi_iff empty).mp normalN
  simp only [miller, Bool.and_eq_true] at millerN
  exact ⟨B', toB, normalB, millerN.2⟩

/-- **The codomain of a Σ type with Miller normal forms has a Miller normal reduct**, the new local rigid. -/
theorem sigma_codomain_reduct (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R} {type : TypeOver Θ}
    (term : Term Θ type) {mark : Fin Θ.arity → Bool} {A : Tm Head Θ.arity} {B : Tm Head (Θ.arity + 1)}
    (code : term.code = .sigma A B) (sides : ∀ N, Star (R := S.R) term.code N → Normal S.R N → miller mark N = true) :
    MarkedReduct S.R (liftFlexible mark) B := by
  have empty := computation_empty rigid
  obtain ⟨N, toN, normalN⟩ := ContextualDependentOpenedNormal.term_normal sn term
  have millerN := sides N toN normalN
  rw [code] at toN
  obtain ⟨A', B', rfl, _, toB⟩ := star_sigma_inv empty toN
  obtain ⟨_, normalB⟩ := (normal_sigma_iff empty).mp normalN
  simp only [miller, Bool.and_eq_true] at millerN
  exact ⟨B', toB, normalB, millerN.2⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

include rigid in
theorem piDecomposeActive_reduct (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType) (active : Active scope.target)
    {found : {body : Scoped scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (ContextualDependentFragment.scopeWith scope body).Holds solution}}
    (read : piDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
      some found)
    (left : ∀ N, Star (R := S.R) active.left.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true)
    (right : ∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    ScopedReduct (ContextualDependentShortClosure.spineMark scope) found.val := by
  unfold piDecomposeActive at read
  split at read
  · rename_i A B A' B' u leftCode rightCode _
    split at read
    · split at read
      · split at read
        · cases read
        · split at read
          · split at read
            · cases read
            · split at read
              · cases read
              · cases read
                exact ⟨pi_codomain_reduct rigid sn active.left leftCode left,
                  pi_codomain_reduct rigid sn active.right rightCode right⟩
          · cases read
      · cases read
    · cases read
  · cases read

include rigid in
theorem sigmaDecomposeActive_reduct (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType) (active : Active scope.target)
    {found : {body : Scoped scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (ContextualDependentFragment.scopeWith scope body).Holds solution}}
    (read : sigmaDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
      some found)
    (left : ∀ N, Star (R := S.R) active.left.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true)
    (right : ∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    ScopedReduct (ContextualDependentShortClosure.spineMark scope) found.val := by
  unfold sigmaDecomposeActive at read
  split at read
  · rename_i A B A' B' u leftCode rightCode _
    split at read
    · split at read
      · split at read
        · cases read
        · split at read
          · split at read
            · cases read
            · split at read
              · cases read
              · cases read
                exact ⟨sigma_codomain_reduct rigid sn active.left leftCode left,
                  sigma_codomain_reduct rigid sn active.right rightCode right⟩
          · cases read
      · cases read
    · cases read
  · cases read

include rigid in
theorem binderDecomposeActive_reduct (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType) (active : Active scope.target)
    {found : {body : Scoped scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (ContextualDependentFragment.scopeWith scope body).Holds solution}}
    (read : binderDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
      some found)
    (left : ∀ N, Star (R := S.R) active.left.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true)
    (right : ∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    ScopedReduct (ContextualDependentShortClosure.spineMark scope) found.val := by
  unfold binderDecomposeActive at read
  cases computed : piDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active with
  | some pi =>
      rw [computed, Option.some_or] at read
      cases read
      exact piDecomposeActive_reduct facts roots heads algebra rigid complete declared choices reducer sn fuel scope
        active computed left right
  | none =>
      rw [computed, Option.none_or] at read
      exact sigmaDecomposeActive_reduct facts roots heads algebra rigid complete declared choices reducer sn fuel scope
        active read left right

end Codomains

/-! ## The rule -/

section Rule

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

include rigid in
/-- **R98's binder decomposition of one equation is stable.** -/
theorem piDecomposeEquation_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ))
    (sides : FragmentSidesMiller equation) :
    SolvedStable (piDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal fuel equation rest) := by
  have empty := computation_empty rigid
  intro update smaller fired
  unfold piDecomposeEquation at fired
  split at fired
  · cases fired
  rename_i scope active view read
  have readSides := viewEquation_sides facts roots heads algebra declared choices reducer root rigid fuel equation
    sides read
  dsimp only at readSides
  split at fired
  · cases fired
  rename_i body split readBody
  split at fired
  · cases fired
  rename_i closed computed
  dsimp only at fired
  split at fired
  · cases fired
  split at fired
  · rename_i solved solvedSmaller computedPattern
    cases fired
    have reducts := binderDecomposeActive_reduct facts roots heads algebra rigid complete declared choices reducer sn
      fuel scope active readBody readSides.1 readSides.2
    refine StableKeeps.then (replaced_stable [closed.equation] (fun σ => ?_) ?_ ?_ _) ?_
    · exact ((Active.holds_iff_models S.levels closed σ).symm.trans
        ((Scoped.closeWith_holds_iff S.levels choices _ computed σ).trans
          ((split σ).symm.trans (view σ).symm))).trans (models_singleton σ equation)
    · intro piece member
      rw [List.mem_singleton.mp member]
      exact closedBody_sides empty choices scope body computed reducts
    · intro piece member
      rw [List.mem_singleton.mp member]
      rfl
    · exact patternRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal sn fuel _ solved solvedSmaller computedPattern
  · cases fired
  · cases fired

include rigid in
theorem piDecomposeSearch_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      SolvedStable (piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal fuel problem)
  | [], _ => fun _ _ fired => by cases fired
  | equation :: rest, sides => by
      intro update smaller fired
      simp only [piDecomposeSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact piDecomposeEquation_stable facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal sn fuel equation rest (sides equation List.mem_cons_self) update smaller computed
      · exact solvedStable_keepLeft equation (piDecomposeSearch_stable sn fuel rest
          fun other member => sides other (List.mem_cons_of_mem _ member)) update smaller fired

include rigid in
/-- **R98's binder decomposition keeps the permuted class** on a strongly normalizing package. -/
theorem piDecomposeSearch_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted
    (piDecomposeSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel problem fun _ member => permuted.sides_of_mem member)

end Rule

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
