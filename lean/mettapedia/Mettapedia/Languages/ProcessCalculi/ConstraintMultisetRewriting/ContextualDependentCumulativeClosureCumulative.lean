import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureRotate

/-!
# Closure of the cumulative round: R110's cumulative rule

R110's cumulative rule (`ContextualDependentCumulative.cumulativeRule`) reads an equation under exactly one abstraction
(`oneBinder`), retypes the local to `F`'s binder (checking the same codes under the larger universe), and runs R107's
conversion pattern step on the retyped reading. The retyped reading has the original codes (`retypeAt_right`) and one
local, so its right side has Miller normal forms whenever the original reading's does (`oneBinder_sides`); the step
then drops the equation (`cumulativeActive_drops`), and the rule keeps the permuted class (`cumulativeRule_keeps`).

`oneBinder` matches the reading's spine by overlapping patterns on a dependently indexed family, for which no splitter
is derived; `oneBinder_sides` cases on the inner spine through `Spine.casesOn` with an explicit motive that remembers
the index by equations.
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
open ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A reading under exactly one abstraction has Miller sides at one local**, when the reading has them. -/
theorem oneBinder_sides {Θ : Context S.R} {whole : TypeOver Θ} (scope : Spine whole) (active : Active scope.target)
    {found : (domain : TypeOver Θ) × (opened : Active (extend Θ domain)) ×'
      ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (scope.toScoped active).Holds σ ↔
        (Scoped.bind domain (.active opened)).Holds σ}
    (read : oneBinder scope active = some found)
    (sides : ∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    ∀ N, Star (R := S.R) found.2.1.right.code N → Normal S.R N → miller (openedFlexible 1) N = true := by
  cases scope with
  | stop _ => cases read
  | bind shape rest =>
      revert active found read sides
      refine Spine.casesOn (motive := fun {Γ'} t' (inner : Spine t') =>
        ∀ (sameContext : Γ' = extend Θ shape.domain) (sameType : HEq t' shape.codomain) (sameSpine : HEq inner rest),
          ∀ (active : Active (Spine.bind shape rest).target)
            {found : (domain : TypeOver Θ) × (opened : Active (extend Θ domain)) ×'
              ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), ((Spine.bind shape rest).toScoped active).Holds σ ↔
                (Scoped.bind domain (.active opened)).Holds σ},
            oneBinder (Spine.bind shape rest) active = some found →
            (∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
              miller (ContextualDependentShortClosure.spineMark (Spine.bind shape rest)) N = true) →
            ∀ N, Star (R := S.R) found.2.1.right.code N → Normal S.R N → miller (openedFlexible 1) N = true)
        rest ?_ ?_ rfl HEq.rfl HEq.rfl
      · intro Γ' type sameContext sameType sameSpine
        subst sameContext
        obtain rfl := eq_of_heq sameType
        obtain rfl := eq_of_heq sameSpine
        intro active found read sides
        cases read
        exact sides
      · intro Γ' inner innerRest sameContext sameType sameSpine
        subst sameContext
        obtain ⟨domain, codomain, innerWhole, code⟩ := inner
        obtain rfl := eq_of_heq sameType
        obtain rfl := eq_of_heq sameSpine
        intro active found read
        cases read

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

/-- **Retyping keeps the right side's code.** -/
theorem retypeAt_right (fuel : Nat) {Θ : Context S.R} (domain : TypeOver Θ) (opened : Active (extend Θ domain))
    (u : Head)
    {found : (binder : TypeOver Θ) × (retyped : Active (extend Θ binder)) ×'
      ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
        (Scoped.bind domain (.active opened)).Holds σ ↔ (Scoped.bind binder (.active retyped)).Holds σ}
    (read : retypeAt facts roots heads algebra rigid complete declared choices reducer fuel domain opened u =
      some found) :
    found.2.1.right.code = opened.right.code := by
  unfold retypeAt at read
  split at read
  · split at read
    · split at read
      · cases read
      · split at read
        · cases read
        · split at read
          · rename_i left right _ _
            cases read
            exact right.2
          · cases read
    · cases read
  · cases read

include rigid in
/-- **The cumulative rule on one reading drops the equation** when the reading's right side has Miller normal forms. -/
theorem cumulativeActive_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) {whole : TypeOver (extend Γ type)} (scope : Spine whole)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (sides : ∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    SolvedDrops (cumulativeActive facts roots heads algebra rigid complete declared choices reducer normalizes
      certifyNormal fuel type scope active equation view rest) := by
  intro update smaller fired
  unfold cumulativeActive at fired
  split at fired
  · split at fired
    · cases fired
    · rename_i domain opened readOpened readOne
      split at fired
      · cases fired
      · rename_i binder retyped same readRetype
        split at fired
        · cases fired
        · rename_i whole' _
          refine ContextualDependentCumulativeClosure.tryActiveConv_drops facts roots heads algebra declared choices
            reducer rigid complete normalizes certifyNormal sn fuel type
            (Spine.bind ⟨binder, retyped.type, whole'.1, whole'.2⟩ (.stop retyped.type)) retyped equation
            (fun solution => (view solution).trans ((readOpened solution).trans (same solution))) rest ?_ update
            smaller fired
          have onOpened := oneBinder_sides scope active readOne sides
          rw [retypeAt_right facts roots heads algebra rigid complete declared choices reducer fuel _ _ _ readRetype]
          exact onOpened
  · cases fired

include rigid in
theorem cumulativeEquation_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) (sides : FragmentSidesMiller equation) :
    SolvedDrops (cumulativeEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal fuel type equation rest) := by
  intro update smaller fired
  unfold cumulativeEquation at fired
  split at fired
  · cases fired
  rename_i scope active view read
  have readSides := viewEquation_sides facts roots heads algebra declared choices reducer root rigid fuel equation
    sides read
  dsimp only at fired readSides
  split at fired
  · rename_i inner computed
    cases fired
    exact cumulativeActive_drops facts roots heads algebra rigid complete declared choices reducer normalizes
      certifyNormal sn fuel type scope active equation view rest readSides.2 update smaller computed
  · exact cumulativeActive_drops facts roots heads algebra rigid complete declared choices reducer normalizes
      certifyNormal sn fuel type scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest readSides.1 update
      smaller fired

include rigid in
theorem cumulativeSearch_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ (problem : EquationStore (TotalTerm (extend Γ type))), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      SolvedDrops (cumulativeSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal fuel type problem)
  | [], _ => fun _ _ fired => by cases fired
  | equation :: rest, sides => by
      intro update smaller fired
      simp only [cumulativeSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact cumulativeEquation_drops facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal sn fuel type equation rest (sides equation List.mem_cons_self) update smaller
          computed
      · exact solvedDrops_keepLeft equation (cumulativeSearch_drops sn fuel type rest
          fun other member => sides other (List.mem_cons_of_mem _ member)) update smaller fired

include rigid in
/-- **R110's cumulative rule keeps the permuted class** on a strongly normalizing package. -/
theorem cumulativeRule_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      cumulativeRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel problem := by
  intro Θ problem permuted
  refine foundKeeps_of_drops rigid sn permuted ?_
  dsimp only
  unfold cumulativeRule
  split
  · exact fun _ _ fired => by cases fired
  · rename_i view _
    rcases view with ⟨base, newer, same⟩
    subst same
    exact cumulativeSearch_drops facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel newer problem fun _ member => permuted.sides_of_mem member

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
