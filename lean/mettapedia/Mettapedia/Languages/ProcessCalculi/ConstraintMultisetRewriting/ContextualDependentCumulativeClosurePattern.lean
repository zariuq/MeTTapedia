import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureAnswer

/-!
# Closure of the cumulative round: R107's conversion pattern rule

R107's conversion pattern rule (`ContextualDependentRecognitionConversion.patternRuleConv`) reads an equation under its
abstractions (`viewEquation`), recognizes `F x̄ ≐ t` for the newest metavariable `F`, inverts `t` along the argument
map to a body `u` over `F`'s telescope, and answers `F := λ z̄. u` (`Pattern.step`, `Pattern.replace`). It keeps the
permuted class (`patternRuleConv_keeps`):

* **the reading has Miller sides**: the opened sides the rule reads are reducts of the fragment's openings, so their
  normal forms are Miller, with the outer variables flexible and the locals rigid (`viewEquation_sides`);
* **the answer reduces to a pattern answer**: `u` has a normal form (strong normalization), its image along the
  argument map is a normal form of `t`, hence Miller, and Miller occurrences reflect along the injective map, which
  sends outer variables to outer variables and binders to locals (`abstractBody_reducing`, `newestReducing`);
* **the update drops the equation**: the residual is the rest of the store, instantiated, and the answer makes the
  equation valid (`combine_drops`), through both orientations, the store search and the newest declaration.
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
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentClosure
open ContextualDependentDynamicFragment ContextualDependentHereditary ExecutableReduction
open ContextualDependentExecutableJoin ContextualDependentPiSpine ContextualDependentGeneralPattern
open ContextualDependentScope

/-! ## Values with Miller normal forms -/

section Values

variable {Head : Type} {R : Rules Head}

theorem star_lamsVar {o : Nat} : ∀ (count : Nat) {t t' : Tm Head (o + count)}, Star (R := R) t t' →
    Star (R := R) (lamsVar count t) (lamsVar count t')
  | 0, _, _, steps => steps
  | count + 1, _, _, steps => star_lamsVar count (star_map Tm.lam (fun step => .congLam step) steps)

/-- **The newest metavariable answered by a value with a normal Miller reduct reduces to a pattern answer.** -/
theorem newestReducing {Γ : Context R} {type : TypeOver Γ}
    (value : Term Γ type) {v : Tm Head Γ.arity} (toV : Star (R := R) value.code v) (normal : Normal R v)
    (millerV : miller (fun _ => true) v = true) :
    ReducingAnswer R (ContextualDependentEta.Elimination.instantiate Γ value).substitution := by
  refine ⟨consSub v ids, fun i => ?_, ⟨?_⟩⟩
  · change Star (R := R) (consSub (value.cast type.reindex_id.symm).code ids i) (consSub v ids i)
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [consSub_zero, Term.cast_code]
      exact toV
    · simp only [consSub_succ]
      exact .refl
  · exact
      { target := 0
        flexibleTarget := rfl
        rename := fun i hi => i.pred hi
        injective := fun _ _ _ _ same => Fin.pred_inj.mp same
        respects := fun _ _ => rfl
        others := by
          intro i hi
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨prior, rfl⟩
          · exact absurd rfl hi
          · rw [Fin.pred_succ]
            rfl
        outerArity := Γ.arity
        outer := idRen
        outerInjective := fun _ _ same => same
        outerFlexible := fun _ => rfl
        value := v
        solution := (rename_id v).symm
        valueMiller := millerV
        valueNormal := normal }

/-- **An opened side read through a spine**: every normal form of a reduct of the opening has Miller occurrences with
the outer variables flexible and the spine's locals rigid, when every normal form of the opening does. -/
theorem opened_miller (empty : R.computation = RootComputation.empty) {Γ : Context R} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) (side : Tm Head Γ.arity) {code : Tm Head scope.target.arity}
    (steps : Star (R := R) (Presentation.rename (Fin.cast scope.target_arity.symm) (openCode scope.length side)) code)
    (inside : ∀ N, Star (R := R) (openCode scope.length side) N → Normal R N →
      miller (openedFlexible scope.length) N = true) :
    ∀ N, Star (R := R) code N → Normal R N → miller (ContextualDependentShortClosure.spineMark scope) N = true := by
  intro N toN normalN
  have cancel : Presentation.rename (Fin.cast scope.target_arity)
      (Presentation.rename (Fin.cast scope.target_arity.symm) (openCode scope.length side)) =
        openCode scope.length side := by
    rw [rename_comp]
    exact (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)
  have back := star_rename (R := R) (Fin.cast scope.target_arity) (steps.trans toN)
  rw [cancel] at back
  have millerBack := inside _ back
    ((ContextualDependentNormalizing.normal_rename_iff empty (Fin.cast scope.target_arity) N).mpr normalN)
  exact miller_rename_reflect N (ρ := Fin.cast scope.target_arity) (Fin.cast_injective _)
    (flexible' := openedFlexible (n := Γ.arity + scope.length) scope.length)
    (flexible := ContextualDependentShortClosure.spineMark scope) (fun _ => rfl) millerBack

end Values

/-! ## The pattern's body -/

section Body

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The argument map respects the markings**: outer variables to outer variables, binders to locals. -/
theorem bodyRen_respects {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
    {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} (pattern : Pattern spine scope) :
    ∀ i, ContextualDependentShortClosure.spineMark scope (pattern.bodyRen i) =
      ContextualDependentShortClosure.spineMark spine i := by
  intro i
  rcases spine.variable_cases i with ⟨prior, rfl⟩ | ⟨position, rfl⟩
  · rw [ContextualDependentPatternFiring.bodyRen_outer, ContextualDependentShortClosure.spineMark_outer,
      ContextualDependentShortClosure.spineMark_outer]
  · rw [ContextualDependentPatternFiring.bodyRen_local, ContextualDependentShortClosure.spineMark_local,
      ContextualDependentShortClosure.spineMark_local]

/-- **The pattern answer's value has a normal Miller reduct**, when the right side's normal forms are Miller. -/
theorem abstractBody_reducing (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Γ : Context S.R} {type : TypeOver Γ}
    {spine : Spine type} {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}
    (pattern : Pattern spine scope) (body : Term spine.target spine.result)
    (right : ∀ N, Star (R := S.R) (Presentation.rename pattern.bodyRen body.code) N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    ∃ v, Star (R := S.R) (spine.abstractBody body).code v ∧ Normal S.R v ∧ miller (fun _ => true) v = true := by
  have empty := computation_empty rigid
  obtain ⟨b, toB, normalB⟩ := ContextualDependentOpenedNormal.term_normal sn body
  have imageMiller := right _ (star_rename pattern.bodyRen toB)
    ((ContextualDependentNormalizing.normal_rename_iff empty pattern.bodyRen b).mpr normalB)
  have bodyMiller := miller_rename_reflect b pattern.bodyRen_injective (bodyRen_respects pattern) imageMiller
  refine ⟨lamsVar spine.length (Presentation.rename (Fin.cast spine.target_arity) b), ?_, ?_, ?_⟩
  · rw [ContextualDependentShortClosure.abstractBody_code]
    exact star_lamsVar spine.length (star_rename _ toB)
  · exact normal_lamsVar empty _ _ ((ContextualDependentNormalizing.normal_rename_iff empty _ b).mpr normalB)
  · rw [miller_lamsVar]
    refine miller_rename b (Fin.cast_injective _) (fun i => ?_) bodyMiller
    rw [bodyFlexible_eq]
    rfl

end Body

/-! ## The reading of an equation -/

section Reading

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)

/-- **The scoped reading of an equation with Miller sides has Miller sides**: every normal form of either side of the
reading is Miller, with the outer variables flexible and the locals rigid. -/
theorem viewEquation_sides (rigid : ∀ name, S.roles name = .rigid) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) (sides : FragmentSidesMiller equation)
    {found : (scope : Spine equation.1.1) × (active : Active scope.target) ×'
      ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
        (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution}
    (read : viewEquation facts roots heads algebra declared choices reducer root fuel equation = some found) :
    (∀ N, Star (R := S.R) found.2.1.left.code N → Normal S.R N →
        miller (ContextualDependentShortClosure.spineMark found.1) N = true) ∧
      ∀ N, Star (R := S.R) found.2.1.right.code N → Normal S.R N →
        miller (ContextualDependentShortClosure.spineMark found.1) N = true := by
  have empty := computation_empty rigid
  unfold viewEquation at read
  obtain ⟨typesSame, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨scope, discovered, read⟩ := Option.bind_eq_some_iff.mp read
  cases read
  have length := ContextualDependentPiSpineDiscovery.discovered_length facts roots heads algebra declared choices
    reducer fuel _ _ scope discovered
  have insideLeft : ∀ N, Star (R := S.R) (openCode scope.length equation.1.2.code) N → Normal S.R N →
      miller (openedFlexible scope.length) N = true := by
    rw [length]
    exact sides.1
  have insideRight : ∀ N, Star (R := S.R) (openCode scope.length equation.2.2.code) N → Normal S.R N →
      miller (openedFlexible scope.length) N = true := by
    rw [length]
    exact sides.2
  refine ⟨opened_miller empty scope equation.1.2.code ?_ insideLeft,
    opened_miller empty scope equation.2.2.code ?_ insideRight⟩
  · have steps := (termAt_star root facts roots heads fuel ⟨scope.result, scope.openFunction equation.1.2⟩).2
    rw [ContextualDependentPatternFiring.openFunction_code] at steps
    exact steps
  · have steps := (termAt_star root facts roots heads fuel
      ⟨scope.result, scope.openFunction (equation.2.2.convertType equation.1.1 typesSame.down)⟩).2
    rw [ContextualDependentPatternFiring.openFunction_code] at steps
    exact steps

end Reading

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
