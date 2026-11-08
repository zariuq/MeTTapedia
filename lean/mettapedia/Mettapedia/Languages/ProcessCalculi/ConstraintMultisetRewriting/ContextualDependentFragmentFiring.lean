import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentWorklistFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStore

/-!
# Which equations the rules can read

Every syntactic rule of the dependent solver reads the opened, normalized sides of an equation
first, and fires only on a few shapes:

* the distinct-locals rule needs two variables;
* the pattern and prune rules need a variable applied to variables (`readApplication`);
* decomposition needs a variable applied to one argument (`asLocalApplication`).

A code is **silent** when it has none of these shapes. On a one-equation store whose opened sides
are silent at every budget, the distinct-locals, pattern, prune and decomposition rules never fire.
The prune and exchange rules also need two declarations, and rotation three, so on small contexts
they never fire either. What is left is the worklist round: a rigid clash, the conversion scan and
the dispatcher.

This is the precise reach of the rules: an equation between two rigid former applications (two
identity types, two Π types, two pairs) whose sides differ is read by no rule unless conversion
already identifies them. In particular, rigid–rigid equations headed by the same type former are
neither decomposed nor refuted (`ContextualDependentFragmentFiringControls`).
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
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget ContextualDependentDynamicFragment

/-! ## Silent codes -/

section Silent

variable {Head : Type}

/-- **A silent code**: not a variable applied to variables, and not a variable applied to anything. -/
def Silent {n : Nat} (code : Tm Head n) : Prop :=
  readApplication code = none ∧ ∀ (index : Fin n) (argument : Tm Head n), code ≠ .app (.var index) argument

/-- Silence, decided. -/
def silentB {n : Nat} (code : Tm Head n) : Bool :=
  (readApplication code).isNone && (match code with
    | .app (.var _) _ => false
    | _ => true)

theorem silent_of_silentB {n : Nat} {code : Tm Head n} (decided : silentB code = true) : Silent code := by
  unfold silentB at decided
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at decided
  refine ⟨decided.1, fun index argument same => ?_⟩
  subst same
  simp at decided

/-- A Π code, decided. -/
def isPiB {n : Nat} : Tm Head n → Bool
  | .pi _ _ => true
  | _ => false

theorem exists_pi_of_isPiB {n : Nat} {code : Tm Head n} (decided : isPiB code = true) : ∃ A B, code = .pi A B := by
  cases code <;> simp_all [isPiB]

variable {rules : Rules Head}

theorem asLocal_silent {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    {code : Tm Head scope.target.arity} (silent : Silent code) :
    ContextualDependentRigidDecomposition.asLocal scope code = none := by
  cases code with
  | var index => exact absurd silent.1 (by simp [readApplication])
  | _ => rfl

theorem asLocalApplication_silent {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    {code : Tm Head scope.target.arity} (silent : Silent code) :
    ContextualDependentRigidDecomposition.asLocalApplication scope code = none := by
  cases code with
  | app function argument =>
      cases function with
      | var index => exact absurd rfl (silent.2 index argument)
      | _ => rfl
  | _ => rfl

end Silent

/-! ## The rules on one silent equation -/

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

/-- **An equation with silent opened sides**: at every budget, the scoped reading, when it
exists, has two silent sides. -/
def SilentEquation {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Prop :=
  ∀ fuel reading, viewEquation facts roots heads algebra declared choices reducer root fuel equation = some reading →
    Silent reading.2.1.left.code ∧ Silent reading.2.1.right.code

theorem tryActive_silent (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) (silent : Silent active.left.code) :
    tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel type scope
      active equation view rest = none := by
  unfold tryActive
  rw [silent.1]

theorem tryEquation_silent (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type)))
    (silent : SilentEquation facts roots heads algebra declared choices reducer root equation) :
    tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel type
      equation rest = none := by
  unfold tryEquation
  split
  · rfl
  · rename_i scope active view read
    have sides := silent fuel _ read
    rw [tryActive_silent rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel
      type scope active equation view rest sides.1]
    exact tryActive_silent rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel
      type scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest sides.2

/-- **The pattern rule never fires on a lone silent equation.** -/
theorem patternRule_silent (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (silent : SilentEquation facts roots heads algebra declared choices reducer root equation) :
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
    rw [tryEquation_silent rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel type equation [] silent]
    rfl

/-- **The distinct-locals rule never fires on a lone silent equation.** -/
theorem localsRule_silent (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (silent : SilentEquation facts roots heads algebra declared choices reducer root equation) :
    ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
      root fuel [equation] = none := by
  have single : ContextualDependentRigidDecomposition.localsClash rigid complete facts roots heads algebra declared
      choices reducer root fuel equation [] = none := by
    unfold ContextualDependentRigidDecomposition.localsClash
    split
    · rfl
    · rename_i scope active view read
      have sides := silent fuel _ read
      split
      · rename_i first second leftFound rightFound
        rw [asLocal_silent scope sides.1] at leftFound
        cases leftFound
      · rfl
  simp only [ContextualDependentRigidDecomposition.localsRule, single]
  rfl

/-- **Decomposition never fires on a lone silent equation.** -/
theorem decomposeSearch_silent (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (silent : SilentEquation facts roots heads algebra declared choices reducer root equation) :
    ContextualDependentRigidDecomposition.decomposeSearch rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel [equation] = none := by
  have single : ContextualDependentRigidDecomposition.decomposeEquation rigid facts complete roots heads algebra
      declared choices reducer root normalizes certifyNormal fuel equation [] = none := by
    unfold ContextualDependentRigidDecomposition.decomposeEquation
    split
    · rfl
    · rename_i scope active view read
      have sides := silent fuel _ read
      have none : ContextualDependentRigidDecomposition.decomposeActive facts complete roots heads algebra declared
          choices reducer fuel scope active = none := by
        unfold ContextualDependentRigidDecomposition.decomposeActive
        split
        · rename_i head left head' right leftFound rightFound
          rw [asLocalApplication_silent scope sides.1] at leftFound
          cases leftFound
        · rfl
      rw [none]
  simp only [ContextualDependentRigidDecomposition.decomposeSearch, single]
  rfl

/-- A context with one declaration has no older declaration to read. -/
theorem newestOf_base_none (fuel : Nat) {Θ : Context S.R} (one : Θ.arity = 1) (view : Newest Θ) :
    newestOf facts roots heads algebra declared choices reducer fuel view.base = none := by
  rcases view with ⟨⟨arity, raw, formed⟩, type, same⟩
  have zero : arity = 0 := by
    have counted := congrArg Context.arity same
    change Θ.arity = arity + 1 at counted
    omega
  subst zero
  cases raw
  rfl

/-- **The prune rule needs two declarations.** -/
theorem pruneRule_one (fuel : Nat) {Θ : Context S.R} (one : Θ.arity = 1) (problem : EquationStore (TotalTerm Θ)) :
    ContextualDependentPatternSolver.pruneRule rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal headTypingUnique fuel problem = none := by
  unfold ContextualDependentPatternSolver.pruneRule
  split
  · rfl
  · rename_i outer _
    rw [newestOf_base_none facts roots heads algebra declared choices reducer fuel one outer]

/-- **The exchange rule needs two declarations.** -/
theorem exchangeRule_one (fuel : Nat) {Θ : Context S.R} (one : Θ.arity = 1) (problem : EquationStore (TotalTerm Θ)) :
    ContextualDependentPatternSolver.exchangeRule rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel problem = none := by
  unfold ContextualDependentPatternSolver.exchangeRule
  split
  · rfl
  · rename_i outer _
    rw [newestOf_base_none facts roots heads algebra declared choices reducer fuel one outer]

/-- **Rotation needs three declarations.** -/
theorem rotateRule_short (fuel : Nat) {Θ : Context S.R} (short : Θ.arity ≤ 2) (problem : EquationStore (TotalTerm Θ)) :
    ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel problem = none := by
  unfold ContextualDependentPermutation.rotateRule
  rw [show Θ.arity - 2 = 0 by omega]
  rfl

/-- **The first rule never fires on a lone silent equation over one declaration.** -/
theorem firstRule_silent (fuel : Nat) {Θ : Context S.R} (one : Θ.arity = 1) (equation : Equation (TotalTerm Θ))
    (silent : SilentEquation facts roots heads algebra declared choices reducer root equation) :
    firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel [equation] = none := by
  unfold firstRule
  rw [patternRule_silent rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
    fuel equation silent]
  dsimp only
  rw [pruneRule_one rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
    headTypingUnique fuel one]
  exact exchangeRule_one rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
    fuel one _

end Rules

/-! ## The worklist round -/

section Worklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

omit [DecidableRel S.R.cumulative] in
/-- **The conversion scan cannot empty an unsolvable store**: the identity would solve it. -/
theorem scan_not_shorter_of_unsolvable (fuel : Nat) {Γ : Context S.R} (equation : Equation (TotalTerm Γ))
    (unsolvable : ¬ (frames S.levels).Solvable [equation]) :
    ¬ (Conversion.scan facts roots heads algebra reducer fuel [equation]).length < [equation].length := by
  intro shorter
  have empty : Conversion.scan facts roots heads algebra reducer fuel [equation] = [] :=
    List.eq_nil_of_length_eq_zero (by simp only [List.length_singleton] at shorter; omega)
  apply unsolvable
  refine (Conversion.scan_solvable_iff facts roots heads algebra reducer fuel [equation]).mp ?_
  rw [empty]
  exact ⟨Γ, 𝟙 Γ, fun _ member => absurd member List.not_mem_nil⟩

/-- **The dispatcher never solves the newest declaration from a lone equation whose annotation
can never be aligned with the newest declaration's type.** -/
theorem search_misaligned (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type)))
    (misaligned : ¬ TypeEq S.R (extend Γ type).raw equation.1.1.code (type.reindex (projectionHom Γ type)).code) :
    ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel type [equation] = none := by
  have aligned : ContextualDependentDispatch.align facts roots heads algebra reducer fuel
      (type.reindex (projectionHom Γ type)) equation = none := by
    unfold ContextualDependentDispatch.align
    cases compared : Conversion.compareTypes facts roots heads algebra reducer fuel equation.1.1
        (type.reindex (projectionHom Γ type)) with
    | none => rfl
    | some same => exact absurd same.down misaligned
  have oriented : ContextualDependentDispatch.orient facts roots heads algebra declared choices reducer fuel type
      equation [] = none := by
    unfold ContextualDependentDispatch.orient
    simp only [Option.bind_eq_bind, aligned, Option.bind_none]
  simp only [ContextualDependentDispatch.search, oriented]
  rfl

variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles) in
/-- **The worklist round is stuck on a lone unsolvable equation** without a clash, whose
annotation is a Π type while the newest declaration is typed by a universe head. -/
theorem worklistRound_stuck (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (noClash : ContextualDependentRigid.storeClashes [equation] = false)
    (unsolvable : ¬ (frames S.levels).Solvable [equation])
    (annotationPi : ∃ A B, equation.1.1.code = .pi A B)
    (lastHead : ∃ (arity : Nat) (raw : Ctx Head arity) (h : Head) (formed : CtxFormed S.R (.snoc raw (.head h))),
      Θ = ⟨arity + 1, .snoc raw (.head h), formed⟩) :
    ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel [equation] =
      .stuck := by
  unfold ContextualDependentWorklist.round
  rw [dif_neg (by rw [noClash]; decide),
    dif_neg (scan_not_shorter_of_unsolvable facts roots heads algebra reducer fuel equation unsolvable)]
  split
  · rfl
  · rename_i view found
    obtain ⟨h, headCode⟩ : ∃ h, view.type.code = .head h := by
      obtain ⟨arity, raw, h, formed, rfl⟩ := lastHead
      refine ⟨h, ?_⟩
      simp only [newestOf] at found
      obtain ⟨checked, _, returned⟩ := Option.bind_eq_some_iff.mp found
      cases returned
      exact checked.property
    have none : ContextualDependentWorklist.throughNewest view [equation]
        (dispatchNewest facts roots heads algebra declared choices reducer fuel view.type) = none := by
      rcases view with ⟨base, type, same⟩
      subst same
      show dispatchNewest facts roots heads algebra declared choices reducer fuel type [equation] = none
      have misaligned : ¬ TypeEq S.R (extend base type).raw equation.1.1.code
          (type.reindex (projectionHom base type)).code := by
        apply ContextualDependentRigid.not_typeEq_of_shapeClashes rigid facts complete (extend base type).formed
        obtain ⟨A, B, pi⟩ := annotationPi
        rw [pi]
        change ContextualDependentRigid.shapeClashes S.R (.pi A B) (subst (projectionHom base type).substitution type.code) = true
        rw [headCode]
        simp [ContextualDependentRigid.shapeClashes, ContextualDependentRigid.shape, ContextualDependentRigid.former,
          ContextualDependentRigid.clashes, ContextualDependentRigid.Shape.kind, subst]
      have searched := search_misaligned facts roots heads algebra declared choices reducer fuel type equation misaligned
      have mapped := dispatchNewest_val facts roots heads algebra declared choices reducer fuel type [equation]
      rw [searched, Option.map_none] at mapped
      exact Option.map_eq_none_iff.mp mapped
    rw [none]

end Worklist

/-! ## Reading an equation -/

section Reading

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)

/-- **A spine discovered for one binder opens a function by one application**: every property of
codes at every arity that holds of `f x` holds of the opened function. -/
theorem discover_one_code (fuel : Nat) {Γ : Context S.R} (whole : TypeOver Γ) (scope : Spine whole)
    (found : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel 1 whole =
      some scope)
    (function : Term Γ whole) (P : ∀ {n : Nat}, Tm Head n → Prop)
    (holds : P (Tm.app (Presentation.rename wk function.code) (.var 0))) :
    P (scope.openFunction function).code := by
  obtain ⟨code, level, universeWitness, formed⟩ := whole
  cases code with
  | pi domain codomain =>
      simp only [ContextualDependentPiSpineDiscovery.discover] at found
      obtain ⟨first, _, afterOne⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨second, _, afterTwo⟩ := Option.bind_eq_some_iff.mp afterOne
      obtain ⟨rest, restRun, returned⟩ := Option.bind_eq_some_iff.mp afterTwo
      cases restRun
      cases returned
      exact holds
  | _ => simp [ContextualDependentPiSpineDiscovery.discover] at found

/-- **A spine discovered for two binders opens a function by two applications.** -/
theorem discover_two_code (fuel : Nat) {Γ : Context S.R} (whole : TypeOver Γ) (scope : Spine whole)
    (found : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel 2 whole =
      some scope)
    (function : Term Γ whole) (P : ∀ {n : Nat}, Tm Head n → Prop)
    (holds : P (Tm.app (Presentation.rename wk (Tm.app (Presentation.rename wk function.code) (.var 0))) (.var 0))) :
    P (scope.openFunction function).code := by
  obtain ⟨code, level, universeWitness, formed⟩ := whole
  cases code with
  | pi domain codomain =>
      simp only [ContextualDependentPiSpineDiscovery.discover] at found
      obtain ⟨first, _, afterOne⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨second, _, afterTwo⟩ := Option.bind_eq_some_iff.mp afterOne
      obtain ⟨rest, restRun, returned⟩ := Option.bind_eq_some_iff.mp afterTwo
      cases returned
      exact discover_one_code facts roots heads algebra declared choices reducer fuel second.val rest restRun _ P holds
  | _ => simp [ContextualDependentPiSpineDiscovery.discover] at found

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **Bounded normalization of an endpoint returns its code, or the executable normalizer's
result.** -/
theorem normalizeAt_code (fuel : Nat) {C : Context S.R} {type : TypeOver C} (term : Term C type) :
    (normalizeAt facts roots heads root fuel term).1.code = term.code ∨
      ∃ result, ExecutableReduction.normalize S.R root fuel term.code = some result ∧
        (normalizeAt facts roots heads root fuel term).1.code = result.val := by
  change (ContextualDependentNormalization.termAt root facts roots heads fuel ⟨type, term⟩).2.code = term.code ∨
    ∃ result, ExecutableReduction.normalize S.R root fuel term.code = some result ∧
      (ContextualDependentNormalization.termAt root facts roots heads fuel ⟨type, term⟩).2.code = result.val
  unfold ContextualDependentNormalization.termAt
  cases computed : ContextualDependentNormalization.reduceTerm root facts roots heads fuel ⟨type, term⟩ with
  | none => exact .inl rfl
  | some reduced =>
      right
      unfold ContextualDependentNormalization.reduceTerm at computed
      split at computed
      · cases computed
      · split at computed
        · cases computed
        · rename_i value valueRun
          cases computed
          exact ⟨value, valueRun, rfl⟩

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **A normalized endpoint is silent** when its code is, and so is every result of the executable
normalizer on it. -/
theorem normalizeAt_silent (fuel : Nat) {C : Context S.R} {type : TypeOver C} (term : Term C type)
    (silent : Silent term.code)
    (results : ∀ result, ExecutableReduction.normalize S.R root fuel term.code = some result → Silent result.val) :
    Silent (normalizeAt facts roots heads root fuel term).1.code := by
  rcases normalizeAt_code facts roots heads root fuel term with same | ⟨result, run, same⟩
  · rw [same]; exact silent
  · rw [same]; exact results result run

/-- **The scoped reading of an equation** opens both sides along the discovered spine and
normalizes them. -/
theorem viewEquation_codes (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {reading}
    (read : viewEquation facts roots heads algebra declared choices reducer root fuel equation = some reading) :
    ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
        (lamDepth equation.1.2.code) equation.1.1 = some reading.1 ∧
      reading.2.1.left.code = (normalizeAt facts roots heads root fuel (reading.1.openFunction equation.1.2)).1.code ∧
      ∃ right : Term Θ equation.1.1, right.code = equation.2.2.code ∧
        reading.2.1.right.code = (normalizeAt facts roots heads root fuel (reading.1.openFunction right)).1.code := by
  unfold viewEquation at read
  obtain ⟨typesSame, _, afterTypes⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨scope, discovered, returned⟩ := Option.bind_eq_some_iff.mp afterTypes
  cases returned
  exact ⟨discovered, rfl, _, rfl, rfl⟩

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- One more round of the executable normalizer: stop at a term without a step, otherwise continue
from the step. -/
theorem normalizeTerm_succ (fuel : Nat) {n : Nat} (term : Tm Head n) :
    ExecutableReduction.normalizeTerm S.R root (fuel + 1) term =
      match (ExecutableReduction.step S.R root term).map Subtype.val with
      | none => some term
      | some next => ExecutableReduction.normalizeTerm S.R root fuel next := by
  unfold ExecutableReduction.normalizeTerm
  simp only [ExecutableReduction.normalize]
  cases ExecutableReduction.step S.R root term with
  | none => rfl
  | some next =>
      simp only [Option.map_some]
      cases ExecutableReduction.normalize S.R root fuel next.val <;> rfl

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **Every result of the executable normalizer is the one at a budget where it finishes**, so it
is silent when that one is. -/
theorem normalize_results_silent (bound : Nat) {n : Nat} (code : Tm Head n)
    (finishes : (ExecutableReduction.normalize S.R root bound code).isSome = true)
    (silentResult : ((ExecutableReduction.normalize S.R root bound code).map Subtype.val).all silentB = true) :
    ∀ fuel result, ExecutableReduction.normalize S.R root fuel code = some result → Silent result.val := by
  intro fuel result run
  obtain ⟨found, foundRun⟩ := Option.isSome_iff_exists.mp finishes
  have mono : ∀ {first second : Nat} {value : ExecutableReduction.Result S.R code},
      ExecutableReduction.normalize S.R root first code = some value → first ≤ second →
        ExecutableReduction.normalize S.R root second code = some value := by
    intro first second value computed enough
    induction enough with
    | refl => exact computed
    | step _ ih => exact ContextualDependentReductionBudget.success_succ S.R root ih
  have same : result = found := by
    have atResult := mono run (le_max_left fuel bound)
    rw [mono foundRun (le_max_right fuel bound)] at atResult
    exact (Option.some.inj atResult).symm
  subst same
  rw [foundRun] at silentResult
  exact silent_of_silentB (by simpa using silentResult)

end Reading

/-! ## Stuck rounds are never decided -/

section Undecided

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **A store on which the first round is stuck is never decided**, at any number of rounds. -/
theorem never_decided_of_stuck (solver : Solver levels) {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (nonempty : problem ≠ []) (stuck : solver.round problem = .stuck) :
    ∀ rounds, ¬ (run solver problem rounds).Decided
  | 0 => fun decided => decided
  | rounds + 1 => by
      obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
      intro decided
      have step : advance solver (Update.pending levels (first :: rest)) =
          .done (.stuck (Update.pending levels (first :: rest))) := by
        unfold advance
        split
        · rename_i empty
          cases empty
        · dsimp only [Update.pending]
          rw [stuck]
      unfold run at decided
      rw [drive_succ, step] at decided
      exact decided

end Undecided

/-! ## Unreadable codes: repeated arguments -/

section Unreadable

variable {Head : Type}

/-- **An unreadable code**: every variable spine it is has a repeated argument, and it is not a
variable applied to anything. A silent code is unreadable; so is `F x x`. -/
def Unreadable {n : Nat} (code : Tm Head n) : Prop :=
  (∀ head arguments, readApplication code = some (head, arguments) → ¬ arguments.Nodup) ∧
    ∀ (index : Fin n) (argument : Tm Head n), code ≠ .app (.var index) argument

theorem Silent.unreadable {n : Nat} {code : Tm Head n} (silent : Silent code) : Unreadable code :=
  ⟨fun _ _ read => (by rw [silent.1] at read; cases read), silent.2⟩

/-- Unreadability, decided. -/
def unreadableB {n : Nat} (code : Tm Head n) : Bool :=
  (match readApplication code with
    | some (_, arguments) => !decide arguments.Nodup
    | none => true) &&
  (match code with
    | .app (.var _) _ => false
    | _ => true)

theorem unreadable_of_unreadableB {n : Nat} {code : Tm Head n} (decided : unreadableB code = true) :
    Unreadable code := by
  unfold unreadableB at decided
  simp only [Bool.and_eq_true] at decided
  constructor
  · intro head arguments read distinct
    rw [read] at decided
    simp [distinct] at decided
  · intro index argument same
    subst same
    simp at decided

/-- A list whose image under a partial map has no repetition has none either. -/
theorem mapM_mem {α β : Type} {f : α → Option β} {a : α} {b : β} (found : f a = some b) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → a ∈ l → b ∈ l'
  | [], _, _, member => absurd member List.not_mem_nil
  | x :: rest, l', computed, member => by
      rw [List.mapM_cons] at computed
      obtain ⟨y, yRun, after⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨ys, ysRun, returned⟩ := Option.bind_eq_some_iff.mp after
      cases returned
      rcases List.mem_cons.mp member with same | later
      · subst same
        rw [found] at yRun
        cases yRun
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mapM_mem found ysRun later)

theorem mapM_nodup {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.Nodup → l.Nodup
  | [], _, _, _ => List.nodup_nil
  | x :: rest, l', computed, distinct => by
      rw [List.mapM_cons] at computed
      obtain ⟨y, yRun, after⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨ys, ysRun, returned⟩ := Option.bind_eq_some_iff.mp after
      cases returned
      obtain ⟨fresh, restDistinct⟩ := List.nodup_cons.mp distinct
      refine List.nodup_cons.mpr ⟨fun member => fresh (mapM_mem yRun ysRun member), mapM_nodup ysRun restDistinct⟩

variable {rules : Rules Head} [DecidableEq Head]

/-- **Recognition never reads a spine with a repeated argument.** -/
theorem recognize_unreadable {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType) (active : Active scope.target)
    (unreadable : Unreadable active.left.code) : recognize spine scope active = none := by
  unfold recognize
  split
  · rfl
  · rename_i head arguments read
    split
    · rfl
    · rename_i values locals
      split
      · rfl
      · rename_i args assigned
        rw [dif_neg (fun distinct => unreadable.1 head arguments read (mapM_nodup locals distinct))]

omit [DecidableEq Head] in
theorem asLocal_unreadable {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    {code : Tm Head scope.target.arity} (unreadable : Unreadable code) :
    ContextualDependentRigidDecomposition.asLocal scope code = none := by
  cases code with
  | var index => exact absurd List.nodup_nil (unreadable.1 index [] rfl)
  | _ => rfl

omit [DecidableEq Head] in
theorem asLocalApplication_unreadable {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    {code : Tm Head scope.target.arity} (unreadable : Unreadable code) :
    ContextualDependentRigidDecomposition.asLocalApplication scope code = none := by
  cases code with
  | app function argument =>
      cases function with
      | var index => exact absurd rfl (unreadable.2 index argument)
      | _ => rfl
  | _ => rfl

end Unreadable

section UnreadableRules

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

/-- **An equation with unreadable opened sides** at every budget. -/
def UnreadableEquation {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Prop :=
  ∀ fuel reading, viewEquation facts roots heads algebra declared choices reducer root fuel equation = some reading →
    Unreadable reading.2.1.left.code ∧ Unreadable reading.2.1.right.code

theorem tryActive_unreadable (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) (unreadable : Unreadable active.left.code) :
    tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal fuel type scope
      active equation view rest = none := by
  unfold tryActive
  split
  · rfl
  · split
    · rfl
    · rename_i spine _
      rw [recognize_unreadable spine scope active unreadable]

theorem tryEquation_unreadable (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type)))
    (unreadable : UnreadableEquation facts roots heads algebra declared choices reducer root equation) :
    tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel type
      equation rest = none := by
  unfold tryEquation
  split
  · rfl
  · rename_i scope active view read
    have sides := unreadable fuel _ read
    rw [tryActive_unreadable rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
      fuel type scope active equation view rest sides.1]
    exact tryActive_unreadable rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
      fuel type scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest sides.2

/-- **The pattern rule never fires on a lone unreadable equation.** -/
theorem patternRule_unreadable (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (unreadable : UnreadableEquation facts roots heads algebra declared choices reducer root equation) :
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
    rw [tryEquation_unreadable rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel type equation [] unreadable]
    rfl

/-- **The distinct-locals rule never fires on a lone unreadable equation.** -/
theorem localsRule_unreadable (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (unreadable : UnreadableEquation facts roots heads algebra declared choices reducer root equation) :
    ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices reducer
      root fuel [equation] = none := by
  have single : ContextualDependentRigidDecomposition.localsClash rigid complete facts roots heads algebra declared
      choices reducer root fuel equation [] = none := by
    unfold ContextualDependentRigidDecomposition.localsClash
    split
    · rfl
    · rename_i scope active view read
      have sides := unreadable fuel _ read
      split
      · rename_i first second leftFound rightFound
        rw [asLocal_unreadable scope sides.1] at leftFound
        cases leftFound
      · rfl
  simp only [ContextualDependentRigidDecomposition.localsRule, single]
  rfl

/-- **Decomposition never fires on a lone unreadable equation.** -/
theorem decomposeSearch_unreadable (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (unreadable : UnreadableEquation facts roots heads algebra declared choices reducer root equation) :
    ContextualDependentRigidDecomposition.decomposeSearch rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel [equation] = none := by
  have single : ContextualDependentRigidDecomposition.decomposeEquation rigid facts complete roots heads algebra
      declared choices reducer root normalizes certifyNormal fuel equation [] = none := by
    unfold ContextualDependentRigidDecomposition.decomposeEquation
    split
    · rfl
    · rename_i scope active view read
      have sides := unreadable fuel _ read
      have none : ContextualDependentRigidDecomposition.decomposeActive facts complete roots heads algebra declared
          choices reducer fuel scope active = none := by
        unfold ContextualDependentRigidDecomposition.decomposeActive
        split
        · rename_i head left head' right leftFound rightFound
          rw [asLocalApplication_unreadable scope sides.1] at leftFound
          cases leftFound
        · rfl
      rw [none]
  simp only [ContextualDependentRigidDecomposition.decomposeSearch, single]
  rfl

theorem pruneActive_unreadable (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) {scopeType : TypeOver (extend (extend Γ₀ older) newer)}
    (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) (unreadable : Unreadable active.left.code) :
    pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel older newer scope active equation view rest = none := by
  unfold pruneActive
  split
  · rfl
  · split
    · rfl
    · rename_i spine _
      rw [recognize_unreadable spine scope active unreadable]

/-- **The prune rule never fires on a lone unreadable equation.** -/
theorem pruneRule_unreadable (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (unreadable : UnreadableEquation facts roots heads algebra declared choices reducer root equation) :
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
                  have sides := unreadable fuel _ read
                  rw [pruneActive_unreadable rigid facts complete roots heads algebra declared choices reducer root
                    normalizes certifyNormal headTypingUnique fuel older newer scope active equation view [] sides.1]
                  exact pruneActive_unreadable rigid facts complete roots heads algebra declared choices reducer root
                    normalizes certifyNormal headTypingUnique fuel older newer scope ⟨active.type, active.right,
                      active.left⟩ equation (fun solution => (view solution).trans (toScoped_swap scope active
                      solution).symm) [] sides.2
              simp only [pruneSearch, single]
              rfl

/-- **The exchange rule never fires when the newest declaration mentions the one below it.** -/
theorem exchangeRule_dependent (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (dependent : ∀ (Γ₀ : Context S.R) (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)),
      Θ = extend (extend Γ₀ older) newer →
        ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code =
          none) :
    ContextualDependentPatternSolver.exchangeRule rigid facts complete roots heads algebra declared choices reducer root
      normalizes certifyNormal fuel problem = none := by
  unfold ContextualDependentPatternSolver.exchangeRule
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
              have inverted := dependent base₀ older newer rfl
              show ContextualDependentPatternSolver.exchangeAt rigid facts complete roots heads algebra declared choices
                reducer root normalizes certifyNormal fuel older newer problem = none
              unfold ContextualDependentPatternSolver.exchangeAt
              cases problem with
              | nil => rfl
              | cons equation rest => simp only [inverted]

/-- **The worklist round is stuck on a lone unsolvable equation** without a clash, when the
dispatcher's search never solves the newest declaration from it. -/
theorem worklistRound_stuck_of_search (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (noClash : ContextualDependentRigid.storeClashes [equation] = false)
    (unsolvable : ¬ (frames S.levels).Solvable [equation])
    (noSearch : ∀ view : Newest Θ, ∀ moved : Equation (TotalTerm (extend view.base view.type)), HEq moved equation →
      ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel view.type [moved] =
        none) :
    ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel [equation] =
      .stuck := by
  unfold ContextualDependentWorklist.round
  rw [dif_neg (by rw [noClash]; decide),
    dif_neg (scan_not_shorter_of_unsolvable facts roots heads algebra reducer fuel equation unsolvable)]
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

/-- **The dispatcher never solves the newest declaration from a lone equation neither of whose
sides equals the newest variable.** -/
theorem search_of_not_newest (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type)))
    (left : ¬ Equal S.R (extend Γ type).raw equation.1.2.code (Elimination.last Γ type).2.code
      (type.reindex (projectionHom Γ type)).code)
    (right : ¬ Equal S.R (extend Γ type).raw equation.2.2.code (Elimination.last Γ type).2.code
      (type.reindex (projectionHom Γ type)).code) :
    ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel type [equation] = none := by
  have oriented : ContextualDependentDispatch.orient facts roots heads algebra declared choices reducer fuel type
      equation [] = none := by
    unfold ContextualDependentDispatch.orient
    cases aligned : ContextualDependentDispatch.align facts roots heads algebra reducer fuel
        (type.reindex (projectionHom Γ type)) equation with
    | none => rfl
    | some alignment =>
        have codes : alignment.left.code = equation.1.2.code ∧ alignment.right.code = equation.2.2.code := by
          unfold ContextualDependentDispatch.align at aligned
          obtain ⟨first, _, afterFirst⟩ := Option.bind_eq_some_iff.mp aligned
          obtain ⟨second, _, returned⟩ := Option.bind_eq_some_iff.mp afterFirst
          cases returned
          exact ⟨rfl, rfl⟩
        have forward : ContextualDependentFlex.solveNewest facts roots heads algebra declared choices reducer fuel
            alignment.left alignment.right [] = none := by
          unfold ContextualDependentFlex.solveNewest
          cases compared : Conversion.compare facts roots heads algebra reducer fuel (⟨_, alignment.left⟩ : TotalTerm _)
              (Elimination.last Γ type) with
          | none => rfl
          | some same =>
            have equal := same.down.2
            change Equal S.R (extend Γ type).raw alignment.left.code (Elimination.last Γ type).2.code
              (type.reindex (projectionHom Γ type)).code at equal
            rw [codes.1] at equal
            exact absurd equal left
        have backward : ContextualDependentFlex.solveNewest facts roots heads algebra declared choices reducer fuel
            alignment.right alignment.left [] = none := by
          unfold ContextualDependentFlex.solveNewest
          cases compared : Conversion.compare facts roots heads algebra reducer fuel
              (⟨_, alignment.right⟩ : TotalTerm _) (Elimination.last Γ type) with
          | none => rfl
          | some same =>
            have equal := same.down.2
            change Equal S.R (extend Γ type).raw alignment.right.code (Elimination.last Γ type).2.code
              (type.reindex (projectionHom Γ type)).code at equal
            rw [codes.2] at equal
            exact absurd equal right
        simp only [Option.bind_eq_bind, Option.bind_some, forward, backward, Option.bind_none]
  simp only [ContextualDependentDispatch.search, oriented]
  rfl

end UnreadableRules

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
