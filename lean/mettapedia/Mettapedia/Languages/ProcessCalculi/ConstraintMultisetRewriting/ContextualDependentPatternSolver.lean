import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternDispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRecognition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineDiscovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneIntersection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverOccurs

/-!
# The pattern solver as a worklist solver

A store equation `λ x̄. l ≐ λ x̄. r` is read under its own local telescope: the telescope is
discovered from the left annotation, both sides are opened at fresh rigid arguments and
normalized by the actual bounded normalizer, and the resulting scoped equation has exactly the
store equation's solutions at every future context (`viewEquation`). On that scoped equation the
general pattern step of `ContextualDependentGeneralPatternDispatch` runs for the newest
metavariable, in both orientations; when it is pending, the occurs check of
`ContextualDependentPatternSolverOccurs` may refute the equation. A principal answer becomes an update of the whole store;
the other equations are instantiated, never dropped. A certified refutation of the scoped
equation refutes the store.

One round of the composed solver tries this pattern rule first and otherwise runs the round of
`ContextualDependentWorklistSolver` (rigid clash, typed eta conversion, newest-variable
dispatch with twin wake-up). The rank is the number of declarations, then the number of
equations; a pattern answer removes the newest declaration. Every round is therefore sound and
loses no solution, and every refutation is a rigid clash, an out-of-image local, or an occurs
check, each certified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternSolver

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Reading a store equation under its local telescope -/

/-- The number of leading abstractions of a code. -/
def lamDepth {n : Nat} : Tm Head n → Nat
  | .lam body => lamDepth body + 1
  | _ => 0

/-- Typed-equal endpoints give a scoped equation the same solutions. -/
theorem toScoped_congr {Θ : Context S.R} {scopeType : TypeOver Θ} (scope : Spine scopeType)
    (type : TypeOver scope.target) (left left' right right' : Term scope.target type)
    (sameLeft : Equal S.R scope.target.raw left.code left'.code type.code)
    (sameRight : Equal S.R scope.target.raw right.code right'.code type.code)
    {Δ : Context S.R} (solution : Δ ⟶ Θ) :
    (scope.toScoped ⟨type, left, right⟩).Holds solution ↔ (scope.toScoped ⟨type, left', right'⟩).Holds solution := by
  rw [Spine.toScoped_holds_iff, Spine.toScoped_holds_iff]
  have onLeft := sameLeft.substitute (scope.map solution).typed
  have onRight := sameRight.substitute (scope.map solution).typed
  constructor
  · intro held
    exact onLeft.symm.trans (held.trans onRight)
  · intro held
    exact onLeft.trans (held.trans onRight.symm)

theorem toScoped_swap {Θ : Context S.R} {scopeType : TypeOver Θ} (scope : Spine scopeType)
    (active : Active scope.target) {Δ : Context S.R} (solution : Δ ⟶ Θ) :
    (scope.toScoped ⟨active.type, active.right, active.left⟩).Holds solution ↔
      (scope.toScoped active).Holds solution := by
  rw [Spine.toScoped_holds_iff, Spine.toScoped_holds_iff]
  exact ⟨fun held => held.symm, fun held => held.symm⟩

/-- **A store equation with a scoped reading** that has exactly its solutions. -/
structure View {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  constraint : Scoped Θ
  holds_iff : ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
    (frames S.levels).Models solution [equation] ↔ constraint.Holds solution

/-- A scoped solver result for the reading becomes an update of the whole store; the other
equations are instantiated by the answer. -/
def View.combine {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (view : View equation)
    (rest : EquationStore (TotalTerm Θ))
    (result : ContextualDependentScopedDispatch.Result S.levels [view.constraint]) :
    Update S.levels (equation :: rest) :=
  (result.update.keepLeft rest).rephrase fun Δ solution => by
    constructor
    · intro solved
      apply (Frames.models_append (X := frames S.levels) solution rest result.closed.equations).mpr
      refine ⟨fun other member => solved other (List.mem_cons_of_mem _ member), (result.closed.models solution).mpr ?_⟩
      intro constraint member
      obtain rfl := List.mem_singleton.mp member
      exact (view.holds_iff solution).mp fun other member => by
        obtain rfl := List.mem_singleton.mp member
        exact solved _ List.mem_cons_self
    · intro solved
      obtain ⟨restSolved, closedSolved⟩ :=
        (Frames.models_append (X := frames S.levels) solution rest result.closed.equations).mp solved
      have one := (view.holds_iff solution).mpr
        ((result.closed.models solution).mp closedSolved _ (List.mem_singleton_self _))
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact one _ (List.mem_singleton_self _)
      · exact restSolved other member

theorem View.combine_target {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (view : View equation)
    (rest : EquationStore (TotalTerm Θ))
    (result : ContextualDependentScopedDispatch.Result S.levels [view.constraint]) :
    (view.combine rest result).target = result.update.target := rfl

/-- A reading without solutions refutes every store containing the equation. -/
theorem View.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (view : View equation)
    (absent : ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ), ¬ view.constraint.Holds solution)
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (equation :: rest) := by
  rintro ⟨Δ, solution, solved⟩
  exact absent solution ((view.holds_iff solution).mp fun other member => by
    obtain rfl := List.mem_singleton.mp member
    exact solved _ List.mem_cons_self)

/-- **The outcome of the pattern rule** on a store: a principal answer for one equation that
removes a declaration, or a refutation. -/
inductive Found {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Type
  | solved (update : Update S.levels problem) (smaller : update.target.arity < Θ.arity)
  | refuted (absent : ¬ (frames S.levels).Solvable problem)

def Found.keepLeft {Θ : Context S.R} {rest : EquationStore (TotalTerm Θ)} (equation : Equation (TotalTerm Θ)) :
    Found rest → Found (equation :: rest)
  | .solved update smaller => .solved (update.keepLeft [equation]) smaller
  | .refuted absent => .refuted fun ⟨Δ, solution, modeled⟩ =>
      absent ⟨Δ, solution, fun other member => modeled other (List.mem_cons_of_mem _ member)⟩

/-- Run a computation at the newest declaration of a context. -/
def throughNewest {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : (stored : EquationStore (TotalTerm (extend view.base view.type))) → Option (Found stored)) :
    Option (Found problem) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact solve problem

theorem throughNewest_nil {Θ : Context S.R} (view : Newest Θ)
    (solve : (stored : EquationStore (TotalTerm (extend view.base view.type))) → Option (Found stored))
    (nothing : solve [] = none) : throughNewest view [] solve = none := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact nothing

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

/-- Bounded normalization of an endpoint at its own annotation. An unfinished run returns the
endpoint itself. -/
def normalizeAt (fuel : Nat) {C : Context S.R} {type : TypeOver C} (term : Term C type) :
    {normal : Term C type // Equal S.R C.raw term.code normal.code type.code} :=
  let reduced := ContextualDependentNormalization.termAt root facts roots heads fuel ⟨type, term⟩
  have same := ContextualDependentNormalization.termAt_equivalent root facts roots heads fuel ⟨type, term⟩
  ⟨reduced.2.convertType type same.1.symm, same.2⟩

/-- **The scoped reading of a store equation**, computed from its left annotation. -/
def viewEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option ((scope : Spine equation.1.1) × (active : Active scope.target) ×'
      ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
        (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution) := do
  let typesSame ← Conversion.compareTypes facts roots heads algebra reducer fuel equation.2.1 equation.1.1
  let right := equation.2.2.convertType equation.1.1 typesSame.down
  let scope ← ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
    (lamDepth equation.1.2.code) equation.1.1
  let left' := normalizeAt facts roots heads root fuel (scope.openFunction equation.1.2)
  let right' := normalizeAt facts roots heads root fuel (scope.openFunction right)
  return ⟨scope, ⟨scope.result, left'.1, right'.1⟩, fun solution => by
    let aligned : ContextualDependentDispatch.Aligned S.levels equation.1.1 equation :=
      ⟨equation.1.2, right, ((frames S.levels).equivalence _).refl _,
        ⟨typesSame.down, .refl equation.2.2.typed⟩⟩
    have first := aligned.models_iff [] _ solution
    exact first.trans ((Spine.opened_models_iff S.levels scope equation.1.2 right solution).trans
      (toScoped_congr scope scope.result _ _ _ _ left'.2 right'.2 solution))⟩

/-! ## The pattern rule -/

/-- The general pattern step on one scoped equation, for the newest metavariable. -/
def tryActive (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) : Option (Found (equation :: rest)) :=
  match readApplication active.left.code with
  | none => none
  | some (_, arguments) =>
      match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
          arguments.length type with
      | none => none
      | some spine =>
          match recognize spine scope active with
          | none => none
          | some recognized =>
              let reading : View equation := ⟨scope.toScoped active, view⟩
              match Pattern.step facts roots heads algebra declared
                  (ContextualDependentScopeConsequence.root_reflection rigid) complete rigid normalizes certifyNormal
                  choices reducer fuel recognized.pattern recognized.right with
              | .solved result _ =>
                  let moved : ContextualDependentScopedDispatch.Result S.levels [reading.constraint] :=
                    result.rephrase fun solution => by
                      simp only [ContextualDependentScopedDispatch.Holds, List.mem_singleton, forall_eq]
                      exact recognized.holds_iff solution
                  if smaller : (reading.combine rest moved).target.arity < (extend Γ type).arity then
                    some (.solved (reading.combine rest moved) smaller)
                  else none
              | .refuted absent =>
                  some (.refuted (reading.refutes (fun solution held =>
                    absent solution ((recognized.holds_iff solution).mp held)) rest))
              | .pending =>
                  match occursCheck rigid complete normalizes recognized.pattern recognized.right with
                  | some absent =>
                      some (.refuted (reading.refutes (fun solution held =>
                        absent.down solution ((recognized.holds_iff solution).mp held)) rest))
                  | none => none

/-- The pattern rule on one store equation, in both orientations. -/
def tryEquation (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type))) :
    Option (Found (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
          fuel type scope active equation view rest with
      | some found => some found
      | none =>
          tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
            fuel type scope ⟨active.type, active.right, active.left⟩ equation
            (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest

/-- Search the store for an equation on which the pattern rule decides. -/
def searchStore (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    (problem : EquationStore (TotalTerm (extend Γ type))) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
          certifyNormal fuel type equation rest with
      | some found => some found
      | none => (searchStore fuel type rest).map (Found.keepLeft equation)

/-- **The pattern rule** at the newest declaration of the context. -/
def patternRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some view => throughNewest view problem
      (searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        fuel view.type)

theorem patternRule_nil (fuel : Nat) {Θ : Context S.R} :
    patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel ([] : EquationStore (TotalTerm Θ)) = none := by
  unfold patternRule
  cases newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => rfl
  | some view =>
      exact throughNewest_nil view _ rfl

/-! ## The composed solver -/

/-- **One round of the composed solver**: the pattern rule, then the qualified worklist round
(clash, conversion, newest-variable dispatch with wake-up). -/
def round (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  match patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel problem with
  | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
  | some (.refuted absent) => .refuted absent
  | none => ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel problem

/-- **The composed solver** for the worklist driver. -/
def solver (fuel : Nat) : Solver S.levels where
  rank := size
  round := round rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel

theorem round_nil (fuel : Nat) {Θ : Context S.R} :
    round rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
      ([] : EquationStore (TotalTerm Θ)) = .stuck := by
  unfold round
  rw [patternRule_nil]
  exact ContextualDependentWorklist.round_nil rigid facts complete roots heads algebra declared choices reducer fuel

/-- **Refutations are certified**: a refuting round found a rigid clash, or the pattern rule
refuted one equation of the store. -/
theorem round_refuted_grounds (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : round rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel problem = .refuted absent) :
    ContextualDependentRigid.storeClashes problem = true ∨
      ∃ absent', patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal fuel problem = some (.refuted absent') := by
  unfold round at refuted
  cases found : patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem with
  | some result =>
      cases result with
      | solved update smaller => simp only [found] at refuted; cases refuted
      | refuted absent' => exact .inr ⟨absent', rfl⟩
  | none =>
    simp only [found] at refuted
    exact .inl (ContextualDependentWorklist.round_refuted_clashes rigid facts complete roots heads algebra declared
      choices reducer fuel refuted)

/-- **The stores the composed solver decides form a fragment.** -/
def decidedFragment (fuel : Nat) :
    Fragment (solver rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel) :=
  Reaches.fragment _ (round_nil rigid facts complete roots heads algebra declared choices reducer root normalizes
    certifyNormal fuel)

end ContextualDependentPatternSolver
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
