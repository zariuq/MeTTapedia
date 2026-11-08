import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersSpineRounds

/-!
# Decomposing rigid formers to the bottom

A decomposition commits only when a following rule decides the decomposed store. Nested formers
defeat a single decomposition: `Π (Π A X) A ≐ Π (Π A A) A` decomposes into `Π A X ≐ Π A A` and a
family twin, and no rule decides that.

**Deep decomposition** decomposes the first decomposable equation of the store again and again, up to
a bound read from the store's codes, before the rules run. Every step keeps exactly the solutions
(`decomposeDeep`). The **deep round** extends the spine round by it; it is eventually constant on
every store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace ContextualDependentEtaExpansion ContextualDependentOccursCheck
open ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- A store with exactly the solutions of a given one. -/
abbrev Rewritten {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :=
  {next : EquationStore (TotalTerm Θ) // (frames S.levels).Equivalent problem next}

theorem equivalent_trans {Θ : Context S.R} {first second third : EquationStore (TotalTerm Θ)}
    (one : (frames S.levels).Equivalent first second) (two : (frames S.levels).Equivalent second third) :
    (frames S.levels).Equivalent first third := fun Δ σ => (one Δ σ).trans (two Δ σ)

theorem equivalent_cons {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {rest next : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent rest next) :
    (frames S.levels).Equivalent (equation :: rest) (equation :: next) := fun Δ σ => by
  rw [models_cons, models_cons, same Δ σ]

/-- The size of a store: the nodes of all its codes. -/
def storeNodes {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Nat :=
  (problem.map fun equation => nodes equation.1.2.code + nodes equation.2.2.code).sum

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
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **Decompose the first equation of the store that decomposes.** -/
def decomposeOnce (fuel : Nat) {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Rewritten problem)
  | [] => none
  | equation :: rest =>
      match formerParts facts roots heads algebra complete declared choices reducer fuel equation with
      | some parts => some ⟨parts.val ++ rest, parts_equivalent parts rest⟩
      | none => (decomposeOnce fuel rest).map fun next => ⟨equation :: next.val, equivalent_cons equation next.property⟩

/-- One step of deep decomposition: stop, or continue from the decomposed store. -/
def deepStep {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (onward : (next : EquationStore (TotalTerm Θ)) → Rewritten next) : Option (Rewritten problem) → Rewritten problem
  | none => ⟨problem, fun _ _ => Iff.rfl⟩
  | some next => ⟨(onward next.val).val, equivalent_trans next.property (onward next.val).property⟩

/-- **Deep decomposition**: decompose again and again, at most `steps` times. -/
def decomposeDeep (fuel : Nat) {Θ : Context S.R} : Nat → (problem : EquationStore (TotalTerm Θ)) → Rewritten problem
  | 0, problem => ⟨problem, fun _ _ => Iff.rfl⟩
  | steps + 1, problem =>
      deepStep problem (decomposeDeep fuel steps)
        (decomposeOnce facts roots heads algebra declared choices reducer complete fuel problem)

/-- **The deep rule on one store equation**: decompose it, decompose the result to the bottom, and run
the rules. -/
def deepEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    Option (Found (equation :: rest)) :=
  (formerParts facts roots heads algebra complete declared choices reducer fuel equation).bind fun parts =>
    afterParts facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      headTypingUnique fuel
      (decomposeDeep facts roots heads algebra declared choices reducer complete fuel (storeNodes (equation :: rest))
        (parts.val ++ rest)).val
      (equivalent_trans (parts_equivalent parts rest)
        (decomposeDeep facts roots heads algebra declared choices reducer complete fuel (storeNodes (equation :: rest))
          (parts.val ++ rest)).property)

/-- Search the store for an equation whose deep decomposition decides. -/
def deepSearch (fuel : Nat) {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match deepEquation facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique fuel equation rest with
      | some found => some found
      | none => (deepSearch fuel rest).map (Found.keepLeft equation)

/-- **One deep round**: the spine round, and when it is stuck, deep decomposition on the prepared store. -/
def deepRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  extendRound root rootComplete facts roots heads
    (fun fuel => spineRound facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => deepSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique fuel) fuel problem

/-- **The deep family.** -/
def deepFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := deepRound facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal headTypingUnique rootComplete fuel

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

theorem decomposeOnce_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      decomposeOnce facts roots heads algebra declared choices reducer complete fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (formerParts_const facts roots heads algebra declared choices reducer complete stable
        equation).spec
      obtain ⟨t₂, later⟩ := (decomposeOnce_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [decomposeOnce]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

theorem decomposeDeep_const {Θ : Context S.R} :
    ∀ (steps : Nat) (problem : EquationStore (TotalTerm Θ)), EventuallyConst fun fuel =>
      decomposeDeep facts roots heads algebra declared choices reducer complete fuel steps problem
  | 0, _ => EventuallyConst.const _
  | steps + 1, problem =>
      EventuallyConst.dep (h := fun fuel =>
          decomposeOnce facts roots heads algebra declared choices reducer complete fuel problem)
        (k := fun fuel once =>
          deepStep problem (decomposeDeep facts roots heads algebra declared choices reducer complete fuel steps) once)
        (decomposeOnce_const facts roots heads algebra declared choices reducer complete stable problem)
        (fun once => by
          cases once with
          | none => exact EventuallyConst.const _
          | some next =>
              exact EventuallyConst.comp
                (fun deeper : Rewritten next.val =>
                  (⟨deeper.val, equivalent_trans next.property deeper.property⟩ : Rewritten problem))
                (decomposeDeep_const steps next.val))

theorem deepEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => deepEquation facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel equation rest := by
  refine EventuallyConst.dep (h := fun fuel => formerParts facts roots heads algebra complete declared choices reducer
      fuel equation)
    (k := fun fuel found => found.bind fun parts => afterParts facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel
      (decomposeDeep facts roots heads algebra declared choices reducer complete fuel (storeNodes (equation :: rest))
        (parts.val ++ rest)).val
      (equivalent_trans (parts_equivalent parts rest)
        (decomposeDeep facts roots heads algebra declared choices reducer complete fuel (storeNodes (equation :: rest))
          (parts.val ++ rest)).property))
    (formerParts_const facts roots heads algebra declared choices reducer complete stable equation) ?_
  intro found
  cases found with
  | none => exact EventuallyConst.const _
  | some parts =>
      exact EventuallyConst.dep
        (h := fun fuel => decomposeDeep facts roots heads algebra declared choices reducer complete fuel
          (storeNodes (equation :: rest)) (parts.val ++ rest))
        (k := fun fuel deep => afterParts facts roots heads algebra declared choices reducer rigid complete root
          normalizes certifyNormal headTypingUnique fuel deep.val (equivalent_trans (parts_equivalent parts rest)
            deep.property))
        (decomposeDeep_const facts roots heads algebra declared choices reducer complete stable _ _)
        (fun deep => afterParts_const facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique stable deep.val _)

theorem deepSearch_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      deepSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (deepEquation_const facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique stable equation rest).spec
      obtain ⟨t₂, later⟩ := (deepSearch_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [deepSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The deep round is eventually constant on every store.** -/
theorem deepRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => deepRound facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  extendRound_const root rootComplete facts roots heads _ _
    (fun problem => spineRound_const facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete stable problem)
    (fun problem => deepSearch_const facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique stable problem) problem

/-- **The deep family settles** on every class of stores on which, at each nonempty store and from
some budget on, its round is not stuck and keeps every residual store in the class. -/
def deepSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        deepRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          deepRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (deepFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => deepRound_const facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentRigidFormers
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
