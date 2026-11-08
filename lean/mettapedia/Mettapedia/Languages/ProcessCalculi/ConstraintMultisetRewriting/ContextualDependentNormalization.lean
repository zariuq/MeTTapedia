import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReductionBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate

/-!
# Safe normalization of independently typed equation stores

Both the value and its annotation are reduced using their existing typing
derivations. Reduction preservation supplies the new typing and comparison
certificate; no raw-checker completeness or backwards subject expansion is
used. An unfinished endpoint is retained. At every fuel the complete store
has exactly the same solutions at every future frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalization

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (root : ExecutableReduction.RootEvaluator S.R)

structure Normalized {Γ : Context S.R} (original : TotalTerm Γ) where
  value : TotalTerm Γ
  annotationPath : Reduces S.R original.1.code value.1.code
  valuePath : Reduces S.R original.2.code value.2.code
  annotationStopped : ExecutableReduction.step S.R root value.1.code = none
  valueStopped : ExecutableReduction.step S.R root value.2.code = none
  equivalent : (frames S.levels).E original value

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

def reduceTerm (fuel : Nat) {Γ : Context S.R} (original : TotalTerm Γ) : Option (Normalized root original) :=
  match annotationRun : ExecutableReduction.normalize S.R root fuel original.1.code with
  | none => none
  | some annotation =>
      match valueRun : ExecutableReduction.normalize S.R root fuel original.2.code with
      | none => none
      | some value => some <| by
          have typePreserved := Reduces.preserve facts roots heads Γ.formed annotation.property original.1.formed
          let resultType : TypeOver Γ :=
            ⟨annotation.val, original.1.level, original.1.universeWitness, typePreserved.1⟩
          have typeSame : TypeEq S.R Γ.raw original.1.code resultType.code :=
            ⟨original.1.level, original.1.universeWitness, typePreserved.2⟩
          have valuePreserved := Reduces.preserve facts roots heads Γ.formed value.property original.2.typed
          let resultValue : Term Γ resultType :=
            ⟨value.val, Typed.convType valuePreserved.1 typeSame⟩
          exact ⟨⟨resultType, resultValue⟩, annotation.property, value.property,
            ContextualDependentReductionBudget.stopped_of_success S.R root annotationRun,
            ContextualDependentReductionBudget.stopped_of_success S.R root valueRun,
            ⟨typeSame, valuePreserved.2⟩⟩

/-- Bounded normalization does not erase an unfinished obligation. -/
def termAt (fuel : Nat) {Γ : Context S.R} (original : TotalTerm Γ) : TotalTerm Γ :=
  match reduceTerm root facts roots heads fuel original with
  | none => original
  | some reduced => reduced.value

theorem termAt_equivalent (fuel : Nat) {Γ : Context S.R} (original : TotalTerm Γ) :
    (frames S.levels).E original (termAt root facts roots heads fuel original) := by
  cases computed : reduceTerm root facts roots heads fuel original with
  | none =>
    unfold termAt
    rw [computed]
    exact ((frames S.levels).equivalence Γ).refl _
  | some reduced =>
    unfold termAt
    rw [computed]
    exact reduced.equivalent

def storeAt (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    EquationStore (TotalTerm Γ) :=
  problem.map fun equation =>
    (termAt root facts roots heads fuel equation.1, termAt root facts roots heads fuel equation.2)

theorem storeAt_length (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    (storeAt root facts roots heads fuel problem).length = problem.length := by simp only [storeAt, List.length_map]

theorem reduceTerm_success_iff (fuel : Nat) {Γ : Context S.R} (original : TotalTerm Γ) :
    (reduceTerm root facts roots heads fuel original).isSome = true ↔
      (ExecutableReduction.normalize S.R root fuel original.1.code).isSome = true ∧
      (ExecutableReduction.normalize S.R root fuel original.2.code).isSome = true := by
  unfold reduceTerm
  split
  · simp_all
  · split <;> simp_all

theorem termAt_normal_of_success
    (complete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
    {fuel : Nat} {Γ : Context S.R} (original : TotalTerm Γ)
    (success : (reduceTerm root facts roots heads fuel original).isSome = true) :
    (∀ target, ¬ StrongNormalization.Reduces S.R (termAt root facts roots heads fuel original).1.code target) ∧
    (∀ target, ¬ StrongNormalization.Reduces S.R (termAt root facts roots heads fuel original).2.code target) := by
  cases computed : reduceTerm root facts roots heads fuel original with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at success
  | some reduced =>
    have same : termAt root facts roots heads fuel original = reduced.value := by
      unfold termAt
      rw [computed]
    rw [same]
    exact ⟨ContextualDependentReductionBudget.normal_of_stopped S.R root complete _ reduced.annotationStopped,
      ContextualDependentReductionBudget.normal_of_stopped S.R root complete _ reduced.valueStopped⟩

theorem storeAt_zero {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    storeAt root facts roots heads 0 problem = problem := by
  change problem.map (fun equation => (equation.1, equation.2)) = problem
  exact List.map_id problem

theorem storeAt_models (fuel : Nat) {Γ Δ : Context S.R} (solution : Δ ⟶ Γ)
    (problem : EquationStore (TotalTerm Γ)) :
    (frames S.levels).Models solution problem ↔
      (frames S.levels).Models solution (storeAt root facts roots heads fuel problem) := by
  constructor
  · intro solved equation member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    have first := (frames S.levels).preserves solution (termAt_equivalent root facts roots heads fuel original.1)
    have second := (frames S.levels).preserves solution (termAt_equivalent root facts roots heads fuel original.2)
    exact ((frames S.levels).equivalence Δ).trans (((frames S.levels).equivalence Δ).symm first)
      (((frames S.levels).equivalence Δ).trans (solved original originalMember) second)
  · intro solved equation member
    have compared := solved _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
    have first := (frames S.levels).preserves solution (termAt_equivalent root facts roots heads fuel equation.1)
    have second := (frames S.levels).preserves solution (termAt_equivalent root facts roots heads fuel equation.2)
    exact ((frames S.levels).equivalence Δ).trans first
      (((frames S.levels).equivalence Δ).trans compared (((frames S.levels).equivalence Δ).symm second))

theorem storeAt_entails (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (observation : (Δ : Context S.R) → (Δ ⟶ Γ) → Prop) :
    (frames S.levels).Entails problem observation ↔
      (frames S.levels).Entails (storeAt root facts roots heads fuel problem) observation :=
  Frames.Equivalent.entails_iff (X := frames S.levels) (a := Γ)
    (fun _ solution => storeAt_models root facts roots heads fuel solution problem) observation

def update (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Update S.levels problem :=
  (Update.pending S.levels (storeAt root facts roots heads fuel problem)).rephrase
    (fun _ solution => storeAt_models root facts roots heads fuel solution problem)

theorem fixed_point_solutions_iff (fuel : Nat) {Γ : Context S.R}
    (problem : EquationStore (TotalTerm Γ)) (point : Context S.R) :
    (∃ solution : point ⟶ Γ, (frames S.levels).Models solution problem) ↔
      ∃ solution : point ⟶ Γ, (frames S.levels).Models solution (storeAt root facts roots heads fuel problem) :=
  exists_congr fun solution => storeAt_models root facts roots heads fuel solution problem

end ContextualDependentNormalization
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
