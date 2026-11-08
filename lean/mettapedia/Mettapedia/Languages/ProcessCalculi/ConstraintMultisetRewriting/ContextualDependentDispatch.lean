import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlex

/-!
# Finding a flexible-variable definition in an equation store

Each endpoint retains its own typing. The dispatcher first checks that both
annotations convert to the newest declaration's type, then tries both
orientations of the existing flexible-variable rule. It searches the whole
finite queue, reindexes skipped equations, and scans them again after a
successful update. Every returned update factors all original solutions.

This selects one newest-variable definition. It is not the complete dynamic
pattern worklist, and an unfinished search is never a refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDispatch

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

structure Aligned (levels : LevelModel rules L) {Γ : Context rules}
    (type : TypeOver Γ) (original : Equation (TotalTerm Γ)) where
  left : Term Γ type
  right : Term Γ type
  leftSame : (frames levels).E original.1 (⟨type, left⟩ : TotalTerm Γ)
  rightSame : (frames levels).E original.2 (⟨type, right⟩ : TotalTerm Γ)

variable {levels : LevelModel rules L}

theorem Aligned.models_iff {Γ : Context rules} {type : TypeOver Γ}
    {original : Equation (TotalTerm Γ)} (aligned : Aligned levels type original)
    (rest : EquationStore (TotalTerm Γ)) :
    (frames levels).Equivalent (original :: rest)
      (((⟨type, aligned.left⟩ : TotalTerm Γ), (⟨type, aligned.right⟩ : TotalTerm Γ)) :: rest) := by
  intro Δ solution
  have first := (frames levels).preserves solution aligned.leftSame
  have second := (frames levels).preserves solution aligned.rightSame
  simp only [Frames.Models, List.mem_cons, forall_eq_or_imp]
  apply and_congr_left
  intro _
  constructor
  · intro same
    exact ((frames levels).equivalence Δ).trans (((frames levels).equivalence Δ).symm first)
      (((frames levels).equivalence Δ).trans same second)
  · intro same
    exact ((frames levels).equivalence Δ).trans first
      (((frames levels).equivalence Δ).trans same (((frames levels).equivalence Δ).symm second))

theorem swap_models {Γ : Context rules} (first second : TotalTerm Γ)
    (rest : EquationStore (TotalTerm Γ)) :
    (frames levels).Equivalent ((first, second) :: rest) ((second, first) :: rest) := by
  intro Δ solution
  simp only [Frames.Models, List.mem_cons, forall_eq_or_imp]
  apply and_congr_left
  intro _
  exact ⟨((frames levels).equivalence Δ).symm, ((frames levels).equivalence Δ).symm⟩

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def align (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (original : Equation (TotalTerm Γ)) : Option (Aligned S.levels type original) := do
  let first ← Conversion.compareTypes facts roots heads algebra reducer fuel original.1.1 type
  let second ← Conversion.compareTypes facts roots heads algebra reducer fuel original.2.1 type
  return ⟨original.1.2.convertType type first.down, original.2.2.convertType type second.down,
    ⟨first.down, .refl original.1.2.typed⟩, ⟨second.down, .refl original.2.2.typed⟩⟩

def orient (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (original : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    Option (Update S.levels (original :: rest)) := do
  let aligned ← align facts roots heads algebra reducer fuel (type.reindex (projectionHom Γ type)) original
  match ContextualDependentFlex.solveNewest facts roots heads algebra declared choices reducer fuel
      aligned.left aligned.right rest with
  | some updated => return updated.rephrase (aligned.models_iff rest)
  | none => do
      let updated ← ContextualDependentFlex.solveNewest facts roots heads algebra declared choices reducer fuel
        aligned.right aligned.left rest
      return updated.rephrase (fun Δ solution =>
        (aligned.models_iff rest Δ solution).trans
          (swap_models (levels := S.levels) ⟨_, aligned.left⟩ ⟨_, aligned.right⟩ rest Δ solution))

def search (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    (problem : EquationStore (TotalTerm (extend Γ type))) → Option (Update S.levels problem)
  | [] => none
  | original :: rest =>
      match orient facts roots heads algebra declared choices reducer fuel type original rest with
      | some updated => some updated
      | none => do
          let updated ← search fuel type rest
          return updated.keepLeft [original]

/-- After an assignment, skipped obligations are scanned in the updated
context as well. Failed selection retains the complete original problem. -/
def step (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) : Update S.levels problem :=
  match search facts roots heads algebra declared choices reducer fuel type problem with
  | none => Update.pending S.levels problem
  | some updated => updated.then (conversion facts roots heads algebra reducer fuel updated.remaining)

theorem solveNewest_target {fuel : Nat} {Γ : Context S.R} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (updated : Update S.levels (ContextualDependentFlex.equation left right :: rest))
    (accepted : ContextualDependentFlex.solveNewest facts roots heads algebra declared choices reducer fuel
      left right rest = some updated) : updated.target = Γ := by
  unfold ContextualDependentFlex.solveNewest at accepted
  obtain ⟨first, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨recovered, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  cases Option.some.inj accepted
  rfl

theorem orient_target {fuel : Nat} {Γ : Context S.R} (type : TypeOver Γ)
    (original : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (updated : Update S.levels (original :: rest))
    (accepted : orient facts roots heads algebra declared choices reducer fuel type original rest = some updated) :
    updated.target = Γ := by
  unfold orient at accepted
  obtain ⟨aligned, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i result computed
    cases Option.some.inj accepted
    exact solveNewest_target facts roots heads algebra declared choices reducer
      aligned.left aligned.right rest result computed
  · obtain ⟨result, computed, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    cases Option.some.inj accepted
    exact solveNewest_target facts roots heads algebra declared choices reducer
      aligned.right aligned.left rest result computed

set_option backward.isDefEq.respectTransparency false in
/-- Success is a real declaration elimination, not a residual-only pass
reported as progress. -/
theorem search_target {fuel : Nat} {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (updated : Update S.levels problem)
    (accepted : search facts roots heads algebra declared choices reducer fuel type problem = some updated) :
    updated.target = Γ := by
  induction problem with
  | nil => cases accepted
  | cons original rest ih =>
      simp only [search] at accepted
      split at accepted
      · rename_i result computed
        have target := orient_target facts roots heads algebra declared choices reducer type original rest result computed
        cases Option.some.inj accepted
        exact target
      · obtain ⟨result, computed, accepted⟩ := Option.bind_eq_some_iff.mp accepted
        cases Option.some.inj accepted
        exact ih result computed

set_option backward.isDefEq.respectTransparency false in
theorem search_zero {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    search facts roots heads algebra declared choices reducer 0 type problem = none := by
  induction problem with
  | nil => rfl
  | cons original rest ih =>
      have stopped : orient facts roots heads algebra declared choices reducer 0 type original rest = none := by rfl'
      simp only [search, stopped, ih]
      rfl

theorem step_zero {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    step facts roots heads algebra declared choices reducer 0 type problem = Update.pending S.levels problem := by
  unfold step
  rw [search_zero]

theorem step_of_unfinished {fuel : Nat} {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (unfinished : search facts roots heads algebra declared choices reducer fuel type problem = none) :
    step facts roots heads algebra declared choices reducer fuel type problem = Update.pending S.levels problem := by
  simp only [step, unfinished]

theorem step_principal_of_finished {fuel : Nat} {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (finished : (step facts roots heads algebra declared choices reducer fuel type problem).remaining = []) :
    (frames S.levels).Principal problem
      (step facts roots heads algebra declared choices reducer fuel type problem).answer :=
  (step facts roots heads algebra declared choices reducer fuel type problem).completed finished

end ContextualDependentDispatch
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
