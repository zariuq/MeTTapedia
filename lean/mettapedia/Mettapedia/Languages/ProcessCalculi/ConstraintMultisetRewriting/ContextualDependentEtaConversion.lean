import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.AlgorithmSoundness

/-!
# Executable conversion at the typed eta frame

The existing type-directed converter constructs algorithmic certificates.
Its soundness theorem supplies typed equality after both independently formed
annotations have been compared and the right value has been retyped. The
worklist removes only equations accepted by that actual finite computation.
Every unresolved equation remains in the returned store, at every budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEta.Conversion

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
variable (reducer : ExecutableReduction.Reducer S.R)

/-- Compare annotations without selecting a common universe computationally;
the universe join is needed only inside the soundness proof. -/
def compareTypes (fuel : Nat) {Γ : Context S.R} (first second : TypeOver Γ) :
    Option (PLift (TypeEq S.R Γ.raw first.code second.code)) := do
  let certificate ← ExecutableConversion.types S.R reducer fuel Γ.raw first.code second.code
  return ⟨by
    obtain ⟨level, joined⟩ := S.levels.join_exists first.universeWitness second.universeWitness
    obtain ⟨left, right⟩ := S.levels.join_upper joined
    exact ⟨level, (S.levels.join_level joined).1,
      Algorithm.sound (S := S) facts roots heads algebra certificate.down Γ.formed
        (S.levels.join_level joined).1 (.cumul first.formed left) (.cumul second.formed right)⟩⟩

def compare (fuel : Nat) {Γ : Context S.R} (first second : TotalTerm Γ) :
    Option (PLift ((frames S.levels).E first second)) := do
  let annotations ← compareTypes facts roots heads algebra reducer fuel first.1 second.1
  let certificate ← ExecutableConversion.compare S.R reducer fuel Γ.raw
    first.2.code second.2.code first.1.code
  return ⟨⟨annotations.down,
    Algorithm.sound (S := S) facts roots heads algebra certificate.down Γ.formed first.2.typed
      (Typed.convType second.2.typed annotations.down.symm)⟩⟩

def scan (fuel : Nat) {Γ : Context S.R} : EquationStore (TotalTerm Γ) → EquationStore (TotalTerm Γ)
  | [] => []
  | equation :: rest =>
      match compare facts roots heads algebra reducer fuel equation.1 equation.2 with
      | some _ => scan fuel rest
      | none => equation :: scan fuel rest

/-- The bounded executable pass preserves exactly every future solution.
In particular, a failed certificate search cannot remove a non-pattern. -/
theorem scan_models (fuel : Nat) {Γ Δ : Context S.R} (σ : Δ ⟶ Γ)
    (problem : EquationStore (TotalTerm Γ)) :
    (frames S.levels).Models σ (scan facts roots heads algebra reducer fuel problem) ↔
      (frames S.levels).Models σ problem := by
  induction problem with
  | nil => rfl
  | cons equation rest ih =>
      simp only [scan]
      cases checked : compare facts roots heads algebra reducer fuel equation.1 equation.2 with
      | none =>
          simpa only [Frames.Models, List.mem_cons, forall_eq_or_imp] using
            and_congr_right (fun (_ : (frames S.levels).Solves σ equation) => ih)
      | some certificate =>
          have solved : (frames S.levels).Solves σ equation :=
            (frames S.levels).preserves σ certificate.down
          change (frames S.levels).Models σ (scan facts roots heads algebra reducer fuel rest) ↔
            (frames S.levels).Models σ (equation :: rest)
          simp only [Frames.Models, List.mem_cons, forall_eq_or_imp] at ih ⊢
          exact ⟨fun rest => ⟨solved, ih.mp rest⟩, fun rest => ih.mpr rest.2⟩

theorem scan_solvable_iff (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    (frames S.levels).Solvable (scan facts roots heads algebra reducer fuel problem) ↔
      (frames S.levels).Solvable problem :=
  Frames.Equivalent.solvable_iff (X := frames S.levels)
    (fun _ σ => scan_models facts roots heads algebra reducer fuel σ problem)

theorem scan_entails_iff (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (observation : (Δ : Context S.R) → (Δ ⟶ Γ) → Prop) :
    (frames S.levels).Entails (scan facts roots heads algebra reducer fuel problem) observation ↔
      (frames S.levels).Entails problem observation :=
  Frames.Equivalent.entails_iff (X := frames S.levels)
    (fun _ σ => scan_models facts roots heads algebra reducer fuel σ problem) observation

end ContextualDependentEta.Conversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
