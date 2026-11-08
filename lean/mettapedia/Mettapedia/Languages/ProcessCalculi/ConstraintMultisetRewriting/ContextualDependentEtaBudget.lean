import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConversionBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversion

/-!
# Increasing budgets of the typed eta scanner

The solver's annotation and value comparisons inherit full-result fuel
stability from executable conversion. Larger budgets can remove additional
certified equations; they cannot reintroduce an equation already discharged.
The residual remains an ordered sublist, including repeated equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaBudget

open Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
variable (reducer : ExecutableReduction.Reducer S.R)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem compareTypes_mono {Γ : Context S.R} {fuel larger : Nat} {first second : TypeOver Γ}
    {result : PLift (TypeEq S.R Γ.raw first.code second.code)}
    (accepted : Conversion.compareTypes facts roots heads algebra reducer fuel first second = some result)
    (enough : fuel ≤ larger) :
    Conversion.compareTypes facts roots heads algebra reducer larger first second = some result := by
  unfold Conversion.compareTypes at accepted ⊢
  obtain ⟨certificate, compared, returned⟩ := Option.bind_eq_some_iff.mp accepted
  exact Option.bind_eq_some_iff.mpr ⟨certificate,
    types_success_mono S.R reducer stable compared enough, returned⟩

include stable in
theorem compare_mono {Γ : Context S.R} {fuel larger : Nat} {first second : TotalTerm Γ}
    {result : PLift ((frames S.levels).E first second)}
    (accepted : Conversion.compare facts roots heads algebra reducer fuel first second = some result)
    (enough : fuel ≤ larger) :
    Conversion.compare facts roots heads algebra reducer larger first second = some result := by
  unfold Conversion.compare at accepted ⊢
  obtain ⟨annotations, comparedTypes, afterTypes⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨certificate, comparedTerms, returned⟩ := Option.bind_eq_some_iff.mp afterTypes
  exact Option.bind_eq_some_iff.mpr ⟨annotations,
    compareTypes_mono facts roots heads algebra reducer stable comparedTypes enough,
    Option.bind_eq_some_iff.mpr ⟨certificate,
      compare_success_mono S.R reducer stable comparedTerms enough, returned⟩⟩

include stable in
theorem scan_sublist {Γ : Context S.R} {fuel larger : Nat} (enough : fuel ≤ larger)
    (problem : EquationStore (TotalTerm Γ)) :
    (Conversion.scan facts roots heads algebra reducer larger problem).Sublist
      (Conversion.scan facts roots heads algebra reducer fuel problem) := by
  induction problem with
  | nil => exact .slnil
  | cons equation rest ih =>
    cases earlier : Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2 with
    | none =>
      cases later : Conversion.compare facts roots heads algebra reducer larger equation.1 equation.2 with
      | none => simpa only [Conversion.scan, earlier, later] using List.Sublist.cons_cons equation ih
      | some result => simpa only [Conversion.scan, earlier, later] using List.Sublist.cons equation ih
    | some result =>
      have later := compare_mono facts roots heads algebra reducer stable earlier enough
      simpa only [Conversion.scan, earlier, later] using ih

include stable in
theorem scan_finished_mono {Γ : Context S.R} {fuel larger : Nat} (enough : fuel ≤ larger)
    (problem : EquationStore (TotalTerm Γ))
    (finished : Conversion.scan facts roots heads algebra reducer fuel problem = []) :
    Conversion.scan facts roots heads algebra reducer larger problem = [] := by
  have sub := scan_sublist facts roots heads algebra reducer stable enough problem
  rw [finished] at sub
  exact List.sublist_nil.mp sub

end ContextualDependentEtaBudget
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
