import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTypedInversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices

/-!
# Dependency-sensitive inversion controls

The selected subcontext retains `A : U0, x : A` from
`A : U0, junk : U0, x : A`. The executable inverse reconstructs and checks
the variable at its dependent type. Selecting only the value while dropping
its type variable fails type reconstruction. Separate controls exercise a
permutation under a binder and a beta redex whose discarded argument prevents
raw inversion even though its reduct is in scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInversion.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion

def universeType : TypeOver (empty Tower.rules) :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

abbrev typeContext := extend (empty Tower.rules) universeType

def parameterType : TypeOver typeContext := ⟨.var 0, .sort Tower.zero, .sort _, .var 0⟩
abbrev small := extend typeContext parameterType

def extraType : TypeOver typeContext := universeType.reindex (toEmpty typeContext)
abbrev withExtra := extend typeContext extraType

def shiftedParameter : TypeOver withExtra := ⟨.var 1, .sort Tower.zero, .sort _, .var 1⟩
abbrev large := extend withExtra shiftedParameter

def selected : Ren 2 3 := fun index => if index.val = 0 then 0 else 2

theorem selected_injective : Function.Injective selected := by
  intro first second same
  fin_cases first <;> fin_cases second <;> simp_all [selected]

def inclusion : Inclusion small large where
  forward := selected
  injective := selected_injective
  typed := by
    intro index
    fin_cases index
    · exact .var 0
    · exact .var 2

def expected : TypeOver small := ⟨.var 1, .sort Tower.zero, .sort _, .var 1⟩

def target : Term large (expected.reindex inclusion.hom) := ⟨.var 0, .var 0⟩

abbrev setting := TowerModel.setting (fun _ => (0 : Nat))

instance : DecidableRel setting.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right =>
  LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

theorem declarations_formed : DeclaredTypesFormed setting.R := by
  intro name type known
  cases known

def reducer : ExecutableReduction.Reducer setting.R :=
  ExecutableReduction.normalize setting.R (fun _ => none)

def recovered := recover (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra declarations_formed ExecutableTowerChoices.choices reducer 16 inclusion expected target.code

/-- The body is computed and checked in the smaller dependent context. -/
theorem dependent_body_recovered : recovered.map (fun result => result.body.code) = some (.var 0) := by
  decide +kernel

theorem checked_recovery_solves :
    ∃ result : Recovery inclusion expected target.code,
      (ContextualDependentEta.frames setting.levels).E
        (TotalTerm.reindex ⟨expected, result.body⟩ inclusion.hom)
        (⟨expected.reindex inclusion.hom, target⟩ : TotalTerm large) := by
  obtain ⟨result, _, _⟩ := Option.map_eq_some_iff.mp dependent_body_recovered
  exact ⟨result, result.solves (S := setting) target⟩

/-- Keeping x alone recovers its value syntax but cannot recover its
annotation A. A value-only scope test would miss this dependency. -/
def valueOnly : Ren 1 3 := fun _ => 0

theorem value_without_type_dependency :
    invert (Head := Tower.Head) (lookup valueOnly) (.var 0) = some (.var 0) ∧
      invert (Head := Tower.Head) (lookup valueOnly) (.var 2) = none := by
  constructor <;> decide +kernel

theorem missing_type_has_no_raw_preimage :
    ¬ ∃ body : Tower.Tm 1, rename valueOnly body = .var 2 := by
  apply (invert_eq_none_iff valueOnly (lookup valueOnly)
    (lookup_exact valueOnly (fun first second _ => Subsingleton.elim first second)) (.var 2)).mp
  exact value_without_type_dependency.2

def swap : Ren 2 2 := fun index => if index.val = 0 then 1 else 0

theorem inversion_crosses_binder_and_permutation :
    invert (Head := Tower.Head) (lookup swap)
      (.lam (.app (.var 1) (.var 2))) = some (.lam (.app (.var 2) (.var 1))) := by
  decide +kernel

def keepFirst : Ren 1 2 := fun _ => 0
def erasedArgument : Tower.Tm 2 := .app (.lam (.var 1)) (.var 1)

/-- A raw inverse failure is not a conversion-relative refutation. -/
theorem beta_can_remove_the_out_of_scope_occurrence :
    invert (lookup keepFirst) erasedArgument = none ∧
      Conv Tower.rules.headEq erasedArgument (.var 0) Tower.rules.computation ∧
      invert (Head := Tower.Head) (lookup keepFirst) (.var 0) = some (.var 0) := by
  refine ⟨?_, .rel _ _ (.betaPi _ _), ?_⟩ <;> decide +kernel

end ContextualDependentInversion.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
