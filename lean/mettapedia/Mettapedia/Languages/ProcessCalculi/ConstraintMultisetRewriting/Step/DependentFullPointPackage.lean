import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullJoinFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreConservativityControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTowerBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices

/-!
# The executable full solver in the point package

The point package (`ContextualDependentFibre.Controls`: the cumulative tower with one rigid sort
constant `point : U0`) discharges every hypothesis of the fibre join except the ones the full solver
itself reads. This file builds those, so that the actual full solver runs in the package:

* decisions of head equality, cumulativity and universe recognition, read from the tower;
* the declared type of `point` is formed (`declared`);
* the tower's head choices and the fuelled reducer with no root evaluator (`choices`, `reducer`);
* **strong normalization of the package** (`point_sn`): `point` is a rigid constant with the closed
  witness `Ground : U0`, so the tower's strong normalization transfers to the extension
  (`Witnessed.strong_normalization`);
* hence every typed term has a normal form at its type (`point_normalizes`);
* a normality certificate from a stopped reduction step (`certifyNormal`), and uniqueness of head
  typings (`headTypingUnique`).

`full` is R77's full solver over these witnesses. Controls: the certificate accepts the constant
`point` and refuses the redex `(λx. x) point`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.PointPackage

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ContextualDependentFibre ContextualDependentFibre.Controls

/-! ## Decisions read from the tower -/

instance headEqDecidable : DecidableRel setting.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

instance cumulativeDecidable : DecidableRel setting.R.cumulative := fun left right =>
  LevelTower.instDecidableCumulative left right

instance universeDecidable (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

/-! ## Strong normalization of the package -/

/-- **`point` is a rigid constant with a witness**: `Ground : U0` is a closed term of its type. -/
def witnessed : Witnessed Tower.rules where
  name := point
  type := universe0
  witness := .head .legacyGround
  fresh := rfl
  typesAbsent := fun known => by cases known
  stepsStable := fun step => False.elim step
  typeAbsent := rfl
  universeHead := .sort (.succ Tower.zero)
  universeOk := LevelTower.IsUniverse.sort _
  typeTyped := Derivable.headType (LevelTower.HeadTyping.sort Tower.zero)
  inhabited := Derivable.headType LevelTower.HeadTyping.legacyGround

/-- **Strong normalization of the point package.** -/
theorem point_sn {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed setting.R Γ) (typed : Typed setting.R Γ t A) :
    StrongNormalization.SN setting.R t :=
  witnessed.strong_normalization (fun formed typed => TowerInterpretation.tower_sn formed typed) formed typed

/-- **Every typed term of the package has a normal form at its type.** -/
theorem point_normalizes {Θ : Context setting.R} {type : TypeOver Θ} (term : Term Θ type) :
    ∃ code : Tower.Tm Θ.arity, ContextualDependentNormalChecking.Normal (S := setting) code ∧
      Equal setting.R Θ.raw term.code code type.code := by
  obtain ⟨typeFuel, _, _, typeStable⟩ :=
    ContextualDependentReductionBudget.eventually_stable_of_sn setting.R (fun _ => none)
      (point_sn Θ.formed type.formed)
  obtain ⟨termFuel, _, _, termStable⟩ :=
    ContextualDependentReductionBudget.eventually_stable_of_sn setting.R (fun _ => none)
      (point_sn Θ.formed term.typed)
  have success := (ContextualDependentNormalization.reduceTerm_success_iff (S := setting) (fun _ => none)
      facts roots heads (max typeFuel termFuel) (⟨type, term⟩ : TotalTerm Θ)).mpr
    ⟨by rw [typeStable _ (Nat.le_max_left _ _)]; rfl, by rw [termStable _ (Nat.le_max_right _ _)]; rfl⟩
  have normal := ContextualDependentNormalization.termAt_normal_of_success (S := setting) (fun _ => none)
    facts roots heads (fun _ _ _ impossible => False.elim impossible) _ success
  have same := ContextualDependentNormalization.termAt_equivalent (S := setting) (fun _ => none)
    facts roots heads (max typeFuel termFuel) (⟨type, term⟩ : TotalTerm Θ)
  exact ⟨_, normal.2, same.2⟩

/-! ## The executable witnesses -/

/-- A normality certificate: the reduction step stops. -/
def certifyNormal {n : Nat} (term : Tower.Tm n) :
    Option (PLift (ContextualDependentNormalChecking.Normal (S := setting) term)) :=
  if stopped : ExecutableReduction.step setting.R (fun _ => none) term = none then
    some ⟨ContextualDependentReductionBudget.normal_of_stopped setting.R (fun _ => none)
      (fun _ _ _ impossible => False.elim impossible) term stopped⟩
  else none

/-- The declared type of `point` is formed, and nothing else is declared. -/
theorem declared : DeclaredTypesFormed setting.R := by
  intro name type known
  by_cases same : name = point
  · subst same
    have lookup : setting.R.constantType point = some universe0 := by
      simp only [setting, pointRules, Rules.addConstant, beq_self_eq_true, cond_true]
    rw [lookup] at known
    obtain rfl := (Option.some.inj known).symm
    exact ⟨.sort (.succ Tower.zero), LevelTower.IsUniverse.sort _,
      Derivable.headType (LevelTower.HeadTyping.sort Tower.zero)⟩
  · have none : setting.R.constantType name = none := by
      simp only [setting, pointRules, Rules.addConstant, beq_false_of_ne same, cond_false]
      rfl
    rw [none] at known
    cases known

/-- The tower's head choices. -/
def choices : ExecutableChecking.HeadChoices setting.R where
  typing head := some (ExecutableTowerChoices.typing head)
  join := ExecutableTowerChoices.join

/-- The fuelled reducer with no root evaluator. -/
def reducer : ExecutableReduction.Reducer setting.R :=
  ExecutableReduction.normalize setting.R (fun _ => none)

theorem headTypingUnique {head first second : Tower.Head}
    (one : setting.R.headTyping head first) (two : setting.R.headTyping head second) : first = second :=
  ContextualDependentNormalCheckingTower.head_typing_unique (L := Nat) one two

/-- **R77's full solver in the point package**, at checker budget `rounds`. -/
def fullAt (rounds : Nat) : ContextualDependentWorklist.Solver setting.levels :=
  ContextualDependentPatternSolver.fullSolver (S := setting) rigid facts complete roots heads algebra declared
    choices reducer (fun _ => none) point_normalizes certifyNormal headTypingUnique rounds

/-- The full solver at checker budget 16, the budget of R77's controls. -/
abbrev full : ContextualDependentWorklist.Solver setting.levels := fullAt 16

/-! ## Controls of the certificate -/

/-- The constant `point` is certified normal. -/
theorem certify_point : (certifyNormal (.const point : Tower.Tm 0)).isSome = true := by
  decide +kernel

/-- The redex `(λx. x) point` is not certified. -/
theorem certify_redex_refused :
    (certifyNormal (.app (.lam (.var 0)) (.const point) : Tower.Tm 0)).isSome = false := by
  decide +kernel

end DependentFull.PointPackage

#print axioms DependentFull.PointPackage.witnessed
#print axioms DependentFull.PointPackage.point_sn
#print axioms DependentFull.PointPackage.point_normalizes
#print axioms DependentFull.PointPackage.certifyNormal
#print axioms DependentFull.PointPackage.declared
#print axioms DependentFull.PointPackage.headTypingUnique
#print axioms DependentFull.PointPackage.fullAt
#print axioms DependentFull.PointPackage.certify_point
#print axioms DependentFull.PointPackage.certify_redex_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
