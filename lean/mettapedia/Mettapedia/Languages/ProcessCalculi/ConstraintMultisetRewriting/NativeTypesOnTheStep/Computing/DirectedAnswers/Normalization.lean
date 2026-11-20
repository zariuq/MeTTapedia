import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Data
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Instances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Erasing

/-!
# Answers of every typed term, and where strong normalization is not needed

* **Under strong normalization of typed terms** (`Eventually.TypedSN`), in a qualified package every term
  typed in a formed context has exactly one answer, of its type (`answer_of_typedSN`).
* **The hypothesis has an instance**: the executable package of the certified-transform program is
  qualified (`executable_qualified`) and its typed terms are strongly normalizing
  (`Eventually.executable_typedSN`), so every typed term of it has exactly one answer
  (`executable_answer`); the universe `U₀` answers itself there (`executable_u0`). For the vectors package
  strong normalization of typed terms is not proved, and for it the statement is conditional.
* **Strong normalization is not necessary for answers at the numbers.** In the qualified package
  `Eventually.Erasing`, whose typed terms are not all strongly normalizing and on whose typed term
  `d zero` the tree's normalizer returns nothing at every budget (`Eventually.Erasing.separation`; the
  failure is that normalizer's fixed traversal, `Eventually.Erasing.argFirst_normalizes`), every closed
  term typed at the numbers has exactly one answer, a numeral (`erasing_num_answer`), by the logical
  relation of the package's normalization model; `d zero` answers `zero` (`erasing_control`). Whether
  every typed term of that package, open or of a function type, has an answer is not decided here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerNumbersModel (num zero succ numRec ctors)
open Definitions (nat)

/-! ## Under strong normalization -/

section Generic

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Under strong normalization of typed terms, every typed term of a qualified package has exactly one
answer, of its type.** -/
theorem answer_of_typedSN (q : Qualified S) (sn : Eventually.TypedSN S.R) {n : Nat} {Γ : Ctx Head n}
    {t A : Tm Head n} (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ t A) :
    ∃ v, DirectedAnswer S.R t v ∧ Typed S.R Γ v A ∧ Equal S.R Γ t v A ∧
      ∀ w, DirectedAnswer S.R t w → w = v := by
  obtain ⟨v, answer⟩ := exists_of_typedSN sn formed typed
  obtain ⟨typedV, equal⟩ := typed_of_qualified q formed typed answer
  exact ⟨v, answer, typedV, equal, fun w other => unique_of_qualified q other answer⟩

end Generic

/-! ## The executable package -/

section Executable

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open CertifiedTransformProgram

/-- **Every typed term of the executable package has exactly one answer, of its type.** -/
theorem executable_answer {n : Nat} {Γ : Ctx Tower.Head n} {t A : Tower.Tm n}
    (formed : CtxFormed ExecutableModel.rules Γ) (typed : Typed ExecutableModel.rules Γ t A) :
    ∃ v, DirectedAnswer ExecutableModel.rules t v ∧ Typed ExecutableModel.rules Γ v A ∧
      Equal ExecutableModel.rules Γ t v A ∧ ∀ w, DirectedAnswer ExecutableModel.rules t w → w = v :=
  answer_of_typedSN executable_qualified Eventually.executable_typedSN formed typed

/-- **An instance**: the universe `U₀`, typed at `U₁` in the empty context, has exactly one answer in the
executable package, itself, a head. -/
theorem executable_u0 :
    Typed ExecutableModel.rules .nil (.head (.sort (.const 0)) : Tower.Tm 0) (.head (.sort (.succ (.const 0)))) ∧
      ∀ v, DirectedAnswer ExecutableModel.rules (.head (.sort (.const 0)) : Tower.Tm 0) v ↔
        v = .head (.sort (.const 0)) := by
  have typed : Typed ExecutableModel.rules .nil (.head (.sort (.const 0)) : Tower.Tm 0)
      (.head (.sort (.succ (.const 0)))) := .headType (LevelTower.HeadTyping.sort _)
  have normal : ContextualDependentExecutableJoin.Normal ExecutableModel.rules
      (.head (.sort (.const 0)) : Tower.Tm 0) := by
    intro target step
    cases step with
    | head impossible => exact impossible
    | root h => exact ExecutableModel.constructors.no_root_of_spineHead h rfl
  obtain ⟨w, -, -, -, unique⟩ := executable_answer .nil typed
  have self : DirectedAnswer ExecutableModel.rules (.head (.sort (.const 0)) : Tower.Tm 0)
      (.head (.sort (.const 0))) := .self normal
  refine ⟨typed, fun v => ⟨fun answer => (unique v answer).trans (unique _ self).symm, ?_⟩⟩
  rintro rfl
  exact self

end Executable

/-! ## Without strong normalization: the numbers of `Erasing` -/

section Erasing

open Eventually.Erasing (rules roles setting qualified bName dName dZero)

/-- Every declared constant of `Erasing` is not rigid. -/
theorem erasing_declared (c : DeclName) (type : Tm Tower.Head 0)
    (declared : rules.constantType c = some type) : roles c ≠ .rigid := by
  intro rigid
  by_cases hbd : c = bName ∨ c = dName
  · rw [show roles c = .computes 1 .leaf by simp [roles, hbd]] at rigid
    cases rigid
  by_cases hnum : c = num
  · subst hnum
    rw [Eventually.Erasing.roles_num] at rigid
    cases rigid
  by_cases hzero : c = zero
  · subst hzero
    rw [Eventually.Erasing.roles_zero] at rigid
    cases rigid
  by_cases hsucc : c = succ
  · subst hsucc
    rw [Eventually.Erasing.roles_succ] at rigid
    cases rigid
  by_cases hrec : c = numRec
  · subst hrec
    rw [Eventually.Erasing.roles_numRec] at rigid
    cases rigid
  have undeclared : rules.constantType c = none := by
    simp [rules, Eventually.Erasing.constantType, hbd, TowerNumbersModel.constantType, hnum, hzero, hsucc,
      hrec]
  rw [undeclared] at declared
  cases declared

/-- The computing constants of `Erasing` inspect at most one argument. -/
theorem erasing_inspects (c : DeclName) (arity : Nat) (inspect : InspectTree)
    (role : roles c = .computes arity inspect) :
    inspect = .leaf ∨ ∃ k, inspect = .split k .constructor fun _ => .leaf := by
  by_cases hbd : c = bName ∨ c = dName
  · rw [show roles c = .computes 1 .leaf by simp [roles, hbd]] at role
    cases role
    exact .inl rfl
  by_cases hrec : c = numRec
  · subst hrec
    rw [Eventually.Erasing.roles_numRec] at role
    cases role
    exact .inr ⟨3, rfl⟩
  by_cases hnum : c = num
  · subst hnum
    rw [Eventually.Erasing.roles_num] at role
    cases role
  by_cases hzero : c = zero
  · subst hzero
    rw [Eventually.Erasing.roles_zero] at role
    cases role
  by_cases hsucc : c = succ
  · subst hsucc
    rw [Eventually.Erasing.roles_succ] at role
    cases role
  have rigid : roles c = .rigid := by
    simp [roles, hbd, TowerNumbersModel.roles, hnum, hzero, hsucc, hrec]
  rw [rigid] at role
  cases role

/-- **No closed neutral term is typed in `Erasing`.** -/
theorem erasing_noNeutral : NoClosedNeutral setting :=
  fun _ A neutral typed => no_closed_neutral erasing_declared erasing_inspects neutral rfl .nil A typed

/-- **Every closed number of `Erasing` has exactly one answer, a numeral**, although typed terms of that
package are not all strongly normalizing. -/
theorem erasing_num_answer {t : Tm Tower.Head 0} (typing : Typed rules .nil t (.const num)) :
    ∃ k, DirectedAnswer rules t (nat k) ∧ ∀ w, DirectedAnswer rules t w ↔ w = nat k := by
  obtain ⟨v, tree, answer, -, unique⟩ := inductive_answer (S := setting) qualified
    (noClosedNeutralAt_of erasing_noNeutral num)
    (show setting.roles num = .inductive ctors from Eventually.Erasing.roles_num) numbers_recursive typing
  obtain ⟨k, rfl⟩ := ctorTree_numeral tree
  exact ⟨k, answer, fun w => ⟨unique w, fun same => same ▸ answer⟩⟩

/-- **Strong normalization is not necessary for answers at the numbers**: in `Erasing` typed terms are not
all strongly normalizing and the tree's normalizer returns nothing on `d zero` at every budget, yet every
closed number has exactly one answer, and that of `d zero` is `zero`. -/
theorem erasing_control :
    ¬ Eventually.TypedSN rules ∧
      (∀ root : ExecutableReduction.RootEvaluator rules, Eventually.RootComplete rules root → ∀ fuel,
        ExecutableReduction.normalize rules root fuel (dZero : Tm Tower.Head 0) = none) ∧
      DirectedAnswer rules (dZero : Tm Tower.Head 0) (.const zero) ∧
      ∀ {t : Tm Tower.Head 0}, Typed rules .nil t (.const num) →
        ∃ k, DirectedAnswer rules t (nat k) ∧ ∀ w, DirectedAnswer rules t w ↔ w = nat k := by
  obtain ⟨-, -, notSN, -, -, -, -, never⟩ := Eventually.Erasing.separation
  have zeroAnswer : DirectedAnswer rules (dZero : Tm Tower.Head 0) (.const zero) :=
    ⟨Eventually.Erasing.dZero_reduces, Eventually.Erasing.zero_normal⟩
  exact ⟨notSN, never, zeroAnswer, fun typing => erasing_num_answer typing⟩

end Erasing

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms answer_of_typedSN
#print axioms executable_answer
#print axioms executable_u0
#print axioms erasing_declared
#print axioms erasing_inspects
#print axioms erasing_noNeutral
#print axioms erasing_num_answer
#print axioms erasing_control
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
