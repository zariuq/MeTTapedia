import Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms

/-!
# Reduction, choice, and the boundary of unique normal forms

Prime's reduction probe separates three notions that a deterministic evaluator
can accidentally conflate:

* a resident term may be inert;
* a process may reduce nondeterministically;
* an observer may collect or resolve the resulting alternatives.

The already validated gluing of quotation and choice supplies the operational
presentation used here.  The module proves that its concrete choice canary
reaches two distinct terms and that both are normal.  Consequently the choice
fragment has no unique normal form for that term.  Deterministic fragments may
still expose ordinary normal forms, but a whole-language normalization
interface must return an occurrence family or accept an explicit resolution
observer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace ReductionChoiceNormalFormBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DialectGluing
open Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms
open Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping

/-! ## Validated choice presentation -/

/-- The glued choice-and-quotation presentation passes the authored language
validation boundary. -/
theorem choice_language_validate : quoteAndChoice.validate = [] :=
  quoteAndChoice_validate

def validatedChoiceLanguage : ValidatedLanguageDef where
  language := quoteAndChoice
  valid := choice_language_validate

/-- Collection remains a separate `Process → Alternatives` boundary in the
validated gluing. -/
theorem validated_collect_crossing :
    ("prime-collect", "Process", "Alternatives") ∈
      unaryCrossings validatedChoiceLanguage.language := by
  decide

def validatedProcessSort : LangSort validatedChoiceLanguage.language :=
  ⟨"Process", by decide⟩

def validatedAlternativesSort : LangSort validatedChoiceLanguage.language :=
  ⟨"Alternatives", by decide⟩

def validatedCollectArrow :
    SortArrow validatedChoiceLanguage.language validatedProcessSort
      validatedAlternativesSort :=
  ⟨"prime-collect", validated_collect_crossing⟩

/-- Reifying alternatives is classified as quoting; it observes the choice
family rather than becoming another reduction branch. -/
theorem validated_collect_is_quoting :
    classifyArrow validatedChoiceLanguage.language "Process"
      validatedCollectArrow = .quoting := by
  decide

/-! ## Concrete normal-form obstruction -/

def leftDemo : Pattern := .apply "prime-left-demo" []
def rightDemo : Pattern := .apply "prime-right-demo" []
def choiceDemo : Pattern :=
  .apply "prime-choose" [leftDemo, rightDemo]

def successors (term : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises noFacts)
    validatedChoiceLanguage.language 1 term

def IsNormal (term : Pattern) : Prop := successors term = []

/-- A one-step normal result retains both reachability and normality rather
than returning a bare structural atom. -/
def IsImmediateNormalResult (source result : Pattern) : Prop :=
  result ∈ successors source ∧ IsNormal result

/-- Normal-result uniqueness is always relative to a declared observer. -/
def ImmediateNormalResultsAgreeAt {View : Type*}
    (observe : Pattern → View) (source : Pattern) : Prop :=
  ∀ first second,
    IsImmediateNormalResult source first →
    IsImmediateNormalResult source second →
    observe first = observe second

theorem choice_successors_exact :
    successors choiceDemo = [leftDemo, rightDemo] := by
  decide +kernel

theorem left_normal : IsNormal leftDemo := by
  unfold IsNormal successors
  decide +kernel

theorem right_normal : IsNormal rightDemo := by
  unfold IsNormal successors
  decide +kernel

theorem left_is_result : IsImmediateNormalResult choiceDemo leftDemo := by
  simp [IsImmediateNormalResult, choice_successors_exact, left_normal]

theorem right_is_result : IsImmediateNormalResult choiceDemo rightDemo := by
  simp [IsImmediateNormalResult, choice_successors_exact, right_normal]

theorem left_ne_right : leftDemo ≠ rightDemo := by
  decide

/-- Native choice refutes a language-wide unique-normal-form reading.  Any
single answer therefore comes from an additional resolution policy, not from
normalization alone. -/
theorem choice_has_no_unique_normal_result :
    ¬ ∃! result, IsImmediateNormalResult choiceDemo result := by
  rintro ⟨result, _isResult, unique⟩
  have leftEq : leftDemo = result := unique leftDemo left_is_result
  have rightEq : rightDemo = result := unique rightDemo right_is_result
  exact left_ne_right (leftEq.trans rightEq.symm)

/-- The identity observer detects the two normal results. -/
theorem choice_not_unique_at_identity :
    ¬ ImmediateNormalResultsAgreeAt id choiceDemo := by
  intro agreement
  exact left_ne_right
    (agreement leftDemo rightDemo left_is_result right_is_result)

/-- A deliberately coarse observer may identify them without erasing the
underlying occurrence family. -/
theorem choice_unique_at_trivial_observer :
    ImmediateNormalResultsAgreeAt (fun _ : Pattern => Unit.unit) choiceDemo := by
  intro first second firstResult secondResult
  rfl

#print axioms choice_language_validate
#print axioms validated_collect_is_quoting
#print axioms choice_successors_exact
#print axioms left_normal
#print axioms right_normal
#print axioms choice_has_no_unique_normal_result
#print axioms choice_not_unique_at_identity
#print axioms choice_unique_at_trivial_observer

end ReductionChoiceNormalFormBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
