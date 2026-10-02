import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredTermsOnlyControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedEmptyEquationClassComparison
import Mettapedia.OSLF.Syntax.JsonAuthoredComparison

/-!
# The authored JSON data presentation through operational classification

The existing intrinsic JSON signature expands the authored ordered list
parameters into their Values and Fields sorts. Its complete empty equation
and rewrite inventories instantiate the same operational model and
cocontinuous classification as the binding languages. All four original
closed data carriers are recovered in the actual classified program objects.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedJsonClassifiedInstance

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open JsonTermRung (sig Srt Value Field Values Fields termsOnly)
open IntrinsicScopedLocalPolynomial (LocalRule)
open IntrinsicScopedAuthoredTermsOnlyControls (programAtEquiv)

/-- The authored empty rewrite inventory through the unpruned rule adapter. -/
abbrev rules : List (LocalRule sig) :=
  IntrinsicScopedSharedLocalPolynomialComparison.localRules
    ([] : List (IntrinsicScopedConditionalPolynomial.Rule sig termsOnly.metas))

/-- The complete equation inventory of the existing JSON presentation. -/
abbrev equations := termsOnly.eqs

abbrev algebra := IntrinsicScopedAuthoredClassifiedInstance.algebra equations
abbrev categoricalModel := IntrinsicScopedAuthoredClassifiedInstance.model rules equations

/-- Its actual structure-preserving classifying functor. -/
def classified := IntrinsicScopedAuthoredClassifiedInstance.classified rules equations

/-- The genuine cocontinuous interpretation from operational classification. -/
def interpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation rules equations

def restrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso rules equations
def recoveredModelIso :=
  IntrinsicScopedAuthoredClassifiedInstance.recoveredModelIso rules equations

/-- Neither equations nor operational constructors are added to the source. -/
theorem intrinsic_inventory :
    termsOnly.metas = [] ∧ equations = [] ∧ termsOnly.rules = [] ∧ rules = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- All authored constructor labels and result sorts are retained. -/
theorem authored_constructor_coverage :
    JsonAuthoredComparison.authored.terms.map (fun term => (term.label, term.category)) =
      [("JNull", "Value"), ("JBool", "Value"),
       ("JNum", "Value"), ("JStr", "Value"),
       ("JArr", "Value"), ("JObj", "Value"), ("Field", "Field")] :=
  JsonAuthoredComparison.authored_constructor_results

/-- The source record has exactly the empty equation and rewrite inventories used above. -/
theorem authored_inventory_coverage :
    JsonAuthoredComparison.authored.validate = [] ∧
    JsonAuthoredComparison.authored.equations.length = equations.length ∧
    JsonAuthoredComparison.authored.rewrites.length = rules.length :=
  ⟨JsonAuthoredComparison.authored_valid, rfl, rfl⟩

/-- The four intrinsic sorts include both explicit ordered list sorts. -/
theorem sort_coverage (s : Srt) :
    s = .value ∨ s = .field ∨ s = .values ∨ s = .fields := by
  cases s <;> simp

/-- The represented closed program carrier of the actual classified model. -/
abbrev closedPrograms (s : Srt) :=
  (categoricalModel.programModel.sort s).obj
    (Opposite.op (ContextObject.ofList algebra.substitution.toClone []))

/-- Original closed terms survive the genuine empty equation quotient. -/
def closedTermProgramEquiv (s : Srt) : Term sig [] s ≃ closedPrograms s :=
  (IntrinsicScopedEmptyEquationClassComparison.carrierEquiv termsOnly.metas [] s).symm.trans
    (programAtEquiv rules equations [] s).symm

def closedValueProgramEquiv : Value ≃ closedPrograms .value :=
  JsonTermRung.closedValueEquiv.trans (closedTermProgramEquiv .value)

def closedFieldProgramEquiv : Field ≃ closedPrograms .field :=
  JsonTermRung.closedFieldEquiv.trans (closedTermProgramEquiv .field)

def closedValuesProgramEquiv : Values ≃ closedPrograms .values :=
  JsonTermRung.closedValuesEquiv.trans (closedTermProgramEquiv .values)

def closedFieldsProgramEquiv : Fields ≃ closedPrograms .fields :=
  JsonTermRung.closedFieldsEquiv.trans (closedTermProgramEquiv .fields)

/-- Duplicate member occurrences remain distinct in the classified program object. -/
theorem duplicate_members_distinct :
    closedValueProgramEquiv JsonTermRung.twoMembers ≠
      closedValueProgramEquiv JsonTermRung.oneMember := by
  intro same
  apply JsonTermRung.duplicate_members_distinct
  exact (closedTermProgramEquiv .value).injective same

/-- Every actual event section would require a constructor from the empty rule list. -/
theorem no_event (Γ : Ctx sig) (s : Srt)
    (X : IntrinsicScopedConditionalPresheaf.Base algebra)
    (event : (categoricalModel.objects.event Γ s).obj X) : False :=
  IntrinsicScopedAuthoredTermsOnlyControls.no_event algebra Γ s X event

/-- In particular, the concrete authored terms have no rewrite modulo equations. -/
theorem no_closed_reduction {s : Srt} (source target : Term sig [] s) :
    ¬ termsOnly.StepModE source target :=
  JsonTermRung.no_closed_reduction source target

/-- The genuinely extended generic reduction is empty at every authored context. -/
theorem no_extended_reduction {Γ : Ctx sig} {s : Srt} (source target : Term sig Γ s) :
    ¬ IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction
      rules equations source target :=
  IntrinsicScopedAuthoredTermsOnlyControls.no_extended_reduction equations source target

end Mettapedia.OSLF.Binding.IntrinsicScopedJsonClassifiedInstance
