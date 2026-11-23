import Mettapedia.OSLF.MeTTaIL.RholangReaching
import Mettapedia.GSLT.Contracts.PaperRhoNamed

/-!
# Rholang's core with the freeze view

Meredith and Radestock (2005, §2.6) apply `{u/z}` to `w[@(y[z])]` and leave it unchanged:
the body between quotes is impervious to substitution. In our calculus the binder `z` of
`x(z).w[@(y[z])]` reaches into the quotation, and the freeze view writes the declared
spelling there. With the spelling `@(*ẑ)` of the binder's closed name `ẑ`, the drop of `z`
inside the quotation receives `@(*ẑ)` and becomes `*ẑ`, so COMM leaves the quotation as
the paper writes it.

* `comm_freezes`, `comm_freezeView`, `stored_is_paper`: COMM under the freeze presentation
  gives the paper's process `w[@(y[z])]`, spelling for spelling, through the declared view.
* `apply_differs`: the apply view on the same term runs the payload at the drop of `z`.
* `bare_spelling_differs`: the bare spelling `@ẑ` runs `ẑ`'s code at the same drop.
* `source_sorted`, `stored_sorted`, `plan_sorted`, `compilation_complete`: the presentation
  runs through the general plan.

## Where the spelling lives

The spelling is declared by the presentation (`QuoteView.freeze`), as a ground name. It
cannot come from the binder's display name: the carrier holds the α-canonical
representative, whose binders carry none (`hinted_source_outside_carrier`), so a spelling
read from the hint would not be a function of the α-class. A spelling per binder would
need the binder's name as data of the signature, as in the paper's `x(y).P`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Rholang.Freeze

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Reflection ReflectiveSubstitution ReflectiveContextualQuote
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
open Mettapedia.GSLT.Contracts.PaperRho
open Mettapedia.GSLT.Contracts.PaperRho.PatternBoundary (encodeName encodeProcess)
open Mettapedia.GSLT.Contracts.PaperRho.Named (frozen received bindingAwareBody literalBody)
open Mettapedia.GSLT.Contracts.PaperRho.Named.Controls (zName zClosed dynamicQuote
  bindingAwareBody_dynamicQuote literalBody_dynamicQuote dynamicQuote_paper)
open RuleBinding

/-! ## The presentation -/

/-- `@0`. -/
def zeroName : Pattern := .apply "NQuote" [.apply "PZero" []]

/-- `ẑ = @(@0!(0))`, the closed name of the binder `z`. -/
def zHat : Pattern := .apply "NQuote" [.apply "POutput" [zeroName, .apply "PZero" []]]

theorem zHat_eq : zHat = encodeName zClosed := by
  simp [zHat, zeroName, encodeName, encodeProcess]

/-- `@(*ẑ)`, the frozen spelling of the binder `z`. -/
def spelling : FrozenSpelling :=
  ⟨.apply "NQuote" [.apply "PDrop" [zHat]], by simp [zHat, zeroName, Pattern.freeFvarNames, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]⟩

theorem spelling_eq : spelling.spelling = frozen zClosed := by
  simp [spelling, frozen, zHat_eq, encodeName, encodeProcess]

/-- Rholang's core, with the eliminated binder frozen to `@(*ẑ)` inside quotations. -/
def presentation : ReflectivePresentationDecl :=
  { Rholang.presentation with
    name := "RholangFreeze"
    -- Reaching (freeze @(*ẑ)): quoted occurrences of the binder keep the spelling `ẑ`.
    quoteScope := .reaching (.freeze spelling) }

def profile : ReflectionProfile :=
  { presentations := [presentation],
    rules := [{ reflectiveRule with
      matchingPresentation := presentation.name
      substitutionPresentation := presentation.name }] }

theorem profile_valid : Reflection.validate language profile = [] := by decide +kernel

/-- The freeze view declares no context constructor. -/
theorem contextless : profile.presentations.filterMap (·.quoteScope.contextConstructor?) = [] := rfl

/-! ## The example of §2.6 -/

/-- The body of `x(z).w[@(y[z])]` with `w = y = @0` and the output sugar `x[y] = x!(*y)`,
read by our calculus: `z` inside the quotation is the bound index. -/
def body : Pattern :=
  .apply "POutput" [zeroName, .apply "PDrop" [.apply "NQuote" [.apply "POutput" [zeroName,
    .apply "PDrop" [.bvar 0]]]]]

theorem body_reads : body = encodeProcess (bindingAwareBody zName dynamicQuote) := by
  rw [bindingAwareBody_dynamicQuote]
  rfl

/-- `@0(z).w[@(y[z])] | @0!(0)`. -/
def source : Pattern :=
  .collection .hashBag [.apply "PInput" [zeroName, .lambda none body], .apply "POutput" [zeroName, .apply "PZero" []]]
    none

/-- `w[@(y[z])]`, the paper's process. -/
def stored : Pattern :=
  .apply "POutput" [zeroName, .apply "PDrop" [.apply "NQuote" [.apply "POutput" [zeroName,
    .apply "PDrop" [zHat]]]]]

def bindings : Match.Bindings :=
  [("n", zeroName), ("p", body), ("q", .apply "PZero" []), ("rest", .collection .hashBag [] none)]

/-- **COMM keeps the quotation's spelling.** -/
theorem comm_freezes :
    applyBindingsForRuleUsing profile GeneralRho.comm bindings = .collection .hashBag [stored] none := by
  decide +kernel

/-- COMM goes through the declared freeze view, which writes `@(*ẑ)`. -/
theorem comm_freezeView :
    applyBindingsForRuleUsing profile GeneralRho.comm bindings =
      .collection .hashBag [freezeView presentation 0 zeroName spelling.spelling body] none := by
  decide +kernel

/-- The view's arguments are the paper's: the received payload `@0` and `frozen ẑ`. -/
theorem view_arguments : zeroName = received .zero ∧ spelling.spelling = frozen zClosed :=
  ⟨by simp [zeroName, received, encodeProcess], spelling_eq⟩

/-- **The result is the paper's process**: `w[@(y[z])]{u/z} = w[@(y[z])]`, spelling for
spelling. -/
theorem stored_is_paper :
    stored = encodeProcess (substitute .zero 0 (literalBody zName dynamicQuote)) ∧
      stored = encodeProcess (literalBody zName dynamicQuote) := by
  rw [dynamicQuote_paper, literalBody_dynamicQuote]
  simp [stored, zeroName, zHat_eq, encodeName, encodeProcess]

/-- **Negative control: the apply view.** On the same term, substitution enters the
quotation and the drop of `z` runs the received payload. -/
theorem apply_differs :
    applyBindingsForRuleUsing Rholang.profile GeneralRho.comm bindings =
        .collection .hashBag [.apply "POutput" [zeroName, .apply "PDrop" [.apply "NQuote"
          [.apply "POutput" [zeroName, .apply "PZero" []]]]]] none ∧
      applyBindingsForRuleUsing Rholang.profile GeneralRho.comm bindings ≠ .collection .hashBag [stored] none := by
  decide +kernel

/-- The presentation with the bare spelling `@ẑ`. -/
def bareProfile : ReflectionProfile :=
  { profile with
    presentations := [{ presentation with quoteScope := .reaching (.freeze ⟨zHat,
      by simp [zHat, zeroName, Pattern.freeFvarNames, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]⟩) }] }

/-- **Negative control: the bare spelling.** Receiving `@ẑ` at the drop of `z` runs `ẑ`'s
code `@0!(0)`. -/
theorem bare_spelling_differs :
    applyBindingsForRuleUsing bareProfile GeneralRho.comm bindings =
        .collection .hashBag [.apply "POutput" [zeroName, .apply "PDrop" [.apply "NQuote"
          [.apply "POutput" [zeroName, .apply "POutput" [zeroName, .apply "PZero" []]]]]]] none ∧
      applyBindingsForRuleUsing bareProfile GeneralRho.comm bindings ≠ .collection .hashBag [stored] none := by
  decide +kernel

/-! ## The carrier and the plan -/

theorem source_sorted :
    checkOpenPatternWellSorted profile language FreeTypeContext.empty [] (.base "Proc") source = true := by
  decide +kernel

theorem stored_sorted :
    checkOpenPatternWellSorted profile language FreeTypeContext.empty [] (.base "Proc") stored = true := by
  decide +kernel

/-- The binder's display name never reaches execution: the carrier holds the α-canonical
representative. -/
theorem hinted_source_outside_carrier :
    checkOpenPatternWellSorted profile language FreeTypeContext.empty [] (.base "Proc")
      (.collection .hashBag [.apply "PInput" [zeroName, .lambda (some "z") body],
        .apply "POutput" [zeroName, .apply "PZero" []]] none) = false := by
  decide +kernel

/-- Rho's standard reduction contexts and COMM, under the freeze profile. -/
def permissions : GeneralExecutionAdmission.Permissions :=
  { GeneralRho.Standard.permissions with reflection := profile }

def plan : GeneralExecutionAdmission.Plan := GeneralExecutionAdmission.compile snapshot permissions

/-- The plan keeps the authored snapshot. -/
theorem plan_snapshot : plan.snapshot = snapshot := rfl

theorem selected_rules :
    GeneralExecutionAdmission.selectedRules snapshot permissions = [(GeneralRho.comm, 0)] := rfl

theorem compiled_rules : plan.rules = [GeneralRho.declaration] := by
  unfold plan GeneralExecutionAdmission.compile GeneralExecutionAdmission.rules
  simp only [selected_rules, List.filterMap_cons, rule_plan_compiled, List.filterMap_nil]

theorem compilation_complete : plan.complete = true := by
  have strata : GeneralPremise.checkStepStratification
      (GeneralExecutionAdmission.executionLanguage snapshot permissions) = true := by
    change GeneralPremise.checkStepStratification
      { language with rewrites := plan.rules.map GeneralExecutionAdmission.RulePlan.rule } = true
    rw [compiled_rules]
    rfl
  have ruleChecks : (GeneralExecutionAdmission.selectedRules snapshot permissions).flatMap
      (fun (rule, index) => GeneralExecutionAdmission.ruleObligations snapshot index rule) = [] := by
    rw [selected_rules]
    simp only [List.flatMap_cons, List.flatMap_nil, GeneralExecutionAdmission.ruleObligations,
      show snapshot.language = language from rfl, binding_compiled,
      show GeneralRho.declaration.binding.elaborate GeneralRho.comm = GeneralRho.comm from rfl,
      show GeneralRho.declaration.binding.spec = Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec
        from rfl, premises_admitted,
      GeneralRho.canonical_comm, GeneralRho.canonical_spines, Bool.and_self,
      ↓reduceIte, List.nil_append]
  have equationSelection : GeneralExecutionAdmission.selectedEquations snapshot permissions = [] := rfl
  have freeChecked : GeneralExecutionAdmission.checkFreeContext snapshot = true := rfl
  have providerChecked : GeneralPremise.checkProviderClosed snapshot.language snapshot.free
      snapshot.provider = true := rfl
  have missingRules : GeneralExecutionAdmission.missing permissions.ruleIndices
      snapshot.language.rewrites.length = [] := rfl
  have missingEquations : GeneralExecutionAdmission.missing permissions.equationIndices
      snapshot.language.equations.length = [] := rfl
  have setChecked : GeneralExecutionAdmission.setDecompositionFree snapshot permissions = true := rfl
  apply List.isEmpty_iff.mpr
  change (GeneralExecutionAdmission.compile snapshot permissions).obligations = []
  dsimp only [GeneralExecutionAdmission.compile]
  rw [show snapshot.language.validate = [] from language_valid, freeChecked, providerChecked,
    show Reflection.validate snapshot.language permissions.reflection = [] from profile_valid,
    missingRules, missingEquations, ruleChecks, equationSelection, strata, setChecked]
  rfl

theorem plan_sorted :
    checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language FreeTypeContext.empty []
      (.base "Proc") stored = true := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.Rholang.Freeze
