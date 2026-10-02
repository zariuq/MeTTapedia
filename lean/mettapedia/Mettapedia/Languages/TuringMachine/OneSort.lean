import Mettapedia.Languages.TuringMachine.NotInteractive
import Mettapedia.GSLT.LanguageDef.SortMerging

/-!
# A Turing machine at one sort

The naive presentation of a Turing machine keeps states, symbols, half-tapes,
tapes and configurations apart, and for that reason has no same-sort contact.
Read the same constructors and the same rules at one sort and the obstruction
disappears: `Run` is then a binary constructor on one sort, and every rule is
headed by it.  The one-sort presentation is interactive as soon as the table
has an entry.

It has the same steps as the machine on every pattern.  What it adds is
terms: `Run` may now be applied to any two terms, a state running on a state
among them.

The map of declarations from the machine to its one-sort presentation fixes
every constructor and sends every sort to the one sort.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortMerging
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- Send every sort to the sort of configurations and fix every other name. -/
abbrev oneSort : LanguageDefSymbolMap := mergeSorts "Config"

/-- The constructors of the machine, at one sort. -/
def oneSortTerms : List GrammarRule := terms.map (mapGrammarRule oneSort)

/-- **The one-sort presentation of a machine**: the same constructors and the
same rules, with every sort replaced by one. -/
def oneSortMachine (machine : Machine) : LanguageDef :=
  { name := "TuringMachineOneSort"
    types := ["Config"]
    terms := oneSortTerms
    equations := []
    rewrites := (rewrites machine).map (mapRewriteRule oneSort) }

/-- The one-sort presentation of every machine passes the declaration gate. -/
theorem oneSortMachine_validate_eq_nil (machine : Machine) :
    (oneSortMachine machine).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · show (["Config"] : List String).Nodup
    decide
  · show (oneSortTerms.map (·.label)).Nodup
    decide
  · show (((rewrites machine).map (mapRewriteRule oneSort)).map (·.name)).Nodup
    rw [List.map_map]
    exact rewrites_names_nodup machine
  · show ∀ term ∈ oneSortTerms, term.category ∈ (["Config"] : List String)
    decide
  · show ∀ term ∈ oneSortTerms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ (["Config"] : List String)
    decide
  · show ∀ term ∈ oneSortTerms, term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param))
    decide +kernel
  · intro rewrite membership
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp membership
    exact validateRewrite_mergeSorts (source := turingMachine machine) rfl rfl
      (rewrites_premiseFree machine rule ruleMember) (rewrites_validate machine rule ruleMember)

/-- The validated naive presentation of a machine. -/
def naive (machine : Machine) : ValidatedLanguageDef :=
  ⟨turingMachine machine, turingMachine_validate_eq_nil machine⟩

/-- The validated one-sort presentation of a machine. -/
def oneSorted (machine : Machine) : ValidatedLanguageDef :=
  ⟨oneSortMachine machine, oneSortMachine_validate_eq_nil machine⟩

/-- **The map of declarations from a machine to its one-sort presentation.** -/
def toOneSort (machine : Machine) : StructuralMorphism (naive machine) (oneSorted machine) where
  symbols := oneSort
  mapsTypes := by
    intro declaration membership
    cases membership with
    | head => exact List.Mem.head _
    | tail _ membership =>
    cases membership with
    | head => exact List.Mem.head _
    | tail _ membership =>
    cases membership with
    | head => exact List.Mem.head _
    | tail _ membership =>
    cases membership with
    | head => exact List.Mem.head _
    | tail _ membership =>
    cases membership with
    | head => exact List.Mem.head _
    | tail _ membership => cases membership
  mapsTerms := fun _ membership => List.mem_map_of_mem membership
  mapsEquations := by
    intro equation membership
    cases membership
  mapsRewrites := fun _ membership => List.mem_map_of_mem membership

/-! ## The same steps -/

/-- **The one-sort presentation has exactly the steps of the machine**, on
every pattern. -/
theorem oneSort_step_iff (machine : Machine) {evaluator : BasePremiseEvaluator}
    {pattern next : Pattern} :
    Step evaluator (oneSortMachine machine) pattern next ↔
      Step evaluator (turingMachine machine) pattern next :=
  step_iff_of_mergeSorts (source := turingMachine machine) rfl (rewrites_premiseFree machine)

/-- Neither presentation generates a static equation. -/
theorem turingMachine_equationFree (machine : Machine) :
    (turingMachine machine).isEquationFree = true := by
  show (LanguageDef.isEquationFree
    { name := "TuringMachine", types := ["State", "Symbol", "Cells", "Tape", "Config"],
      terms := terms, equations := [], rewrites := [] }) = true
  decide

theorem oneSortMachine_equationFree (machine : Machine) :
    (oneSortMachine machine).isEquationFree = true := by
  show (LanguageDef.isEquationFree
    { name := "TuringMachineOneSort", types := ["Config"], terms := oneSortTerms,
      equations := [], rewrites := [] }) = true
  decide

/-! ## Interactive, with contact `Run` -/

/-- `Run` at one sort: a binary constructor whose two operands and whose
result are of the one sort. -/
def oneSortRun : GrammarRule := mapGrammarRule oneSort runConstructor

/-- At one sort `Run` is a same-sort contact. -/
theorem oneSortRun_is_same_sort_contact :
    contactRepresentation? (TypeDecl.plain "Config") oneSortRun = some .binary := by
  rfl

/-- **The one-sort presentation of a machine with at least one table entry is
interactive, with contact `Run`.**  The interacting sort is the one sort, the
contact is `Run`, and the interaction rule is any rule of the machine: each
is premise-free and headed by `Run`. -/
theorem oneSortMachine_interactive_with_run (machine : Machine)
    (nonempty : machine.transitions ≠ []) :
    ∃ presentation : InteractivePresentation,
      presentation.presentation.language = oneSortMachine machine ∧
        presentation.BaseInteraction ∧ presentation.contactConstructor.1 = oneSortRun := by
  obtain ⟨entry, rest, table⟩ := List.exists_cons_of_ne_nil nonempty
  have ruleMember : interiorRule 0 entry ∈ rewrites machine := by
    unfold rewrites
    rw [table]
    simp
  obtain ⟨control, tape, left⟩ := rewrites_headed_by_run machine _ ruleMember
  refine ⟨{ presentation := oneSorted machine
            interactingSort := ⟨TypeDecl.plain "Config", List.Mem.head _⟩
            contactConstructor := ⟨oneSortRun, List.mem_map_of_mem (runConstructor_mem machine)⟩
            interactionRewrite :=
              ⟨mapRewriteRule oneSort (interiorRule 0 entry), List.mem_map_of_mem ruleMember⟩
            contactRepresentation := .binary
            representsContact := oneSortRun_is_same_sort_contact
            interactionHeaded := ?_ }, rfl, ?_, rfl⟩
  · show InteractionHeaded .binary oneSortRun (mapRewriteRule oneSort (interiorRule 0 entry)).left
    rw [mapRewriteRule_mergeSorts_left, left]
    rfl
  · exact isBaseRewrite_of_premises_eq_nil
      (mapRewriteRule_premises_eq_nil _ (rewrites_premiseFree machine _ ruleMember))

/-- The one-sort presentation of a machine with at least one table entry is
interactive. -/
theorem oneSortMachine_isInteractive (machine : Machine)
    (nonempty : machine.transitions ≠ []) : IsInteractive (oneSortMachine machine) := by
  obtain ⟨presentation, language, base, -⟩ := oneSortMachine_interactive_with_run machine nonempty
  exact ⟨presentation, language, base⟩

/-- The machine with an empty table has no rule, and its one-sort
presentation has nothing to select as an interaction rule. -/
theorem oneSortMachine_empty_not_interactive :
    ¬ AdmitsInteractivePresentation (oneSortMachine ⟨[]⟩) :=
  not_admitsInteractivePresentation_of_rewrites_eq_nil rfl

end Mettapedia.Languages.TuringMachine
