import Mettapedia.Languages.PartrecMachine.LanguageDef
import Mettapedia.OSLF.MeTTaIL.PlainRuleValidation
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker

/-!
# The partial-recursive machine as a static equivalence

The authored partial-recursive machine reduces.  This module turns its
reduction into equations, and places them in an interactive theory.

A new sort of histories is added to the machine's signature.  A history is a
configuration being run (`Now`), a configuration followed by a history
(`Then`), a configuration known to finish (`Flag`), two histories in contact
(`Meet`), or a history under one of two prefixes (`Wait`, `Give`).  The
machine's rules are not rewrites of the new language.  Each rule `l ⟶ r`
contributes two equations,

* `Now(l) = Then(l, Now(r))`, which records one step of a run, and
* `Then(l, Flag(r)) = Flag(l)`, which carries a finished run back one step,

and one further equation, `Now(Halt(w)) = Flag(Halt(w))`, says that a halted
configuration is finished.  Every equation has the same variables on both
sides, so the language passes the ordered binding-flow gate even though the
machine's rules discard data.

The only rewrite is headed by the contact: a waiting history facing a given
one releases both, `Meet(Wait(x), Give(y)) ⟶ Meet(x, y)`.  The language is
therefore interactive, with histories as its interacting sort, and its
interaction rule has the plainest cut form: two prefixes, two continuations,
nothing moved.

What this module establishes is structural: the language validates, passes
the flow gate, and is an iGSLT whose interaction rule fires.  That its
static equivalence encodes halting is the subject of the modules that import
this one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism

/-- A configuration being run. -/
def now (configuration : Pattern) : Pattern := .apply "Now" [configuration]

/-- A configuration followed by a history. -/
def andThen (configuration history : Pattern) : Pattern :=
  .apply "Then" [configuration, history]

/-- A configuration known to finish. -/
def flag (configuration : Pattern) : Pattern := .apply "Flag" [configuration]

/-- Two histories in contact. -/
def meet (left right : Pattern) : Pattern := .apply "Meet" [left, right]

/-- A history waiting at the contact. -/
def wait (history : Pattern) : Pattern := .apply "Wait" [history]

/-- A history given at the contact. -/
def give (history : Pattern) : Pattern := .apply "Give" [history]

/-- The six constructors of histories. -/
def historyConstructors : List GrammarRule := [
    { label := "Now", category := "Hist",
      params := [.simple "c" (.base "Cfg")],
      syntaxPattern := [.nonTerminal "c"] },
    { label := "Then", category := "Hist",
      params := [.simple "c" (.base "Cfg"), .simple "h" (.base "Hist")],
      syntaxPattern := [.nonTerminal "c", .nonTerminal "h"] },
    { label := "Flag", category := "Hist",
      params := [.simple "c" (.base "Cfg")],
      syntaxPattern := [.nonTerminal "c"] },
    { label := "Meet", category := "Hist",
      params := [.simple "left" (.base "Hist"), .simple "right" (.base "Hist")],
      syntaxPattern := [.nonTerminal "left", .nonTerminal "right"] },
    { label := "Wait", category := "Hist",
      params := [.simple "h" (.base "Hist")],
      syntaxPattern := [.nonTerminal "h"] },
    { label := "Give", category := "Hist",
      params := [.simple "h" (.base "Hist")],
      syntaxPattern := [.nonTerminal "h"] }
  ]

/-- The machine's constructors followed by those of histories. -/
def historyTerms : List GrammarRule := terms ++ historyConstructors

/-- A halted configuration is finished. -/
def haltLaw : Equation where
  name := "Halted"
  typeContext := [("w", .base "Nats")]
  premises := []
  left := now (.apply "Halt" [.fvar "w"])
  right := flag (.apply "Halt" [.fvar "w"])

/-- One step of a run, recorded: `Now(l) = Then(l, Now(r))`. -/
def nowLaw (rule : RewriteRule) : Equation where
  name := "Now" ++ rule.name
  typeContext := rule.typeContext
  premises := []
  left := now rule.left
  right := andThen rule.left (now rule.right)

/-- A finished run carried back one step: `Then(l, Flag(r)) = Flag(l)`. -/
def flagLaw (rule : RewriteRule) : Equation where
  name := "Flag" ++ rule.name
  typeContext := rule.typeContext
  premises := []
  left := andThen rule.left (flag rule.right)
  right := flag rule.left

/-- The equations: the halting law, then the two laws of every machine rule. -/
def historyEquations : List Equation :=
  haltLaw :: (rewrites.map nowLaw ++ rewrites.map flagLaw)

/-- A waiting history facing a given one releases both. -/
def meetRule : RewriteRule where
  name := "Meet"
  typeContext := [("x", .base "Hist"), ("y", .base "Hist")]
  premises := []
  left := meet (wait (.fvar "x")) (give (.fvar "y"))
  right := meet (.fvar "x") (.fvar "y")

/-- The machine's runs as an equational theory with one interaction rule. -/
def historyMachine : LanguageDef :=
  { name := "HistoryMachine"
    types := ["Nat", "Nats", "Code", "Cont", "Cfg", "Hist"]
    terms := historyTerms
    equations := historyEquations
    rewrites := [meetRule] }

/-! ## Structural admission -/

/-- Every generated equation passes the row test of the declaration gate. -/
theorem historyEquations_ok :
    historyMachine.equations.all (LanguageDef.plainEquationOk historyMachine) = true := by
  decide +kernel

/-- The interaction rule passes the row test of the declaration gate. -/
theorem meetRule_ok : LanguageDef.plainRewriteOk historyMachine meetRule = true := by
  decide +kernel

/-- The language passes the structural declaration gate. -/
theorem historyMachine_validate_eq_nil : historyMachine.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro equation membership
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp historyEquations_ok equation membership)
  · intro rewrite membership
    obtain rfl : rewrite = meetRule := List.mem_singleton.mp membership
    exact LanguageDef.validateRewrite_eq_nil_of_plainRewriteOk meetRule_ok

/-- Every equation has the same variables on both sides, and the interaction
rule binds its right side on its left. -/
theorem historyMachine_plainFlowOk : LanguageDef.plainFlowOk historyMachine = true := by
  decide +kernel

/-- The language passes the ordered binding-flow gate with no relation mode. -/
theorem historyMachine_executionAdmissionErrors_eq_nil :
    historyMachine.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes historyMachine
    historyMachine_validate_eq_nil
    (LanguageDef.executionFlowErrors_eq_nil_of_plainFlowOk historyMachine_plainFlowOk [])

/-! ## The interactive theory -/

/-- The exact validated definition. -/
def historyValidated : ValidatedLanguageDef :=
  ⟨historyMachine, historyMachine_validate_eq_nil⟩

/-- Histories are the interacting sort, `Meet` the contact, and the rule at
which a waiting history faces a given one the interaction. -/
def historyPresentation : InteractivePresentation where
  presentation := historyValidated
  interactingSort := ⟨historyMachine.types[5], List.getElem_mem (by decide)⟩
  contactConstructor := ⟨historyMachine.terms[22], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨meetRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- The history theory as an iGSLT. -/
def historyTheory : IGSLT where
  presentation := historyPresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := historyMachine
          admitted := historyMachine_executionAdmissionErrors_eq_nil }
      exactLanguage := rfl }

/-- The interacting sort is the sort of histories. -/
theorem historyPresentation_interactingSort :
    historyPresentation.interactingLangSort.1 = "Hist" :=
  rfl

/-- The interaction rule is a base rule: the theory is interactive. -/
theorem historyMachine_isInteractive : IsInteractive historyMachine :=
  historyPresentation.isInteractive (isBaseRewrite_of_premises_eq_nil rfl)

/-- The halted configuration with empty output. -/
def haltedEmpty : Pattern := .apply "Halt" [.apply "Nil" []]

/-- A waiting finished run facing a given one, as a closed history. -/
def meetExample : historyPresentation.Term :=
  ClosedTerm.ofCheck (meet (wait (flag haltedEmpty)) (give (flag haltedEmpty)))
    (by decide +kernel)

/-- The two finished runs in contact, as a closed history. -/
def metExample : historyPresentation.Term :=
  ClosedTerm.ofCheck (meet (flag haltedEmpty) (flag haltedEmpty)) (by decide +kernel)

/-- The interaction rule fires: the theory has a real step at its contact. -/
theorem meetExample_steps : historyTheory.toGSLT.Step meetExample metExample :=
  primitiveStep_to_presentedStep (base := defaultBasePremises)
    (presentation := historyPresentation)
    (exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩)

end Mettapedia.Languages.PartrecMachine
