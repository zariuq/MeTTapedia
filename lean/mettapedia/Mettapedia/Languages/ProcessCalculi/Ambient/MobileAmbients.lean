import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.FlowAdmission
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Mobile ambients without restriction, as a language definition

The fragment of the ambient calculus in which boundaries move and dissolve:
inaction, parallel composition, the three capabilities `in`, `out` and
`open`, each prefixing a process, and the ambient `n[P]`.  Parallel
composition is a bag with unit, as in the other process calculi here.  Names
are unary numerals of their own sort, so closed processes exist without a
binder for names.

There are three base rules and two contextual ones.

* `open n.P | n[Q] ⟶ P | Q`: the boundary named `n` dissolves.
* `n[in m.P | R] | m[S] ⟶ m[n[P | R] | S]`: the ambient `n` enters `m`.
* `m[n[out m.P | R] | S] ⟶ n[P | R] | m[S]`: the ambient `n` leaves `m`.
* A component of a parallel composition may reduce, and so may the content
  of an ambient: a process inside a boundary is running.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Mobile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- The constructors. -/
def terms : List GrammarRule := [
    { label := "AZero", category := "Proc", params := [], syntaxPattern := [] },
    { label := "APar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)],
      syntaxPattern := [.nonTerminal "ps"],
      algebra? := some { flatten := true, unit := some "AZero" } },
    { label := "AIn", category := "Proc",
      params := [.simple "n" TypeExpr.name, .simple "p" TypeExpr.proc],
      syntaxPattern := [.nonTerminal "n", .nonTerminal "p"] },
    { label := "AOut", category := "Proc",
      params := [.simple "n" TypeExpr.name, .simple "p" TypeExpr.proc],
      syntaxPattern := [.nonTerminal "n", .nonTerminal "p"] },
    { label := "AOpen", category := "Proc",
      params := [.simple "n" TypeExpr.name, .simple "p" TypeExpr.proc],
      syntaxPattern := [.nonTerminal "n", .nonTerminal "p"] },
    { label := "AAmb", category := "Proc",
      params := [.simple "n" TypeExpr.name, .simple "p" TypeExpr.proc],
      syntaxPattern := [.nonTerminal "n", .nonTerminal "p"] },
    { label := "NBase", category := "Name", params := [], syntaxPattern := [] },
    { label := "NNext", category := "Name",
      params := [.simple "n" TypeExpr.name],
      syntaxPattern := [.nonTerminal "n"] }
  ]

/-- The ambient `name[content]`. -/
def amb (name content : Pattern) : Pattern := .apply "AAmb" [name, content]

/-- A parallel composition of listed components and a named rest. -/
def par (components : List Pattern) (rest : Option String) : Pattern :=
  .collection .hashBag components rest

/-- `open n.P | n[Q] ⟶ P | Q`. -/
def openRule : RewriteRule where
  name := "Open"
  typeContext := [("n", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc)]
  premises := []
  left := par [.apply "AOpen" [.fvar "n", .fvar "p"], amb (.fvar "n") (.fvar "q")] (some "rest")
  right := par [.fvar "p", .fvar "q"] (some "rest")

/-- `n[in m.P | R] | m[S] ⟶ m[n[P | R] | S]`. -/
def inRule : RewriteRule where
  name := "In"
  typeContext := [("n", TypeExpr.name), ("m", TypeExpr.name), ("p", TypeExpr.proc),
    ("s", TypeExpr.proc)]
  premises := []
  left := par
    [amb (.fvar "n") (par [.apply "AIn" [.fvar "m", .fvar "p"]] (some "inner")),
      amb (.fvar "m") (.fvar "s")] (some "rest")
  right := par
    [amb (.fvar "m") (par [amb (.fvar "n") (par [.fvar "p"] (some "inner")), .fvar "s"] none)]
    (some "rest")

/-- `m[n[out m.P | R] | S] ⟶ n[P | R] | m[S]`. -/
def outRule : RewriteRule where
  name := "Out"
  typeContext := [("n", TypeExpr.name), ("m", TypeExpr.name), ("p", TypeExpr.proc)]
  premises := []
  left := amb (.fvar "m")
    (par [amb (.fvar "n") (par [.apply "AOut" [.fvar "m", .fvar "p"]] (some "inner"))]
      (some "rest"))
  right := par
    [amb (.fvar "n") (par [.fvar "p"] (some "inner")), amb (.fvar "m") (par [] (some "rest"))]
    none

/-- A component of a parallel composition may reduce. -/
def parCongRule : RewriteRule where
  name := "ParCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := par [.fvar "S"] (some "rest")
  right := par [.fvar "T"] (some "rest")

/-- The content of an ambient may reduce. -/
def ambCongRule : RewriteRule where
  name := "AmbCong"
  typeContext := [("n", TypeExpr.name)]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := amb (.fvar "n") (.fvar "S")
  right := amb (.fvar "n") (.fvar "T")

/-- Mobile ambients without restriction. -/
def ambientCalc : LanguageDef :=
  { name := "MobileAmbients"
    types := ["Proc", "Name"]
    terms := terms
    equations := []
    rewrites := [openRule, inRule, outRule, parCongRule, ambCongRule] }

/-! ## Validation -/

theorem baseRules_validate :
    ∀ rule ∈ [openRule, inRule, outRule],
      LanguageDef.validateRewrite ambientCalc rule = [] := by
  intro rule membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [openRule, inRule, outRule, ambientCalc, terms, amb, par]

theorem contextualRules_validate :
    ∀ rule ∈ [parCongRule, ambCongRule],
      LanguageDef.validateRewrite ambientCalc rule = [] := by
  intro rule membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
      (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [parCongRule, ambCongRule, ambientCalc, terms, amb, par]

/-- The definition passes the declaration gate. -/
theorem ambientCalc_validate_eq_nil : ambientCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    have listed : rewrite ∈ [openRule, inRule, outRule, parCongRule, ambCongRule] := membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl
    · exact baseRules_validate _ (by simp)
    · exact baseRules_validate _ (by simp)
    · exact baseRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)

/-- Every rule passes the binding-flow gate by its shape. -/
theorem ambientCalc_executionFlowErrors_eq_nil :
    ambientCalc.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleFlows _ _ rfl
  intro rule membership
  have listed : rule ∈ [openRule, inRule, outRule, parCongRule, ambCongRule] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl
  · refine .plain rfl ?_
    intro name membership
    simp [openRule, amb, par, Pattern.freeFvarNames] at membership ⊢
    tauto
  · refine .plain rfl ?_
    intro name membership
    simp [inRule, amb, par, Pattern.freeFvarNames] at membership ⊢
    tauto
  · refine .plain rfl ?_
    intro name membership
    simp [outRule, amb, par, Pattern.freeFvarNames] at membership ⊢
    tauto
  · refine .contextual "S" "T" rfl (by simp [parCongRule, par, Pattern.freeFvarNames]) ?_
    intro name membership
    simp [parCongRule, par, Pattern.freeFvarNames] at membership ⊢
    tauto
  · refine .contextual "S" "T" rfl (by simp [ambCongRule, amb, Pattern.freeFvarNames]) ?_
    intro name membership
    simp [ambCongRule, amb, Pattern.freeFvarNames] at membership ⊢
    tauto

/-- The definition passes the ordered binding-flow gate with no relation mode. -/
theorem ambientCalc_executionAdmissionErrors_eq_nil :
    ambientCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes
    ambientCalc ambientCalc_validate_eq_nil ambientCalc_executionFlowErrors_eq_nil

/-! ## What the rules do -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- The name `a`. -/
def nameA : Pattern := .apply "NBase" []

/-- The name `b`. -/
def nameB : Pattern := .apply "NNext" [nameA]

/-- Inaction. -/
def nil : Pattern := .apply "AZero" []

/-- `open a.0 | a[0]`. -/
def opening : Pattern :=
  par [.apply "AOpen" [nameA, nil], amb nameA nil] none

/-- The boundary dissolves. -/
theorem opening_dissolves : Step base ambientCalc opening (par [nil, nil] none) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- `a[in b.0] | b[0]`. -/
def entering : Pattern :=
  par [amb nameA (par [.apply "AIn" [nameB, nil]] none), amb nameB nil] none

/-- The ambient `a` enters `b`. -/
theorem entering_moves :
    Step base ambientCalc entering
      (par [amb nameB (par [amb nameA (par [nil] none), nil] none)] none) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- `b[open a.0 | a[0]]`: the same dissolution, inside a boundary. -/
def openingInside : Pattern := amb nameB opening

/-- A process inside a boundary is running. -/
theorem openingInside_dissolves :
    Step base ambientCalc openingInside (amb nameB (par [nil, nil] none)) :=
  exists_mem_rewriteAt_iff_step.mp ⟨2, by decide +kernel⟩

/-- A capability with no boundary beside it does nothing. -/
theorem capability_alone_stuck (target : Pattern) :
    ¬ Step base ambientCalc (.apply "AOpen" [nameB, nil]) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule membership
  have listed : rule ∈ [openRule, inRule, outRule, parCongRule, ambCongRule] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- The dissolution rule does not fire when the capability names another
boundary. -/
theorem open_needs_matching_name :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule ambientCalc openRule
      (par [.apply "AOpen" [nameB, nil], amb nameA nil] none) = [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.Ambient.Mobile
