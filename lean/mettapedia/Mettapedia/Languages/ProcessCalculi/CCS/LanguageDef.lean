import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# CCS as a language definition

The fragment of Milner's calculus of communicating systems in which
interaction happens: inaction, prefixing by an action or by its co-action,
and parallel composition.  Parallel composition is authored as a bag with
unit `CNil`, so associativity, commutativity and the unit law are the
presentation's own collection laws.

There is one rule, and it is a base rule.  A process prefixed by an action and
a process prefixed by the complementary action on the same name, side by side
in a parallel composition, synchronise; both continuations are released into
the composition and nothing passes between them.  The rule names the rest of
the composition, so it fires in any parallel context; a nested composition is
flattened by the presentation's own laws, so no separate rule for reduction
inside a composition is needed.

Names are unary numerals of their own sort, so there are infinitely many
actions and the signature is finite.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- Synchronisation of complementary prefixes on one name. -/
def ccsSyncRewrite : RewriteRule where
  name := "Sync"
  typeContext := [("a", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc)]
  premises := []
  left := .collection .hashBag [
    .apply "CAct" [.fvar "a", .fvar "p"],
    .apply "CCoAct" [.fvar "a", .fvar "q"]
  ] (some "rest")
  right := .collection .hashBag [.fvar "p", .fvar "q"] (some "rest")

/-- CCS with prefixing and parallel composition. -/
def ccsCalc : LanguageDef := {
  name := "CCS",
  types := ["Proc", "Name"],
  terms := [
    -- CNil . |- "0" : Proc
    { label := "CNil", category := "Proc", params := [],
      syntaxPattern := [.terminal "0"] },

    -- CPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc
    { label := "CPar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
      algebra? := some { flatten := true, unit := some "CNil" } },

    -- CAct . a:Name, p:Proc |- a "." p : Proc
    { label := "CAct", category := "Proc",
      params := [.simple "a" TypeExpr.name, .simple "p" TypeExpr.proc],
      syntaxPattern := [.nonTerminal "a", .terminal ".", .nonTerminal "p"] },

    -- CCoAct . a:Name, p:Proc |- "~" a "." p : Proc
    { label := "CCoAct", category := "Proc",
      params := [.simple "a" TypeExpr.name, .simple "p" TypeExpr.proc],
      syntaxPattern := [.terminal "~", .nonTerminal "a", .terminal ".", .nonTerminal "p"] },

    -- NBase . |- "a" : Name
    { label := "NBase", category := "Name", params := [],
      syntaxPattern := [.terminal "a"] },

    -- NNext . n:Name |- n "'" : Name
    { label := "NNext", category := "Name",
      params := [.simple "n" TypeExpr.name],
      syntaxPattern := [.nonTerminal "n", .terminal "'"] }
  ],
  equations := [],
  rewrites := [ccsSyncRewrite]
}

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- The definition passes the declaration gate. -/
theorem ccsCalc_validate_eq_nil : ccsCalc.validate = [] := by
  simp [LanguageDef.validate, ccsCalc, ccsSyncRewrite,
    LanguageDef.validateRewrite, LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.typeNames,
    TypeDecl.plain, TypeExpr.baseNames, TypeExpr.proc, TypeExpr.name, TypeExpr.bag,
    TypeExpr.baseType, TermParam.bodyName, TermParam.typeExpr]

/-- The synchronisation rule needs no external relation mode and its
contractum uses only variables bound by its redex. -/
theorem ccsCalc_executionFlowErrors_eq_nil :
    ccsCalc.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    simp [ccsCalc] at membership
    subst rule
    rfl
  · intro rule membership name nameMembership
    simp [ccsCalc] at membership
    subst rule
    simp [ccsSyncRewrite, Pattern.freeFvarNames] at nameMembership ⊢
    tauto

/-- The definition passes the ordered binding-flow gate with no external
relation mode. -/
theorem ccsCalc_executionAdmissionErrors_eq_nil :
    ccsCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes
    ccsCalc ccsCalc_validate_eq_nil ccsCalc_executionFlowErrors_eq_nil

/-! ## A synchronisation -/

/-- The name `a`. -/
def nameA : Pattern := .apply "NBase" []

/-- Inaction. -/
def nil : Pattern := .apply "CNil" []

/-- `a.0 | ~a.(a.0)`. -/
def handshake : Pattern :=
  .collection .hashBag [
    .apply "CAct" [nameA, nil],
    .apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]]] none

/-- `0 | a.0`: both continuations, released side by side. -/
def handshakeDone : Pattern :=
  .collection .hashBag [nil, .apply "CAct" [nameA, nil]] none

/-- Complementary prefixes on one name synchronise. -/
theorem handshake_steps : Step base ccsCalc handshake handshakeDone :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- `a.0 | ~a'.0`: the names differ. -/
def mismatch : Pattern :=
  .collection .hashBag [
    .apply "CAct" [nameA, nil],
    .apply "CCoAct" [.apply "NNext" [nameA], nil]] none

/-- Prefixes on different names do not synchronise: the surfaces must match. -/
theorem mismatch_stuck : rewriteAt base ccsCalc 2 mismatch = [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.CCS
