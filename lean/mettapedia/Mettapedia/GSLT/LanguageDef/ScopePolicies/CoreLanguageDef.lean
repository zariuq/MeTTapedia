import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.UnaryNumerals
import Mettapedia.GSLT.LanguageDef.Contexts.Presented
import Mettapedia.GSLT.LanguageDef.ScopePolicies.Core

/-!
# The lexical-fresh core as a five-field language definition

`lexicalFreshCore` is a `LanguageDef`: a name, the sorts, the term formers,
no equation, and one rewrite.

* **Sorts.**  `Sym` (symbols, as unary numerals), `Tm` (terms), `Store`,
  `Cfg`.
* **Term formers.**  Those of the scope-bearing terms: `Sym`, `Fn`, `Par`,
  `Lam`, `App`, `Quote`, `PQuote`, `Ctx`, `Let`, `Alt`; a store as a list of
  bindings, `Empty` and `Bind`; and a configuration `Cfg` of a store and a
  term.  A slot is a free variable of sort `Tm`, as in
  `TemplateScope.LexicalFreshGSLT`.
* **The rewrite `LetFresh`.**  `Cfg(σ, Let(k, Sym(s), b)) ⟶
  Cfg(Bind(k, Sym(s), σ), b)`, with two freshness premises: `k # Sym(s)`, the
  premise that `let_slot_freshness_premise` discharges for every elaborated
  `let` (the slot is apart from the value), and `k # σ`, the slot is not bound
  in the store.

It validates (`lexicalFreshCore_validate`), so it presents a theory through its
contexts (`lexicalFreshTheory`, by `Contexts.contextTheory`).

## Agreement, as far as it is proved

* On the evaluator's side, for every name type and both disciplines: a `let`
  of a symbol into a slot that the store does not bind runs as its body from
  the store extended by that binding (`run_let_symbol`); into a slot bound to
  the same symbol it runs the body from the same store (`run_let_same`); into
  a slot bound to another symbol it has no result (`run_let_conflict`).
* On the definition's side, by kernel-checked computation on instances: the
  rule fires on a fresh slot and gives the extended store (`letFresh_fires`),
  and it does not fire when the store binds the slot (`letFresh_blocked`) or
  when the name is not a variable (`letFresh_needs_name`).

The agreement on a fragment is in `ScopePolicies.StraightLine` (straight-line
programs: `straight_agreement`) and `ScopePolicies.StraightText` (straight-line
authored text under lexical fresh: `lexicalFresh_straight_agreement`).  It is
about the reduction that the definition generates on patterns, of which the
reduction of `lexicalFreshTheory` is the part on closed, sorted terms; a slot
is a free variable, so a configuration with a slot is not a term of
`lexicalFreshTheory` (`slot_not_presented_term`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## The definition -/

namespace LexicalFreshCore

/-- The symbol numbered `index`, as a term of sort `Sym`. -/
def numeral (index : Nat) : Pattern := Pattern.unary "SZero" "SSucc" index

/-- A symbol, as a term. -/
def symT (symbol : Pattern) : Pattern := .apply "Sym" [symbol]

/-- `(let k w b)`. -/
def letT (pattern value body : Pattern) : Pattern := .apply "Let" [pattern, value, body]

/-- The store with no binding. -/
def emptyStore : Pattern := .apply "Empty" []

/-- A binding in front of a store. -/
def bind (slot value rest : Pattern) : Pattern := .apply "Bind" [slot, value, rest]

/-- A configuration: a store and a term. -/
def cfg (store term : Pattern) : Pattern := .apply "Cfg" [store, term]

/-- The term formers. -/
def terms : List GrammarRule := [
    { label := "SZero", category := "Sym", params := [], syntaxPattern := [] },
    { label := "SSucc", category := "Sym",
      params := [.simple "symbol" (.base "Sym")], syntaxPattern := [.nonTerminal "symbol"] },
    { label := "Sym", category := "Tm",
      params := [.simple "symbol" (.base "Sym")], syntaxPattern := [.nonTerminal "symbol"] },
    { label := "Fn", category := "Tm",
      params := [.simple "equation" (.base "Sym")], syntaxPattern := [.nonTerminal "equation"] },
    { label := "Par", category := "Tm", params := [], syntaxPattern := [] },
    { label := "Lam", category := "Tm",
      params := [.simple "body" (.base "Tm")], syntaxPattern := [.nonTerminal "body"] },
    { label := "App", category := "Tm",
      params := [.simple "function" (.base "Tm"), .simple "argument" (.base "Tm")],
      syntaxPattern := [.nonTerminal "function", .nonTerminal "argument"] },
    { label := "Quote", category := "Tm",
      params := [.simple "code" (.base "Tm")], syntaxPattern := [.nonTerminal "code"] },
    { label := "PQuote", category := "Tm",
      params := [.simple "code" (.base "Tm")], syntaxPattern := [.nonTerminal "code"] },
    { label := "Ctx", category := "Tm", params := [], syntaxPattern := [] },
    { label := "Let", category := "Tm",
      params := [.simple "pattern" (.base "Tm"), .simple "value" (.base "Tm"),
        .simple "body" (.base "Tm")],
      syntaxPattern := [.nonTerminal "pattern", .nonTerminal "value", .nonTerminal "body"] },
    { label := "Alt", category := "Tm",
      params := [.simple "first" (.base "Tm"), .simple "second" (.base "Tm")],
      syntaxPattern := [.nonTerminal "first", .nonTerminal "second"] },
    { label := "Empty", category := "Store", params := [], syntaxPattern := [] },
    { label := "Bind", category := "Store",
      params := [.simple "slot" (.base "Tm"), .simple "value" (.base "Tm"),
        .simple "rest" (.base "Store")],
      syntaxPattern := [.nonTerminal "slot", .nonTerminal "value", .nonTerminal "rest"] },
    { label := "Cfg", category := "Cfg",
      params := [.simple "store" (.base "Store"), .simple "term" (.base "Tm")],
      syntaxPattern := [.nonTerminal "store", .nonTerminal "term"] }
  ]

/-- **The `let` of a fresh slot.**  The two premises are freshness premises:
the slot is apart from the value, and the store does not bind it. -/
def letFresh : RewriteRule :=
  { name := "LetFresh"
    typeContext := [("k", .base "Tm"), ("s", .base "Sym"), ("b", .base "Tm"),
      ("st", .base "Store")]
    premises := [
      .freshness { varName := "k", term := symT (.fvar "s") },
      .freshness { varName := "k", term := .fvar "st" }]
    left := cfg (.fvar "st") (letT (.fvar "k") (symT (.fvar "s")) (.fvar "b"))
    right := cfg (bind (.fvar "k") (symT (.fvar "s")) (.fvar "st")) (.fvar "b") }

end LexicalFreshCore

open LexicalFreshCore

/-- **The lexical-fresh core, as a five-field language definition.** -/
def lexicalFreshCore : LanguageDef :=
  { name := "LexicalFreshCore"
    types := ["Sym", "Tm", "Store", "Cfg"]
    terms := LexicalFreshCore.terms
    equations := []
    rewrites := [letFresh] }

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem lexicalFreshCore_rewrites_validate :
    ∀ rule ∈ lexicalFreshCore.rewrites, LanguageDef.validateRewrite lexicalFreshCore rule = [] := by
  intro rule membership
  simp only [lexicalFreshCore, List.mem_cons, List.mem_nil_iff, or_false] at membership
  subst membership
  simp +decide [LanguageDef.validateRewrite, lexicalFreshCore, LexicalFreshCore.terms,
    LexicalFreshCore.letFresh, LexicalFreshCore.cfg, LexicalFreshCore.bind, LexicalFreshCore.letT,
    LexicalFreshCore.symT, LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseForAllParams, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames, LanguageDef.typeNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The definition validates.** -/
theorem lexicalFreshCore_validate : lexicalFreshCore.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  exact lexicalFreshCore_rewrites_validate

/-- The validated definition. -/
def lexicalFreshPresentation : ValidatedLanguageDef :=
  ⟨lexicalFreshCore, lexicalFreshCore_validate⟩

/-- **The theory that the definition presents through its contexts.** -/
def lexicalFreshTheory : ContextTheory.{0} :=
  Contexts.contextTheory (engineBasePremises RelationEnv.empty) lexicalFreshPresentation

/-- It has no authored equation. -/
theorem lexicalFreshCore_equations : lexicalFreshCore.equations = [] := rfl

/-- Its one rewrite carries two freshness premises. -/
theorem lexicalFreshCore_premises :
    lexicalFreshCore.rewrites.map (fun rule => rule.premises.length) = [2] := rfl

/-! ## The definition's side, on instances -/

/-- One step of the definition, computed. -/
def coreReducts (term : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) lexicalFreshCore 1 term

/-- A computed reduct is a step of the definition. -/
theorem step_of_coreReducts {term next : Pattern} (found : next ∈ coreReducts term) :
    Step (engineBasePremises RelationEnv.empty) lexicalFreshCore term next :=
  ⟨1, mem_rewriteAt_iff_stepAt.mp found⟩

set_option maxRecDepth 100000 in
/-- **Positive: the rule fires on a fresh slot.**
`Cfg(Empty, Let($y, Sym(1), $y)) ⟶ Cfg(Bind($y, Sym(1), Empty), $y)`, and
nothing else. -/
theorem letFresh_fires :
    coreReducts (cfg emptyStore (letT (.fvar "y") (symT (numeral 1)) (.fvar "y"))) =
      [cfg (bind (.fvar "y") (symT (numeral 1)) emptyStore) (.fvar "y")] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Positive: a second `let`, of another slot, fires on the extended store. -/
theorem letFresh_fires_again :
    coreReducts (cfg (bind (.fvar "y") (symT (numeral 1)) emptyStore)
        (letT (.fvar "z") (symT (numeral 2)) (.fvar "y"))) =
      [cfg (bind (.fvar "z") (symT (numeral 2)) (bind (.fvar "y") (symT (numeral 1)) emptyStore))
        (.fvar "y")] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Negative: the freshness premise fails when the store binds the slot.** -/
theorem letFresh_blocked :
    coreReducts (cfg (bind (.fvar "y") (symT (numeral 1)) emptyStore)
        (letT (.fvar "y") (symT (numeral 2)) (.fvar "y"))) = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Negative: a freshness premise needs a name; a `let` whose pattern is not a
variable does not fire. -/
theorem letFresh_needs_name :
    coreReducts (cfg emptyStore (letT (symT (numeral 0)) (symT (numeral 1)) (.fvar "y"))) = [] := by
  decide +kernel

/-! ## The evaluator's side -/

section Evaluator

universe u v

variable {S : Type u} {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]

/-- **A `let` of a symbol into a slot that the store does not bind** runs as
its body from the store extended by the binding. -/
theorem run_let_symbol (d : Disc) (prog : S → Option (Tm S Y)) (n : ℕ) (π : Path)
    (σ : GStore S Y) (k : Nm Y) (s : S) (body : Tm S Y) (fresh : σ k = none) :
    run d prog (n + 2) π σ (.letP (.var k) (.sym s) body) =
      run d prog (n + 1) (π ++ [1]) (fun m => if m = k then some (.sym s) else σ m) body := by
  show step d prog (run d prog (n + 1)) π σ (.letP (.var k) (.sym s) body) = _
  have value : run d prog (n + 1) (π ++ [0]) σ (.sym s) = some [(.sym s, σ)] := rfl
  simp only [step, letLam?, value, bindOpt_some_singleton, act_sym, Tm.toGVal?, GVal.toTm,
    matchT, refineStep, fresh]

/-- A `let` of a symbol into a slot that the store binds to that symbol runs
as its body from the same store: the evaluator's `let` refines. -/
theorem run_let_same (d : Disc) (prog : S → Option (Tm S Y)) (n : ℕ) (π : Path)
    (σ : GStore S Y) (k : Nm Y) (s : S) (body : Tm S Y) (bound : σ k = some (.sym s)) :
    run d prog (n + 2) π σ (.letP (.var k) (.sym s) body) =
      run d prog (n + 1) (π ++ [1]) σ body := by
  show step d prog (run d prog (n + 1)) π σ (.letP (.var k) (.sym s) body) = _
  have value : run d prog (n + 1) (π ++ [0]) σ (.sym s) = some [(.sym s, σ)] := rfl
  simp only [step, letLam?, value, bindOpt_some_singleton, act_sym, Tm.toGVal?, GVal.toTm,
    matchT, refineStep, bound, if_true]

/-- A `let` of a symbol into a slot that the store binds to another symbol has
no result. -/
theorem run_let_conflict (d : Disc) (prog : S → Option (Tm S Y)) (n : ℕ) (π : Path)
    (σ : GStore S Y) (k : Nm Y) (s other : S) (body : Tm S Y)
    (bound : σ k = some (.sym other)) (differ : other ≠ s) :
    run d prog (n + 2) π σ (.letP (.var k) (.sym s) body) = some [] := by
  show step d prog (run d prog (n + 1)) π σ (.letP (.var k) (.sym s) body) = _
  have value : run d prog (n + 1) (π ++ [0]) σ (.sym s) = some [(.sym s, σ)] := rfl
  have apart : (GVal.sym other : GVal S Y) ≠ .sym s := fun same => differ (GVal.sym.inj same)
  simp only [step, letLam?, value, bindOpt_some_singleton, act_sym, Tm.toGVal?, GVal.toTm,
    matchT, refineStep, bound, if_neg apart]

end Evaluator

#print axioms lexicalFreshCore_validate
#print axioms letFresh_fires
#print axioms letFresh_blocked
#print axioms run_let_symbol
#print axioms run_let_conflict

end Mettapedia.GSLT.LanguageDef.ScopePolicies
