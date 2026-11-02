import Mettapedia.Languages.ProcessCalculi.Ambient.MobileAmbients
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Replication
import Mettapedia.OSLF.MeTTaIL.EquationalAdmission

/-!
# Mobile ambients with restriction and replication

Cardelli and Gordon's pure mobile ambients: inaction, parallel composition, restriction of a name, replication, the
ambient `n[P]` and the three capabilities `in n`, `out n` and `open n`, each prefixing a process. Names are variables
of their own sort, bound by restriction.

- Parallel composition is a bag with unit `AZero`, so its associativity, commutativity and unit law are the
  presentation's own collection laws.
- Restriction (`ANu`) binds a name over a process, with the laws of restriction: restriction of inaction, exchange of
  restrictions and scope extrusion; replication (`ARep`) takes any process, with the laws of replication: unfolding,
  inaction, idempotence, distribution and duplication. These are the restriction-block laws of the block
  `ambientRepBlock`.
- **A restriction crosses an ambient boundary** not named by it: `(νn) m[P] = m[(νn) P]` for `n ≠ m`
  (`ambientBoundary`). In the locally nameless syntax the ambient's name stands outside the binder on one side and
  under it on the other, taking no bound name, so it cannot be the restricted one.

The rules are the reaction rules. An ambient enters a sibling named by its `in` capability (`In`), leaves its parent
named by its `out` capability (`Out`), and an `open` capability dissolves a sibling ambient it names (`Open`).
Reaction happens inside a parallel composition, under a restriction and inside an ambient (`ParCong`, `ResCong`,
`AmbCong`). A replicated process takes part through its unfolding, a law.

## References

- Cardelli and Gordon (2000), "Mobile Ambients", Theoretical Computer Science 240(1), sections 2.1–2.3
- Dal Zilio (2000), "Spatial Congruence for Ambients is Decidable", the extended structural congruence
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Full

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Block ReplicationBlock replicationBlockLaws)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## The definition -/

/-- The blocks of the ambient calculus: inaction, restriction, processes and names. -/
abbrev ambientBlock : Block := ⟨"AZero", "ANu", "Proc", "Name", [], []⟩

/-- Its blocks with replication, read by the refined labelling. -/
abbrev ambientRepBlock : ReplicationBlock := ⟨ambientBlock, "ARep", true⟩

/-- A constructor taking a name and a process. -/
def prefixRule (label : String) (keyword : String) : GrammarRule :=
  { label := label, category := "Proc",
    params := [.simple "n" (.base "Name"), .simple "p" (.base "Proc")],
    syntaxPattern := [.terminal keyword, .nonTerminal "n", .terminal ".", .nonTerminal "p"] }

/-- The constructors. -/
def terms : List GrammarRule := [
    { label := "AZero", category := "Proc", params := [], syntaxPattern := [.terminal "0"] },
    { label := "APar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
      algebra? := some { flatten := true, unit := some "AZero" } },
    { label := "ANu", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "ν", .nonTerminal "body"] },
    { label := "ARep", category := "Proc",
      params := [.simple "p" (TypeExpr.base "Proc")],
      syntaxPattern := [.terminal "!", .nonTerminal "p"] },
    { label := "AAmb", category := "Proc",
      params := [.simple "n" (.base "Name"), .simple "p" (.base "Proc")],
      syntaxPattern := [.nonTerminal "n", .terminal "[", .nonTerminal "p", .terminal "]"] },
    prefixRule "AIn" "in",
    prefixRule "AOut" "out",
    prefixRule "AOpen" "open"
  ]

/-- `m[(νn) P] = (νn) m[P]`: a restriction crosses the boundary of an ambient it does not name. -/
def ambientBoundary : Equation where
  name := "AmbientBoundary"
  typeContext := [("m", .base "Name"), ("P", .base "Proc")]
  premises := []
  left := .apply "AAmb" [.fvar "m", .apply "ANu" [.lambda none (.fvar "P")]]
  right := .apply "ANu" [.lambda none (.apply "AAmb" [.fvar "m", .fvar "P"])]
  bindings := some
    { dependencies := [("m", []), ("P", [.base "Name"])]
      occurrences :=
        [{ name := "m", site := .left, path := [0], arguments := [] },
         { name := "P", site := .left, path := [1, 0, 0], arguments := [.bvar 0] },
         { name := "m", site := .right, path := [0, 0, 0], arguments := [] },
         { name := "P", site := .right, path := [0, 0, 1], arguments := [.bvar 0] }] }

open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb par)

/-- `n[in m.P | R] | m[S] ~> m[n[P | R] | S]`. -/
def inRule : RewriteRule where
  name := "In"
  typeContext := [("n", .base "Name"), ("m", .base "Name"), ("p", .base "Proc"), ("s", .base "Proc")]
  premises := []
  left := par
    [amb (.fvar "n") (par [.apply "AIn" [.fvar "m", .fvar "p"]] (some "inner")), amb (.fvar "m") (.fvar "s")]
    (some "rest")
  right := par
    [amb (.fvar "m") (par [amb (.fvar "n") (par [.fvar "p"] (some "inner")), .fvar "s"] none)] (some "rest")

/-- `m[n[out m.P | R] | S] ~> n[P | R] | m[S]`. -/
def outRule : RewriteRule where
  name := "Out"
  typeContext := [("n", .base "Name"), ("m", .base "Name"), ("p", .base "Proc")]
  premises := []
  left := amb (.fvar "m")
    (par [amb (.fvar "n") (par [.apply "AOut" [.fvar "m", .fvar "p"]] (some "inner"))] (some "rest"))
  right := par [amb (.fvar "n") (par [.fvar "p"] (some "inner")), amb (.fvar "m") (par [] (some "rest"))] none

/-- `open n.P | n[Q] ~> P | Q`. -/
def openRule : RewriteRule where
  name := "Open"
  typeContext := [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]
  premises := []
  left := par [.apply "AOpen" [.fvar "n", .fvar "p"], amb (.fvar "n") (.fvar "q")] (some "rest")
  right := par [.fvar "p", .fvar "q"] (some "rest")

/-- A component of a parallel composition reduces. -/
def parCongRule : RewriteRule where
  name := "ParCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := par [.fvar "S"] (some "rest")
  right := par [.fvar "T"] (some "rest")

/-- A process reduces under a restriction. -/
def resCongRule : RewriteRule where
  name := "ResCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := .apply "ANu" [.lambda none (.fvar "S")]
  right := .apply "ANu" [.lambda none (.fvar "T")]

/-- The content of an ambient reduces. -/
def ambCongRule : RewriteRule where
  name := "AmbCong"
  typeContext := [("n", .base "Name")]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := amb (.fvar "n") (.fvar "S")
  right := amb (.fvar "n") (.fvar "T")

/-- **Mobile ambients with restriction and replication.**

- **Sorts**: `["Proc", "Name"]` (names are variables of the name sort)
- **Equations**: restriction of inaction, exchange of restrictions, scope extrusion; unfolding, inaction, idempotence,
  distribution and duplication of replication; restriction crossing an ambient boundary; besides the laws of the
  parallel bag
- **Reductions**: In, Out, Open, ParCong, ResCong and AmbCong -/
def ambientNuCalc : LanguageDef :=
  { name := "MobileAmbientsNu"
    types := ["Proc", "Name"]
    terms := terms
    equations := replicationBlockLaws ambientRepBlock ++ [ambientBoundary]
    rewrites := [inRule, outRule, openRule, parCongRule, resCongRule, ambCongRule] }

theorem ambientNuCalc_rewrites :
    ambientNuCalc.rewrites = [inRule, outRule, openRule, parCongRule, resCongRule, ambCongRule] :=
  rfl

/-! ## Admission -/

theorem baseRules_validate :
    ∀ rule ∈ [inRule, outRule, openRule], LanguageDef.validateRewrite ambientNuCalc rule = [] := by
  intro rule membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [inRule, outRule, openRule, ambientNuCalc, terms, prefixRule, amb, par]

theorem contextualRules_validate :
    ∀ rule ∈ [parCongRule, resCongRule, ambCongRule], LanguageDef.validateRewrite ambientNuCalc rule = [] := by
  intro rule membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [parCongRule, resCongRule, ambCongRule, ambientNuCalc, terms, prefixRule, amb, par]

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (restrictionNilOf restrictionExchangeOf scopeExtrusionOf blockLaws
  replicationUnfoldOf replicationNilOf replicationTwiceOf replicationParOf replicationIdempotentOf replicationLaws) in
theorem equations_validate :
    ∀ equation ∈ ambientNuCalc.equations, LanguageDef.validateEquation ambientNuCalc equation = [] := by
  intro equation membership
  simp only [ambientNuCalc, replicationBlockLaws, blockLaws, replicationLaws, List.map_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
      first
        | rfl
        | decide
        | rule_patterns [restrictionNilOf, restrictionExchangeOf, scopeExtrusionOf, replicationUnfoldOf,
            replicationNilOf, replicationTwiceOf, replicationParOf, replicationIdempotentOf, ambientBoundary,
            ambientNuCalc, terms, prefixRule]

/-- The calculus passes the declaration gate. -/
theorem ambientNuCalc_validate_eq_nil : ambientNuCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · exact equations_validate
  · intro rewrite membership
    rw [ambientNuCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
    · exact baseRules_validate _ (by simp)
    · exact baseRules_validate _ (by simp)
    · exact baseRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (restrictionNilOf restrictionExchangeOf scopeExtrusionOf blockLaws
  replicationUnfoldOf replicationNilOf replicationTwiceOf replicationParOf replicationIdempotentOf replicationLaws) in
/-- The reaction rules bind every variable of their contracta in their redexes, the contextual rules read only their
reduction hypotheses, and each law has the same variables on both sides. -/
theorem ambientNuCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    ambientNuCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleAndEquationFlows
  · intro rule membership
    rw [ambientNuCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
    · refine .plain rfl ?_
      intro name nameMembership
      simp [inRule, amb, par, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .plain rfl ?_
      intro name nameMembership
      simp [outRule, amb, par, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .plain rfl ?_
      intro name nameMembership
      simp [openRule, amb, par, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl (by simp [parCongRule, par, Pattern.freeFvarNames]) ?_
      intro name nameMembership
      simp [parCongRule, par, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl (by simp [resCongRule, Pattern.freeFvarNames]) ?_
      intro name nameMembership
      simp [resCongRule, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl (by simp [ambCongRule, amb, Pattern.freeFvarNames]) ?_
      intro name nameMembership
      simp [ambCongRule, amb, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
  · intro equation membership
    simp only [ambientNuCalc, replicationBlockLaws, blockLaws, replicationLaws, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_, ?_⟩ <;>
      · intro name nameMembership
        simp_all [restrictionNilOf, restrictionExchangeOf, scopeExtrusionOf, replicationUnfoldOf, replicationNilOf,
          replicationTwiceOf, replicationParOf, replicationIdempotentOf, ambientBoundary, Pattern.freeFvarNames]

/-- The calculus passes the ordered binding-flow gate with no relation mode. -/
theorem ambientNuCalc_executionAdmissionErrors_eq_nil : ambientNuCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes ambientNuCalc ambientNuCalc_validate_eq_nil
    (ambientNuCalc_executionFlowErrors_eq_nil [])

end Mettapedia.Languages.ProcessCalculi.Ambient.Full
