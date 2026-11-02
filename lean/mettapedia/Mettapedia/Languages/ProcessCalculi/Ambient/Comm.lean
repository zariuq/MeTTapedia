import Mettapedia.Languages.ProcessCalculi.Ambient.Full

/-!
# Mobile ambients with capability paths and communication

Cardelli and Gordon's ambient calculus with communication: the mobile ambients of `ambientNuCalc`, capabilities as
terms of their own sort, a process prefixed by a capability, and anonymous asynchronous communication inside an
ambient. Names and capabilities are sorts, so communication is sorted, as in the exchange types of the typed
calculus: a name is sent to an input of a name, a capability to an input of a capability.

- **Capabilities** (`Cap`): `in n`, `out n`, `open n`, the empty path `ε` and the path `M.M'`.
- **Processes added**: `M.P`, the process `P` prefixed by the capability `M` (`ACap`); the input of a name `(x).P` and
  of a capability (`AInName`, `AInCap`), binding a variable of that sort in `P`; the output of a name `⟨n⟩` and of a
  capability (`AOutName`, `AOutCap`).
- **Laws of paths**, besides those of `ambientNuCalc`: `ε.P = P` and `(M.M').P = M.(M'.P)` (`pathEps`, `pathDot`),
  and a capability prefix is the prefix the pure calculus writes: `(in n).P = in n.P`, and so for `out` and `open`
  (`capPrefix`). There are no laws on capabilities themselves.
- **Reductions**, besides `In`, `Out`, `Open` and the contextual rules: an input and an output side by side
  communicate, `(x).P | ⟨M⟩ ~> P{x ← M}`, for names (`CommName`) and for capabilities (`CommCap`). Communication
  happens inside one ambient: the contextual rules descend into parallel components, restrictions and ambients, so an
  input and an output meet only as components of one bag.

A capability received by an input stands where the input's body uses its variable; once substituted, the laws of paths
read the prefix it makes.

## References

- Cardelli and Gordon (2000), "Mobile Ambients", Theoretical Computer Science 240(1), sections 2 and 4
- Cardelli and Gordon (1999), "Types for Mobile Ambients", POPL, the exchange types
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (replicationBlockLaws)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.ProcessCalculi.Ambient.Full
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb par)

/-! ## The definition -/

/-- The capability sort. -/
abbrev capType : TypeExpr := .base "Cap"

/-- A capability over a name. -/
def capRule (label keyword : String) : GrammarRule :=
  { label := label, category := "Cap", params := [.simple "n" (.base "Name")],
    syntaxPattern := [.terminal keyword, .nonTerminal "n"] }

/-- The constructors added to the pure calculus: capabilities and paths, the capability prefix, and the inputs and
outputs of names and capabilities. -/
def commTerms : List GrammarRule := [
    capRule "CapIn" "in",
    capRule "CapOut" "out",
    capRule "CapOpen" "open",
    { label := "CapEps", category := "Cap", params := [], syntaxPattern := [.terminal "ε"] },
    { label := "CapPath", category := "Cap", params := [.simple "m" (.base "Cap"), .simple "k" (.base "Cap")],
      syntaxPattern := [.nonTerminal "m", .terminal ".", .nonTerminal "k"] },
    { label := "ACap", category := "Proc", params := [.simple "m" (.base "Cap"), .simple "p" (.base "Proc")],
      syntaxPattern := [.nonTerminal "m", .terminal ":", .nonTerminal "p"] },
    { label := "AInName", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "(", .terminal "name", .terminal ")", .nonTerminal "body"] },
    { label := "AOutName", category := "Proc", params := [.simple "n" (.base "Name")],
      syntaxPattern := [.terminal "<", .nonTerminal "n", .terminal ">"] },
    { label := "AInCap", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Cap") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "(", .terminal "cap", .terminal ")", .nonTerminal "body"] },
    { label := "AOutCap", category := "Proc", params := [.simple "m" (.base "Cap")],
      syntaxPattern := [.terminal "<<", .nonTerminal "m", .terminal ">>"] }
  ]

/-- `ε.P = P`. -/
def pathEps : Equation where
  name := "PathEps"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .apply "ACap" [.apply "CapEps" [], .fvar "P"]
  right := .fvar "P"

/-- `(M.M').P = M.(M'.P)`. -/
def pathDot : Equation where
  name := "PathDot"
  typeContext := [("M", .base "Cap"), ("K", .base "Cap"), ("P", .base "Proc")]
  premises := []
  left := .apply "ACap" [.apply "CapPath" [.fvar "M", .fvar "K"], .fvar "P"]
  right := .apply "ACap" [.fvar "M", .apply "ACap" [.fvar "K", .fvar "P"]]

/-- A capability prefix is the prefix of the pure calculus: `(in n).P = in n.P`. -/
def capPrefix (cap fused : String) : Equation where
  name := cap ++ "Prefix"
  typeContext := [("n", .base "Name"), ("P", .base "Proc")]
  premises := []
  left := .apply "ACap" [.apply cap [.fvar "n"], .fvar "P"]
  right := .apply fused [.fvar "n", .fvar "P"]

/-- The laws of paths. -/
def pathLaws : List Equation :=
  [pathEps, pathDot, capPrefix "CapIn" "AIn", capPrefix "CapOut" "AOut", capPrefix "CapOpen" "AOpen"]

/-- `(x).P | ⟨n⟩ ~> P{x ← n}`. -/
def commNameRule : RewriteRule where
  name := "CommName"
  typeContext := [("body", .base "Proc"), ("n", .base "Name")]
  premises := []
  left := par [.apply "AInName" [.lambda none (.fvar "body")], .apply "AOutName" [.fvar "n"]] (some "rest")
  right := par [.subst (.fvar "body") (.fvar "n")] (some "rest")

/-- `(x).P | ⟨M⟩ ~> P{x ← M}`, for a capability `M`. -/
def commCapRule : RewriteRule where
  name := "CommCap"
  typeContext := [("body", .base "Proc"), ("m", .base "Cap")]
  premises := []
  left := par [.apply "AInCap" [.lambda none (.fvar "body")], .apply "AOutCap" [.fvar "m"]] (some "rest")
  right := par [.subst (.fvar "body") (.fvar "m")] (some "rest")

/-- **Mobile ambients with capability paths and communication.**

- **Sorts**: `["Proc", "Name", "Cap"]`
- **Equations**: those of `ambientNuCalc` and the laws of paths
- **Reductions**: In, Out, Open, CommName, CommCap, ParCong, ResCong and AmbCong -/
def ambientCommCalc : LanguageDef :=
  { name := "MobileAmbientsComm"
    types := ["Proc", "Name", "Cap"]
    terms := terms ++ commTerms
    equations := replicationBlockLaws ambientRepBlock ++ [ambientBoundary] ++ pathLaws
    rewrites := [inRule, outRule, openRule, commNameRule, commCapRule, parCongRule, resCongRule, ambCongRule] }

theorem ambientCommCalc_rewrites :
    ambientCommCalc.rewrites =
      [inRule, outRule, openRule, commNameRule, commCapRule, parCongRule, resCongRule, ambCongRule] :=
  rfl

/-! ## Admission -/

theorem reactionRules_validate :
    ∀ rule ∈ [inRule, outRule, openRule, commNameRule, commCapRule],
      LanguageDef.validateRewrite ambientCommCalc rule = [] := by
  intro rule membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [inRule, outRule, openRule, commNameRule, commCapRule, ambientCommCalc, terms, commTerms,
          prefixRule, capRule, amb, par]

theorem contextualRules_validate :
    ∀ rule ∈ [parCongRule, resCongRule, ambCongRule], LanguageDef.validateRewrite ambientCommCalc rule = [] := by
  intro rule membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [parCongRule, resCongRule, ambCongRule, ambientCommCalc, terms, commTerms, prefixRule,
          capRule, amb, par]

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (restrictionNilOf restrictionExchangeOf scopeExtrusionOf blockLaws
  replicationUnfoldOf replicationNilOf replicationTwiceOf replicationParOf replicationIdempotentOf replicationLaws) in
theorem equations_validate :
    ∀ equation ∈ ambientCommCalc.equations, LanguageDef.validateEquation ambientCommCalc equation = [] := by
  intro equation membership
  simp only [ambientCommCalc, replicationBlockLaws, blockLaws, replicationLaws, pathLaws, List.map_nil,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
      first
        | rfl
        | decide
        | rule_patterns [restrictionNilOf, restrictionExchangeOf, scopeExtrusionOf, replicationUnfoldOf,
            replicationNilOf, replicationTwiceOf, replicationParOf, replicationIdempotentOf, ambientBoundary, pathEps,
            pathDot, capPrefix, ambientCommCalc, terms, commTerms, prefixRule, capRule]

/-- The calculus passes the declaration gate. -/
theorem ambientCommCalc_validate_eq_nil : ambientCommCalc.validate = [] := by
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
    rw [ambientCommCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reactionRules_validate _ (by simp)
    · exact reactionRules_validate _ (by simp)
    · exact reactionRules_validate _ (by simp)
    · exact reactionRules_validate _ (by simp)
    · exact reactionRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)
    · exact contextualRules_validate _ (by simp)

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (restrictionNilOf restrictionExchangeOf scopeExtrusionOf blockLaws
  replicationUnfoldOf replicationNilOf replicationTwiceOf replicationParOf replicationIdempotentOf replicationLaws) in
/-- The reaction rules bind every variable of their contracta in their redexes, the contextual rules read only their
reduction hypotheses, and each law has the same variables on both sides. -/
theorem ambientCommCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    ambientCommCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleAndEquationFlows
  · intro rule membership
    rw [ambientCommCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · refine .plain rfl ?_
      intro name nameMembership
      simp [commNameRule, par, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .plain rfl ?_
      intro name nameMembership
      simp [commCapRule, par, Pattern.freeFvarNames] at nameMembership ⊢
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
    simp only [ambientCommCalc, replicationBlockLaws, blockLaws, replicationLaws, pathLaws, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨rfl, ?_, ?_⟩ <;>
      · intro name nameMembership
        simp_all [restrictionNilOf, restrictionExchangeOf, scopeExtrusionOf, replicationUnfoldOf, replicationNilOf,
          replicationTwiceOf, replicationParOf, replicationIdempotentOf, ambientBoundary, pathEps, pathDot,
          capPrefix, Pattern.freeFvarNames]

/-- The calculus passes the ordered binding-flow gate with no relation mode. -/
theorem ambientCommCalc_executionAdmissionErrors_eq_nil : ambientCommCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes ambientCommCalc ambientCommCalc_validate_eq_nil
    (ambientCommCalc_executionFlowErrors_eq_nil [])

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
