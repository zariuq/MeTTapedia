import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Identity computation as authored GSLT structure

A type theory may itself be presented as a GSLT.  This makes more of the
theory derivable than constructor classification alone, but it does not make
adequacy automatic.  This calibration uses three presentations with exactly
the same sorts and constructors:

* one has no J computation;
* one has the reflexivity-only iota rule; and
* one incorrectly reduces J for every purported identity proof.

The generic rewrite semantics distinguishes all three.  Any DTT extraction
which reads only the constructor signature cannot.  A production extractor
must therefore consume the operational rules and prove correspondence to an
independent typing/model authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.TypeTheoryGSLTBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

private def ty : TypeExpr := .base "Ty"
private def tm : TypeExpr := .base "Tm"

private def simple (name : String) (type : TypeExpr) : TermParam :=
  .simple name type

private def grammar : List GrammarRule :=
  [ { label := "Type0", category := "Ty", params := [],
      syntaxPattern := [.terminal "Type0"] }
  , { label := "Point", category := "Tm", params := [],
      syntaxPattern := [.terminal "point"] }
  , { label := "Motive", category := "Tm", params := [],
      syntaxPattern := [.terminal "motive"] }
  , { label := "Base", category := "Tm", params := [],
      syntaxPattern := [.terminal "base"] }
  , { label := "Id", category := "Ty",
      params := [simple "carrier" ty, simple "left" tm, simple "right" tm],
      syntaxPattern := [.terminal "Id", .nonTerminal "carrier",
        .nonTerminal "left", .nonTerminal "right"] }
  , { label := "Refl", category := "Tm", params := [simple "term" tm],
      syntaxPattern := [.terminal "refl", .nonTerminal "term"] }
  , { label := "OtherProof", category := "Tm",
      params := [simple "term" tm],
      syntaxPattern := [.terminal "other", .nonTerminal "term"] }
  , { label := "J", category := "Tm",
      params := [simple "motive" tm, simple "base" tm,
        simple "left" tm, simple "right" tm, simple "proof" tm],
      syntaxPattern := [.terminal "J", .nonTerminal "motive",
        .nonTerminal "base", .nonTerminal "left", .nonTerminal "right",
        .nonTerminal "proof"] }
  ]

private def common (name : String) (rewrites : List RewriteRule) : LanguageDef :=
  { name := name
    types := ["Ty", "Tm"]
    terms := grammar
    equations := []
    rewrites := rewrites }

private def properIota : RewriteRule :=
  { name := "J-iota"
    typeContext := [("motive", tm), ("base", tm), ("point", tm)]
    premises := []
    left := .apply "J"
      [.fvar "motive", .fvar "base", .fvar "point", .fvar "point",
        .apply "Refl" [.fvar "point"]]
    right := .fvar "base" }

private def indiscriminateIota : RewriteRule :=
  { name := "J-indiscriminate"
    typeContext := [("motive", tm), ("base", tm),
      ("left", tm), ("right", tm), ("proof", tm)]
    premises := []
    left := .apply "J"
      [.fvar "motive", .fvar "base", .fvar "left", .fvar "right",
        .fvar "proof"]
    right := .fvar "base" }

def withoutJ : LanguageDef := common "IdentityWithoutJ" []
def withJ : LanguageDef := common "IdentityWithJ" [properIota]
def malformedJ : LanguageDef :=
  common "IdentityWithIndiscriminateJ" [indiscriminateIota]

/-- The constructor-category input shared by all three presentations. -/
def constructorReadout (language : LanguageDef) :
    List TypeDecl × List GrammarRule :=
  (language.types, language.terms)

def point : Pattern := .apply "Point" []
def motive : Pattern := .apply "Motive" []
def base : Pattern := .apply "Base" []
def reflPoint : Pattern := .apply "Refl" [point]
def otherPointProof : Pattern := .apply "OtherProof" [point]

def properRedex : Pattern :=
  .apply "J" [motive, base, point, point, reflPoint]

def wrongProofRedex : Pattern :=
  .apply "J" [motive, base, point, point, otherPointProof]

def wrongEndpointRedex : Pattern :=
  .apply "J" [motive, base, point, base, reflPoint]

/-- Constructor data alone cannot distinguish absence of J computation from
the proper iota rule. -/
theorem withoutJ_withJ_same_constructor_readout :
    constructorReadout withoutJ = constructorReadout withJ :=
  rfl

/-- The same constructor data also cannot expose an over-broad, unsound iota
rule. -/
theorem withJ_malformedJ_same_constructor_readout :
    constructorReadout withJ = constructorReadout malformedJ :=
  rfl

/-- Positive control: the authored iota rule computes exactly on
reflexivity. -/
theorem proper_j_computes : rewriteStep withJ properRedex = [base] := by
  simp [rewriteStep, withJ, common, properIota, properRedex, motive, base,
    point, reflPoint, applyRule, matchPattern, matchArgs, mergeBindings,
    applyBindings]

/-- Removing the operational rule removes the computation while leaving the
entire constructor signature unchanged. -/
theorem absent_j_does_not_compute : rewriteStep withoutJ properRedex = [] :=
  rfl

/-- Negative control: the proper rule does not treat unrelated syntax as an
identity proof. -/
theorem proper_j_rejects_other_proof :
    rewriteStep withJ wrongProofRedex = [] := by
  simp [rewriteStep, withJ, common, properIota, wrongProofRedex, motive,
    base, point, otherPointProof, applyRule, matchPattern, matchArgs,
    mergeBindings, applyBindings]

/-- Repeated matcher variables enforce the equal-endpoint reflexivity case. -/
theorem proper_j_rejects_wrong_endpoint :
    rewriteStep withJ wrongEndpointRedex = [] := by
  simp [rewriteStep, withJ, common, properIota, wrongEndpointRedex, motive,
    base, point, reflPoint, applyRule, matchPattern, matchArgs,
    mergeBindings, applyBindings]

/-- Adversarial control: a superficially similar but over-broad rule reduces
an arbitrary purported proof. -/
theorem malformed_j_accepts_other_proof :
    rewriteStep malformedJ wrongProofRedex = [base] := by
  simp [rewriteStep, malformedJ, common, indiscriminateIota, wrongProofRedex,
    motive, base, point, otherPointProof, applyRule, matchPattern, matchArgs,
    mergeBindings, applyBindings]

/-- The operational rules, not the constructor signature, decide whether J
is absent, selective, or indiscriminate. -/
theorem constructor_signature_does_not_determine_identity_computation :
    constructorReadout withoutJ = constructorReadout withJ /\
      constructorReadout withJ = constructorReadout malformedJ /\
      rewriteStep withoutJ properRedex = [] /\
      rewriteStep withJ properRedex = [base] /\
      rewriteStep withJ wrongProofRedex = [] /\
      rewriteStep malformedJ wrongProofRedex = [base] := by
  exact And.intro withoutJ_withJ_same_constructor_readout <|
    And.intro withJ_malformedJ_same_constructor_readout <|
      And.intro absent_j_does_not_compute <|
        And.intro proper_j_computes <|
          And.intro proper_j_rejects_other_proof
            malformed_j_accepts_other_proof

/-! ## Axiom audit -/

#print axioms proper_j_computes
#print axioms proper_j_rejects_other_proof
#print axioms proper_j_rejects_wrong_endpoint
#print axioms malformed_j_accepts_other_proof
#print axioms constructor_signature_does_not_determine_identity_computation

end Mettapedia.Languages.MeTTa.TypeTheory.TypeTheoryGSLTBoundary
