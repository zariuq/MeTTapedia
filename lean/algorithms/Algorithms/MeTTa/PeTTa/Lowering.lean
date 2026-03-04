import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Relations

namespace Algorithms.MeTTa.PeTTa

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match
open MeTTailCore.MeTTaIL.Substitution
open MeTTailCore.MeTTaIL.Profile
open Algorithms.MeTTa.Simple

inductive FrozenPeTTaPremise where
  | relationQuery : String → List Pattern → FrozenPeTTaPremise
deriving Repr

namespace FrozenPeTTaPremise

def toPremise : FrozenPeTTaPremise → Premise
  | .relationQuery rel args => .relationQuery rel args

end FrozenPeTTaPremise

/-- Frozen PeTTa rule payload for runtime lowering. -/
structure FrozenPeTTaRule where
  lhs : Pattern
  rhs : Pattern
  premises : List FrozenPeTTaPremise := []
deriving Repr

/-- Frozen PeTTa runtime profile.

The initial lowering focuses on unconditional rewrite rules, matching the same
runtime kernel shape used by HE lowering. `facts` are kept in the profile for
future `match &self` compilation paths.
-/
structure FrozenPeTTaConfig where
  rules : List FrozenPeTTaRule := []
  facts : List Pattern := []
  relationFacts : List RelationTuple := []
  builtinFacts : List RelationTuple := []
  maxSteps : Nat := 200
  maxNodes : Nat := 8192
deriving Repr

private def mkRulesAux (idx : Nat) : List FrozenPeTTaRule → List RewriteRule
  | [] => []
  | rule :: rest =>
      let rewrite : RewriteRule := {
        name := s!"PETTA_RULE_{idx}"
        typeContext := []
        premises := rule.premises.map FrozenPeTTaPremise.toPremise
        left := rule.lhs
        right := rule.rhs
      }
      rewrite :: mkRulesAux (idx + 1) rest

def toLanguageDef (cfg : FrozenPeTTaConfig) : LanguageDef := {
  name := "FrozenPeTTa"
  types := ["Pattern"]
  terms := []
  equations := []
  rewrites := mkRulesAux 0 cfg.rules
  congruenceCollections := []
}

private def matchFactsAgainstSpace (facts : List Pattern) : Pattern → List Bindings
  | .apply "," [lhs, rhs] =>
      (matchFactsAgainstSpace facts lhs).flatMap fun bL =>
        (matchFactsAgainstSpace facts rhs).filterMap fun bR =>
          mergeBindings bL bR
  | pat =>
      facts.flatMap fun fact =>
        matchPattern pat fact
termination_by pat => sizeOf pat

private def spaceMatchFromFacts (facts : List Pattern) (args : List Pattern) :
    List (List Pattern) :=
  match args with
  | [pat, tmpl, _out] =>
      (matchFactsAgainstSpace facts pat).map fun bs =>
        let pat' := applyBindings bs pat
        let tmpl' := applyBindings bs tmpl
        [pat', tmpl', tmpl']
  | [pat, tmpl] =>
      (matchFactsAgainstSpace facts pat).map fun bs =>
        let pat' := applyBindings bs pat
        let tmpl' := applyBindings bs tmpl
        [pat', tmpl']
  | _ => []

private def builtinsOfConfig (cfg : FrozenPeTTaConfig) : BuiltinTable :=
  let extensional := builtinTableOfTuples cfg.builtinFacts
  let pettaBuiltins : BuiltinTable :=
    { relation := fun rel args =>
        let baseRows := extensional.relation rel args
        if rel == "spaceMatch" then
          baseRows ++ spaceMatchFromFacts cfg.facts args
        else
          baseRows }
  mergeBuiltinTables coreIntrinsicBuiltins pettaBuiltins

def toSpecBundle (cfg : FrozenPeTTaConfig) : SpecBundle := {
  language := toLanguageDef cfg
  relationEnv := relationEnvOfTuples cfg.relationFacts
  builtins := builtinsOfConfig cfg
  policy := {
    maxFuel := cfg.maxSteps
    normalizeToFixedPoint := false
  }
}

def toSession (cfg : FrozenPeTTaConfig) : Algorithms.MeTTa.Simple.Session :=
  (Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfg)).withBounds cfg.maxSteps cfg.maxNodes

end Algorithms.MeTTa.PeTTa
