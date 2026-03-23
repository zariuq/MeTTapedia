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

private def headCtor? : Pattern → Option String
  | .apply c _ => some c
  | _ => none

private theorem mkRulesAux_length (idx : Nat) (rules : List FrozenPeTTaRule) :
    (mkRulesAux idx rules).length = rules.length := by
  induction rules generalizing idx with
  | nil =>
      simp [mkRulesAux]
  | cons rule rest ih =>
      simp [mkRulesAux, ih]

private theorem mkRulesAux_heads (idx : Nat) (rules : List FrozenPeTTaRule) :
    (mkRulesAux idx rules).map (fun r => headCtor? r.left) =
      rules.map (fun r => headCtor? r.lhs) := by
  induction rules generalizing idx with
  | nil =>
      simp [mkRulesAux]
  | cons rule rest ih =>
      simp [mkRulesAux, headCtor?]
      simpa using ih (idx + 1)

def toLanguageDef (cfg : FrozenPeTTaConfig) : LanguageDef := {
  name := "FrozenPeTTa"
  types := ["Pattern"]
  terms := []
  equations := []
  rewrites := mkRulesAux 0 cfg.rules
  congruenceCollections := []
}

/-! ## Lowering No-Loss Contracts -/

theorem toLanguageDef_rewrite_count_preserved (cfg : FrozenPeTTaConfig) :
    (toLanguageDef cfg).rewrites.length = cfg.rules.length := by
  simpa [toLanguageDef] using mkRulesAux_length 0 cfg.rules

theorem toLanguageDef_rewrite_heads_preserved (cfg : FrozenPeTTaConfig) :
    (toLanguageDef cfg).rewrites.map (fun r => headCtor? r.left) =
      cfg.rules.map (fun r => headCtor? r.lhs) := by
  simpa [toLanguageDef] using mkRulesAux_heads 0 cfg.rules

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

theorem spaceMatchFromFacts_noLoss_two_args
    (facts : List Pattern) (pat tmpl : Pattern) (bs : Bindings)
    (hbs : bs ∈ matchFactsAgainstSpace facts pat) :
    [applyBindings bs pat, applyBindings bs tmpl] ∈
      spaceMatchFromFacts facts [pat, tmpl] := by
  unfold spaceMatchFromFacts
  exact List.mem_map.mpr ⟨bs, hbs, rfl⟩

theorem spaceMatchFromFacts_noLoss_three_args
    (facts : List Pattern) (pat tmpl out : Pattern) (bs : Bindings)
    (hbs : bs ∈ matchFactsAgainstSpace facts pat) :
    [applyBindings bs pat, applyBindings bs tmpl, applyBindings bs tmpl] ∈
      spaceMatchFromFacts facts [pat, tmpl, out] := by
  unfold spaceMatchFromFacts
  exact List.mem_map.mpr ⟨bs, hbs, rfl⟩

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

theorem toSpecBundle_spaceMatch_contains_fact_row
    (cfg : FrozenPeTTaConfig) (args row : List Pattern)
    (hrow : row ∈ spaceMatchFromFacts cfg.facts args) :
    row ∈ (toSpecBundle cfg).builtins.relation "spaceMatch" args := by
  unfold toSpecBundle builtinsOfConfig
  simp [mergeBuiltinTables, hrow]

end Algorithms.MeTTa.PeTTa
