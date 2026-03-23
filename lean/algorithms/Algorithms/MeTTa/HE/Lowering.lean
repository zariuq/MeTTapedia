import Algorithms.MeTTa.Simple.Relations

/-
Lowering from frozen HE atoms to the shared MeTTaIL runtime.

Semantics note:
- HE lowering uses explicit `Sym`/`Expr` constructors to preserve HE surface intent
  from `hyperon/hyperon-experimental/docs/metta.md`.
- The lowering target here is data only: `LanguageDef` + `SpecBundle`.
- Legacy `Simple.Session` execution now lives in
  `Algorithms.MeTTa.HE.LegacySessionBridge`.
- This keeps the forward lowering path spec-driven while isolating the
  deprecated runtime bridge from the reusable lowering artifacts.
-/

namespace Algorithms.MeTTa.HE

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Profile
open Algorithms.MeTTa.Simple

inductive FrozenHEAtom where
  | symbol : String → FrozenHEAtom
  | variable : String → FrozenHEAtom
  | expr : List FrozenHEAtom → FrozenHEAtom
deriving Repr

namespace FrozenHEAtom

def toPattern : FrozenHEAtom → Pattern
  | .symbol name => .apply "Sym" [.apply name []]
  | .variable name => .fvar name
  | .expr atoms => .apply "Expr" (atoms.map toPattern)

def ofPattern? : Pattern → Option FrozenHEAtom
  | .fvar name => some (.variable name)
  | .apply "Sym" [tok] =>
      match tok with
      | .apply name [] => some (.symbol name)
      | _ => none
  | .apply "Expr" args => do
      let atoms ← args.mapM ofPattern?
      some (.expr atoms)
  | _ => none

end FrozenHEAtom

inductive FrozenHEPremise where
  | relationQuery : String → List FrozenHEAtom → FrozenHEPremise
deriving Repr

structure FrozenHEEquation where
  lhs : FrozenHEAtom
  rhs : FrozenHEAtom
  premises : List FrozenHEPremise := []
deriving Repr

structure FrozenHERelationTuple where
  relation : String
  tuple : List FrozenHEAtom
deriving Repr

structure FrozenHEConfig where
  equations : List FrozenHEEquation := []
  relationFacts : List FrozenHERelationTuple := []
  builtinFacts : List FrozenHERelationTuple := []
  maxSteps : Nat := 100
  maxNodes : Nat := 8192
deriving Repr

namespace FrozenHEPremise

def toPremise : FrozenHEPremise → Premise
  | .relationQuery rel args => .relationQuery rel (args.map FrozenHEAtom.toPattern)

end FrozenHEPremise

private def tupleToCore (row : FrozenHERelationTuple) : RelationTuple :=
  { relation := row.relation
    tuple := row.tuple.map FrozenHEAtom.toPattern }

private def builtinsOfConfig (cfg : FrozenHEConfig) : BuiltinTable :=
  mergeBuiltinTables
    coreIntrinsicBuiltins
    (builtinTableOfTuples (cfg.builtinFacts.map tupleToCore))

private def mkRulesAux (idx : Nat) : List FrozenHEEquation → List RewriteRule
  | [] => []
  | eqn :: rest =>
      let rule : RewriteRule := {
        name := s!"HE_EQ_{idx}"
        typeContext := []
        premises := eqn.premises.map FrozenHEPremise.toPremise
        left := eqn.lhs.toPattern
        right := eqn.rhs.toPattern
      }
      rule :: mkRulesAux (idx + 1) rest

def toLanguageDef (cfg : FrozenHEConfig) : LanguageDef := {
  name := "FrozenHE"
  types := ["Atom"]
  terms := []
  equations := []
  rewrites := mkRulesAux 0 cfg.equations
  congruenceCollections := []
}

def toSpecBundle (cfg : FrozenHEConfig) : SpecBundle := {
  language := toLanguageDef cfg
  relationEnv := relationEnvOfTuples (cfg.relationFacts.map tupleToCore)
  builtins := builtinsOfConfig cfg
  policy := {
    maxFuel := cfg.maxSteps
    normalizeToFixedPoint := false
  }
}

end Algorithms.MeTTa.HE
