import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Relations

/-
Lowering from frozen HE atoms to the shared MeTTaIL runtime.

Semantics note:
- HE lowering uses explicit `Sym`/`Expr` constructors to preserve HE surface intent
  from `hyperon/hyperon-experimental/docs/metta.md`.
- `toSession` selects `MeTTaSyntax.he`, and Session evaluation provides a
  Sym-headed `Expr` rewrite fallback so HE-style equations keep reducing when
  tuple intrinsic evaluation is a no-op.
- This keeps the runtime path spec-driven while remaining isolated from PeTTa
  command-head behavior.
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

def toSession (cfg : FrozenHEConfig) : Algorithms.MeTTa.Simple.Session :=
  let s0 := Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfg)
  let s1 := Algorithms.MeTTa.Simple.Session.withSyntax s0 MeTTailCore.MeTTaSyntax.he
  Algorithms.MeTTa.Simple.Session.withBounds s1 cfg.maxSteps cfg.maxNodes

end Algorithms.MeTTa.HE
