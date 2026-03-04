import Algorithms.MeTTa.HE.Lowering
import Mettapedia.Languages.MeTTa.HE.Interpreter

namespace Mettapedia.Conformance.SimpleHE

open Mettapedia.Languages.MeTTa.Core (Atom)
open Mettapedia.Languages.MeTTa.HE
open Algorithms.MeTTa.HE

private def atomToFrozen? : Atom → Option FrozenHEAtom
  | .symbol s => some (.symbol s)
  | .var v => some (.variable v)
  | .expression xs => do
      let ys ← xs.mapM atomToFrozen?
      some (.expr ys)
  | .grounded _ => none

private def frozenToAtom : FrozenHEAtom → Atom
  | .symbol s => .symbol s
  | .variable v => .var v
  | .expr xs => .expression (xs.map frozenToAtom)

private def equationFromAtom? : Atom → Option FrozenHEEquation
  | .expression [.symbol "=", lhs, rhs] => do
      let lhs' ← atomToFrozen? lhs
      let rhs' ← atomToFrozen? rhs
      some { lhs := lhs', rhs := rhs' }
  | _ => none

private def frozenConfigOfSpace (space : Space) : FrozenHEConfig :=
  { equations := space.atoms.filterMap equationFromAtom?
    maxSteps := 100
    maxNodes := 8192 }

/-! ## Syntax/lowering invariants (direct, non-native_decide) -/

theorem frozenConfigOfSpace_equations_def (space : Space) :
    (frozenConfigOfSpace space).equations = space.atoms.filterMap equationFromAtom? := by
  rfl

private def runSimple (space : Space) (query : Atom) : List Atom :=
  match atomToFrozen? query with
  | none => []
  | some q =>
      let cfg := frozenConfigOfSpace space
      let sess := toSession cfg
      let out := Algorithms.MeTTa.Simple.Session.eval sess q.toPattern
      out.filterMap (fun p => (FrozenHEAtom.ofPattern? p).map frozenToAtom)

private def runSimpleWithCfg (cfg : FrozenHEConfig) (query : FrozenHEAtom) : List Atom :=
  let sess := toSession cfg
  let out := Algorithms.MeTTa.Simple.Session.eval sess query.toPattern
  out.filterMap (fun p => (FrozenHEAtom.ofPattern? p).map frozenToAtom)

private def runHE (space : Space) (query : Atom) : List Atom :=
  (eval query space).map Prod.fst

private def spaceSimple : Space :=
  Space.ofList [
    Atom.equality
      (.expression [.symbol "f", .symbol "a"])
      (.symbol "b")
  ]

private def spaceNested : Space :=
  Space.ofList [
    Atom.equality
      (.expression [.symbol "g", .symbol "a"])
      (.expression [.symbol "f", .symbol "a"]),
    Atom.equality
      (.expression [.symbol "f", .symbol "a"])
      (.symbol "b")
  ]

private def spaceNondet : Space :=
  Space.ofList [
    Atom.equality
      (.expression [.symbol "choose"])
      (.symbol "red"),
    Atom.equality
      (.expression [.symbol "choose"])
      (.symbol "blue")
  ]

private def spacePatternVar : Space :=
  Space.ofList [
    Atom.equality
      (.expression [.symbol "f", .var "x"])
      (.expression [.symbol "result", .var "x"])
  ]

private def cfgPremiseRelation : FrozenHEConfig :=
  { equations :=
      [ { lhs := .expr [.symbol "fromRel"]
          rhs := .variable "x"
          premises := [.relationQuery "allowed" [.variable "x"]] }
      ]
    relationFacts :=
      [ { relation := "allowed", tuple := [.symbol "alpha"] }
      , { relation := "allowed", tuple := [.symbol "beta"] }
      ]
    maxSteps := 100
    maxNodes := 8192 }

private def cfgPremiseBuiltin : FrozenHEConfig :=
  { equations :=
      [ { lhs := .expr [.symbol "fromBuiltin"]
          rhs := .variable "x"
          premises := [.relationQuery "palette" [.variable "x"]] }
      ]
    builtinFacts :=
      [ { relation := "palette", tuple := [.symbol "warm"] }
      , { relation := "palette", tuple := [.symbol "cool"] }
      ]
    maxSteps := 100
    maxNodes := 8192 }

private def expectedSimple : List Atom := [.symbol "b"]
private def expectedNested : List Atom := [.symbol "b"]
private def expectedNondet : List Atom := [.symbol "red", .symbol "blue"]
private def expectedNoReduction : List Atom := [.expression [.symbol "unknown", .symbol "arg"]]
private def expectedPatternVar : List Atom := [.expression [.symbol "result", .symbol "hello"]]
private def expectedPremiseRelation : List Atom := [.symbol "alpha", .symbol "beta"]
private def expectedPremiseBuiltin : List Atom := [.symbol "warm", .symbol "cool"]

def checkSimple : Bool :=
  decide (
    runSimple spaceSimple (.expression [.symbol "f", .symbol "a"]) =
      runHE spaceSimple (.expression [.symbol "f", .symbol "a"])
  )

def checkNested : Bool :=
  decide (
    runSimple spaceNested (.expression [.symbol "g", .symbol "a"]) =
      runHE spaceNested (.expression [.symbol "g", .symbol "a"])
  )

def checkNondet : Bool :=
  decide (
    runSimple spaceNondet (.expression [.symbol "choose"]) =
      runHE spaceNondet (.expression [.symbol "choose"])
  )

def checkNoReduction : Bool :=
  decide (
    runSimple Space.empty (.expression [.symbol "unknown", .symbol "arg"]) =
      runHE Space.empty (.expression [.symbol "unknown", .symbol "arg"])
  )

def checkPatternVar : Bool :=
  decide (
    runSimple spacePatternVar (.expression [.symbol "f", .symbol "hello"]) =
      runHE spacePatternVar (.expression [.symbol "f", .symbol "hello"])
  )

def checkPremiseRelationLowering : Bool :=
  decide (
    runSimpleWithCfg cfgPremiseRelation (.expr [.symbol "fromRel"]) =
      expectedPremiseRelation
  )

def checkPremiseBuiltinLowering : Bool :=
  decide (
    runSimpleWithCfg cfgPremiseBuiltin (.expr [.symbol "fromBuiltin"]) =
      expectedPremiseBuiltin
  )

def allChecks : List (String × Bool) :=
  [ ("simple", checkSimple)
  , ("nested", checkNested)
  , ("nondet", checkNondet)
  , ("noReduction", checkNoReduction)
  , ("patternVar", checkPatternVar)
  , ("premiseRelationLowering", checkPremiseRelationLowering)
  , ("premiseBuiltinLowering", checkPremiseBuiltinLowering)
  ]

def allChecksPass : Bool :=
  allChecks.all (fun c => c.2)

/-! ## Conformance theorem scaffolding (non-native_decide path) -/

theorem simple_conformance_of_check
    (h : checkSimple = true) :
    runSimple spaceSimple (.expression [.symbol "f", .symbol "a"]) =
      runHE spaceSimple (.expression [.symbol "f", .symbol "a"]) := by
  unfold checkSimple at h
  exact (decide_eq_true_eq.mp h)

theorem nondet_conformance_of_check
    (h : checkNondet = true) :
    runSimple spaceNondet (.expression [.symbol "choose"]) =
      runHE spaceNondet (.expression [.symbol "choose"]) := by
  unfold checkNondet at h
  exact (decide_eq_true_eq.mp h)

theorem premise_relation_lowering_of_check
    (h : checkPremiseRelationLowering = true) :
    runSimpleWithCfg cfgPremiseRelation (.expr [.symbol "fromRel"]) =
      expectedPremiseRelation := by
  unfold checkPremiseRelationLowering at h
  exact (decide_eq_true_eq.mp h)

theorem premise_builtin_lowering_of_check
    (h : checkPremiseBuiltinLowering = true) :
    runSimpleWithCfg cfgPremiseBuiltin (.expr [.symbol "fromBuiltin"]) =
      expectedPremiseBuiltin := by
  unfold checkPremiseBuiltinLowering at h
  exact (decide_eq_true_eq.mp h)

#eval ("expectedSimple", expectedSimple)
#eval ("runtimeSimple", runSimple spaceSimple (.expression [.symbol "f", .symbol "a"]))
#eval ("specSimple", runHE spaceSimple (.expression [.symbol "f", .symbol "a"]))

#eval ("expectedNested", expectedNested)
#eval ("runtimeNested", runSimple spaceNested (.expression [.symbol "g", .symbol "a"]))
#eval ("specNested", runHE spaceNested (.expression [.symbol "g", .symbol "a"]))

#eval ("expectedNondet", expectedNondet)
#eval ("runtimeNondet", runSimple spaceNondet (.expression [.symbol "choose"]))
#eval ("specNondet", runHE spaceNondet (.expression [.symbol "choose"]))

#eval ("expectedNoReduction", expectedNoReduction)
#eval ("runtimeNoReduction", runSimple Space.empty (.expression [.symbol "unknown", .symbol "arg"]))
#eval ("specNoReduction", runHE Space.empty (.expression [.symbol "unknown", .symbol "arg"]))

#eval ("expectedPatternVar", expectedPatternVar)
#eval ("runtimePatternVar", runSimple spacePatternVar (.expression [.symbol "f", .symbol "hello"]))
#eval ("specPatternVar", runHE spacePatternVar (.expression [.symbol "f", .symbol "hello"]))

#eval ("expectedPremiseRelation", expectedPremiseRelation)
#eval ("runtimePremiseRelation", runSimpleWithCfg cfgPremiseRelation (.expr [.symbol "fromRel"]))
#eval ("expectedPremiseBuiltin", expectedPremiseBuiltin)
#eval ("runtimePremiseBuiltin", runSimpleWithCfg cfgPremiseBuiltin (.expr [.symbol "fromBuiltin"]))

#eval allChecks
#eval ("allChecksPass", allChecksPass)

end Mettapedia.Conformance.SimpleHE
