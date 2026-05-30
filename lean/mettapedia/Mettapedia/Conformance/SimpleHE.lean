import Algorithms.MeTTa.HE.Lowering
import Algorithms.MeTTa.Simple.Session
import Mettapedia.Languages.MeTTa.HE.Eval

namespace Mettapedia.Conformance.SimpleHE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Algorithms.MeTTa.HE
open Algorithms.MeTTa.Simple
open MeTTailCore.MeTTaIL.Syntax (Pattern Premise RewriteRule)

private def fsym (s : String) : FrozenHEAtom := FrozenHEAtom.symbol s
private def fvar (s : String) : FrozenHEAtom := FrozenHEAtom.variable s
private def fexpr (xs : List FrozenHEAtom) : FrozenHEAtom := FrozenHEAtom.expr xs

private def atomToFrozen? : Atom → Option FrozenHEAtom
  | .symbol s => some (FrozenHEAtom.symbol s)
  | .var v => some (FrozenHEAtom.variable v)
  | .expression xs => do
      let ys ← xs.mapM atomToFrozen?
      some (FrozenHEAtom.expr ys)
  | .grounded _ => none

private def frozenToAtom : FrozenHEAtom → Atom
  | FrozenHEAtom.symbol s => .symbol s
  | FrozenHEAtom.variable v => .var v
  | FrozenHEAtom.expr xs => .expression (xs.map frozenToAtom)

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

private def resultAtoms (out : ResultSet) : List Atom :=
  out.map Prod.fst

private def toSession (cfg : FrozenHEConfig) : Session :=
  Session.new (toSpecBundle cfg)

private def runSimple (space : Space) (query : Atom) : List Atom :=
  resultAtoms (eval space query 100)

private def runSimpleWithCfg (cfg : FrozenHEConfig) (query : FrozenHEAtom) : List Atom :=
  let sess := toSession cfg
  let out := Session.eval sess query.toPattern
  out.filterMap (fun p => (FrozenHEAtom.ofPattern? p).map frozenToAtom)

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
      (.expression [.symbol "choose", .symbol "seed"])
      (.symbol "red"),
    Atom.equality
      (.expression [.symbol "choose", .symbol "seed"])
      (.symbol "blue")
  ]

private def spacePatternVar : Space :=
  Space.ofList [
    Atom.equality
      (.expression [.symbol "f", .var "x"])
      (.expression [.symbol "result", .var "x"])
  ]

private def spaceUntypedId : Space :=
  Space.ofList [
    Atom.equality
      (.expression [.symbol "id", .var "x"])
      (.var "x")
  ]

private def spaceDuplicate : Space :=
  Space.ofList [
    Atom.equality
      (.expression [.symbol "dup", .symbol "seed"])
      (.symbol "x"),
    Atom.equality
      (.expression [.symbol "dup", .symbol "seed"])
      (.symbol "x")
  ]

private def cfgDuplicate : FrozenHEConfig :=
  { equations :=
      [ { lhs := fexpr [fsym "dup", fsym "seed"], rhs := fsym "x" }
      , { lhs := fexpr [fsym "dup", fsym "seed"], rhs := fsym "x" }
      ]
    maxSteps := 100
    maxNodes := 8192 }

private def cfgPremiseRelation : FrozenHEConfig :=
  { equations :=
      [ { lhs := fexpr [fsym "fromRel", fsym "seed"]
          rhs := fvar "x"
          premises := [.relationQuery "allowed" [fvar "x"]] }
      ]
    relationFacts :=
      [ { relation := "allowed", tuple := [fsym "alpha"] }
      , { relation := "allowed", tuple := [fsym "beta"] }
      ]
    maxSteps := 100
    maxNodes := 8192 }

private def cfgPremiseBuiltin : FrozenHEConfig :=
  { equations :=
      [ { lhs := fexpr [fsym "fromBuiltin", fsym "seed"]
          rhs := fvar "x"
          premises := [.relationQuery "palette" [fvar "x"]] }
      ]
    builtinFacts :=
      [ { relation := "palette", tuple := [fsym "warm"] }
      , { relation := "palette", tuple := [fsym "cool"] }
      ]
    maxSteps := 100
    maxNodes := 8192 }

private def expectedSimple : List Atom := [.symbol "b"]
private def expectedNested : List Atom := [.symbol "b"]
private def expectedNondet : List Atom := [.symbol "red", .symbol "blue"]
private def expectedNoReduction : List Atom := [.expression [.symbol "unknown", .symbol "arg"]]
private def expectedPatternVar : List Atom := [.expression [.symbol "result", .symbol "hello"]]
private def expectedDuplicate : List Atom := [.symbol "x", .symbol "x"]
private def expectedPremiseRelation : List Atom := [.symbol "alpha", .symbol "beta"]
private def expectedPremiseBuiltin : List Atom := [.symbol "warm", .symbol "cool"]
private def expectedPremiseRelationRuntimeFallback : List Atom :=
  [.expression [.symbol "fromRel", .symbol "seed"]]
private def expectedPremiseBuiltinRuntimeFallback : List Atom :=
  [.expression [.symbol "fromBuiltin", .symbol "seed"]]
private def expectedPremiseRelationPremises : List (List Premise) :=
  [[.relationQuery "allowed" [fvar "x" |>.toPattern]]]
private def expectedPremiseBuiltinPremises : List (List Premise) :=
  [[.relationQuery "palette" [fvar "x" |>.toPattern]]]
private def expectedAllowedRows : List (List Pattern) :=
  [[fsym "alpha" |>.toPattern], [fsym "beta" |>.toPattern]]
private def expectedPaletteRows : List (List Pattern) :=
  [[fsym "warm" |>.toPattern], [fsym "cool" |>.toPattern]]

def checkSimple : Bool :=
  decide (
    runSimple spaceSimple (.expression [.symbol "f", .symbol "a"]) =
      expectedSimple
  )

def checkNested : Bool :=
  decide (
    runSimple spaceNested (.expression [.symbol "g", .symbol "a"]) =
      expectedNested
  )

def checkNondet : Bool :=
  decide (
    runSimple spaceNondet (.expression [.symbol "choose", .symbol "seed"]) =
      expectedNondet
  )

def checkNoReduction : Bool :=
  decide (
    runSimple Space.empty (.expression [.symbol "unknown", .symbol "arg"]) =
      expectedNoReduction
  )

def checkPatternVar : Bool :=
  decide (
    runSimple spacePatternVar (.expression [.symbol "f", .symbol "hello"]) =
      expectedPatternVar
  )

def checkUntypedId : Bool :=
  decide (
    runSimple spaceUntypedId (.expression [.symbol "id", .symbol "five"]) =
      [.symbol "five"]
  )

def checkDuplicate : Bool :=
  decide (
    runSimple spaceDuplicate (.expression [.symbol "dup", .symbol "seed"]) = expectedDuplicate
  )

def checkPremiseRelationLowering : Bool :=
  decide (
    ((toSpecBundle cfgPremiseRelation).language.rewrites.map RewriteRule.premises =
        expectedPremiseRelationPremises) ∧
      ((toSpecBundle cfgPremiseRelation).relationEnv.tuples "allowed" [Pattern.fvar "_"] =
        expectedAllowedRows)
  )

def checkPremiseBuiltinLowering : Bool :=
  decide (
    ((toSpecBundle cfgPremiseBuiltin).language.rewrites.map RewriteRule.premises =
        expectedPremiseBuiltinPremises) ∧
      ((toSpecBundle cfgPremiseBuiltin).builtins.relation "palette" [Pattern.fvar "_"] =
        expectedPaletteRows)
  )

def checkPremiseRelationRuntimeFrontier : Bool :=
  decide (
    runSimpleWithCfg cfgPremiseRelation (fexpr [fsym "fromRel", fsym "seed"]) =
      expectedPremiseRelationRuntimeFallback
  )

def checkPremiseBuiltinRuntimeFrontier : Bool :=
  decide (
    runSimpleWithCfg cfgPremiseBuiltin (fexpr [fsym "fromBuiltin", fsym "seed"]) =
      expectedPremiseBuiltinRuntimeFallback
  )

def allChecks : List (String × Bool) :=
  [ ("simple", checkSimple)
  , ("nested", checkNested)
  , ("nondet", checkNondet)
  , ("noReduction", checkNoReduction)
  , ("patternVar", checkPatternVar)
  , ("untypedId", checkUntypedId)
  , ("duplicate", checkDuplicate)
  , ("premiseRelationLowering", checkPremiseRelationLowering)
  , ("premiseBuiltinLowering", checkPremiseBuiltinLowering)
  ]

def allChecksPass : Bool :=
  allChecks.all (fun c => c.2)

def frontierChecks : List (String × Bool) :=
  [ ("premiseRelationRuntimeFrontier", checkPremiseRelationRuntimeFrontier)
  , ("premiseBuiltinRuntimeFrontier", checkPremiseBuiltinRuntimeFrontier)
  ]

def frontierChecksObserved : Bool :=
  frontierChecks.all (fun c => c.2)

/-! ## Conformance theorem scaffolding (non-native_decide path) -/

theorem simple_conformance_of_check
    (h : checkSimple = true) :
    runSimple spaceSimple (.expression [.symbol "f", .symbol "a"]) =
      expectedSimple := by
  unfold checkSimple at h
  exact (decide_eq_true_eq.mp h)

theorem nondet_conformance_of_check
    (h : checkNondet = true) :
    runSimple spaceNondet (.expression [.symbol "choose", .symbol "seed"]) =
      expectedNondet := by
  unfold checkNondet at h
  exact (decide_eq_true_eq.mp h)

theorem premise_relation_lowering_of_check
    (h : checkPremiseRelationLowering = true) :
    ((toSpecBundle cfgPremiseRelation).language.rewrites.map RewriteRule.premises =
        expectedPremiseRelationPremises) ∧
      ((toSpecBundle cfgPremiseRelation).relationEnv.tuples "allowed" [Pattern.fvar "_"] =
        expectedAllowedRows) := by
  unfold checkPremiseRelationLowering at h
  exact (decide_eq_true_eq.mp h)

theorem premise_builtin_lowering_of_check
    (h : checkPremiseBuiltinLowering = true) :
    ((toSpecBundle cfgPremiseBuiltin).language.rewrites.map RewriteRule.premises =
        expectedPremiseBuiltinPremises) ∧
      ((toSpecBundle cfgPremiseBuiltin).builtins.relation "palette" [Pattern.fvar "_"] =
        expectedPaletteRows) := by
  unfold checkPremiseBuiltinLowering at h
  exact (decide_eq_true_eq.mp h)

/-! ## I/O fixture theorem anchors (by fixture ID) -/

theorem he_io_anchor_he_simple_rewrite :
    (h : checkSimple = true) →
    runSimple spaceSimple (.expression [.symbol "f", .symbol "a"]) =
      expectedSimple := by
  intro h
  unfold checkSimple at h
  exact (decide_eq_true_eq.mp h)

theorem he_io_anchor_he_nested_rewrite :
    (h : checkNested = true) →
    runSimple spaceNested (.expression [.symbol "g", .symbol "a"]) =
      expectedNested := by
  intro h
  unfold checkNested at h
  exact (decide_eq_true_eq.mp h)

theorem he_io_anchor_he_nondet_choose_bag :
    (h : checkNondet = true) →
    runSimple spaceNondet (.expression [.symbol "choose", .symbol "seed"]) =
      expectedNondet := by
  intro h
  unfold checkNondet at h
  exact (decide_eq_true_eq.mp h)

theorem he_io_anchor_he_unknown_expr_preserved :
    (h : checkNoReduction = true) →
    runSimple Space.empty (.expression [.symbol "unknown", .symbol "arg"]) =
      expectedNoReduction := by
  intro h
  unfold checkNoReduction at h
  exact (decide_eq_true_eq.mp h)

theorem he_io_anchor_he_pattern_variable_substitution :
    (h : checkPatternVar = true) →
    runSimple spacePatternVar (.expression [.symbol "f", .symbol "hello"]) =
      expectedPatternVar := by
  intro h
  unfold checkPatternVar at h
  exact (decide_eq_true_eq.mp h)

theorem he_io_anchor_he_duplicate_multiplicity_preserved :
    (h : checkDuplicate = true) →
    runSimple spaceDuplicate (.expression [.symbol "dup", .symbol "seed"]) = expectedDuplicate := by
  intro h
  unfold checkDuplicate at h
  exact (decide_eq_true_eq.mp h)

#eval ("expectedSimple", expectedSimple)
#eval ("runtimeSimple", runSimple spaceSimple (.expression [.symbol "f", .symbol "a"]))

#eval ("expectedNested", expectedNested)
#eval ("runtimeNested", runSimple spaceNested (.expression [.symbol "g", .symbol "a"]))

#eval ("expectedNondet", expectedNondet)
#eval ("runtimeNondet", runSimple spaceNondet (.expression [.symbol "choose", .symbol "seed"]))

#eval ("expectedNoReduction", expectedNoReduction)
#eval ("runtimeNoReduction", runSimple Space.empty (.expression [.symbol "unknown", .symbol "arg"]))

#eval ("expectedPatternVar", expectedPatternVar)
#eval ("runtimePatternVar", runSimple spacePatternVar (.expression [.symbol "f", .symbol "hello"]))

#eval ("expectedDuplicate", expectedDuplicate)
#eval ("runtimeDuplicate", runSimple spaceDuplicate (.expression [.symbol "dup", .symbol "seed"]))

#eval ("expectedPremiseRelation", expectedPremiseRelation)
#eval ("runtimePremiseRelation", runSimpleWithCfg cfgPremiseRelation (fexpr [fsym "fromRel", fsym "seed"]))
#eval ("expectedPremiseBuiltin", expectedPremiseBuiltin)
#eval ("runtimePremiseBuiltin", runSimpleWithCfg cfgPremiseBuiltin (fexpr [fsym "fromBuiltin", fsym "seed"]))

#eval allChecks
#eval ("allChecksPass", allChecksPass)
#eval frontierChecks
#eval ("frontierChecksObserved", frontierChecksObserved)

end Mettapedia.Conformance.SimpleHE
