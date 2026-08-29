import Mettapedia.OSLF.PresheafNativeType.PresheafSemantics
import Mettapedia.GSLT.LanguageDef.Gauthier.Properties

/-!
# Gauthier OEIS Native-Type Bridge

This file instantiates the lightweight constructor native-type endpoint for the
Gauthier OEIS DSL.  The native predicates are semantic: sign and parity classify
observed evaluator results, while totality classifies programs whose certified
totality analyzer succeeds.
-/

namespace Mettapedia.OSLF.Framework.GauthierOEISNativeTypes

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierProperties

/-! ## Language Definition -/

private def progTy : TypeExpr := .base "Prog"
private def intTy : TypeExpr := .base "Int"

private def progParam (name : String) : TermParam :=
  .simple name progTy

private def opRule (label : String) (args : List String) : GrammarRule :=
  { label := label,
    category := "Prog",
    params := args.map progParam,
    syntaxPattern := .terminal label :: args.map SyntaxItem.nonTerminal }

/-- The Gauthier OEIS DSL as an OSLF language definition.

The first sixteen grammar rules are the OEIS operator vocabulary.  The
`evalObs` constructor is a bridge-side observation form used to state native
types for certified evaluator results. -/
def gauthierOEIS : LanguageDef := {
  name := "GauthierOEIS",
  types := [
    { name := "Prog", carrier := .ast },
    { name := "Int", carrier := .builtinInt },
    { name := "EvalObs", carrier := .ast }
  ],
  terms := [
    opRule "zero" [],
    opRule "one" [],
    opRule "two" [],
    opRule "addi" ["left", "right"],
    opRule "diff" ["left", "right"],
    opRule "mult" ["left", "right"],
    opRule "divi" ["left", "right"],
    opRule "modu" ["left", "right"],
    opRule "cond" ["test", "thenBranch", "elseBranch"],
    opRule "loop" ["body", "bound", "init"],
    opRule "x" [],
    opRule "y" [],
    opRule "compr" ["body", "bound"],
    opRule "loop2" ["bodyLeft", "bodyRight", "bound", "initLeft", "initRight"],
    opRule "push" ["head", "tail"],
    opRule "pop" ["list"],
    { label := "evalObs",
      category := "EvalObs",
      params := [.simple "program" progTy, .simple "value" intTy],
      syntaxPattern := [.terminal "evalObs", .nonTerminal "program", .nonTerminal "value"] }
  ],
  equations := [],
  rewrites := []
}

/-! ## Pattern Encoding -/

/-- Table-index labels for the 16-operation OEIS vocabulary. -/
def opLabel : Nat → String
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | 3 => "addi"
  | 4 => "diff"
  | 5 => "mult"
  | 6 => "divi"
  | 7 => "modu"
  | 8 => "cond"
  | 9 => "loop"
  | 10 => "x"
  | 11 => "y"
  | 12 => "compr"
  | 13 => "loop2"
  | 14 => "push"
  | 15 => "pop"
  | n => "op#" ++ toString n

/-- Encode a Gauthier E1 program as an OSLF pattern over the OEIS vocabulary. -/
def progToPattern : Prog → Pattern
  | .node id [] => .apply (opLabel id) []
  | .node id children => .apply (opLabel id) (progListToPattern children)
where
  progListToPattern : List Prog → List Pattern
    | [] => []
    | p :: ps => progToPattern p :: progListToPattern ps

/-- Encode an integer evaluator result as a pattern payload. -/
def intToPattern (v : Int) : Pattern :=
  .fvar (toString v)

/-- Encode one successful evaluator observation. -/
def evalObsPattern (p : Prog) (v : Int) : Pattern :=
  .apply "evalObs" [progToPattern p, intToPattern v]

/-! ## Constructor Native Types -/

private def progSortObj : ConstructorObj gauthierOEIS where
  sort := ⟨"Prog", by
    change "Prog" ∈ (gauthierOEIS.types.map (fun decl => decl.name))
    simp [gauthierOEIS]⟩

private def evalObsSortObj : ConstructorObj gauthierOEIS where
  sort := ⟨"EvalObs", by
    change "EvalObs" ∈ (gauthierOEIS.types.map (fun decl => decl.name))
    simp [gauthierOEIS]⟩

/-- Native type of certified sign observations. -/
def signNativeType : ConstructorNativeType gauthierOEIS where
  sort := evalObsSortObj
  pred := fun pat =>
    ∃ p v, pat = evalObsPattern p v ∧ (certifiedSignAnalysis p).denote v

/-- Native type of certified parity observations. -/
def parityNativeType : ConstructorNativeType gauthierOEIS where
  sort := evalObsSortObj
  pred := fun pat =>
    ∃ p v, pat = evalObsPattern p v ∧ (certifiedParityAnalysis p).denote v

/-- Native type of certified total programs. -/
def totalNativeType : ConstructorNativeType gauthierOEIS where
  sort := progSortObj
  pred := fun pat =>
    ∃ p, pat = progToPattern p ∧ certifiedTotalAnalysis p = true

/-! ## Certified Bridges to the Evaluator -/

/-- Successful E1 evaluation produces a member of the certified sign native type. -/
theorem signNativeType_sound {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (hn : 0 <= n)
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    signNativeType.pred (evalObsPattern p v) := by
  exact ⟨p, v, rfl, Seal.certified_sign_sound hn heval⟩

/-- Successful E1 evaluation produces a member of the certified parity native type. -/
theorem parityNativeType_sound {p : Prog} {fuel : Nat} {n v : Int} {st' : Store}
    (heval : eval fuel orgE1Signature p (seed n) Store.zero = some (v, st')) :
    parityNativeType.pred (evalObsPattern p v) := by
  exact ⟨p, v, rfl, Seal.certified_parity_sound heval⟩

/-- A certified-total program is a native-type member and evaluates at fixed fuel. -/
theorem totalNativeType_sound {p : Prog}
    (htotal : certifiedTotalAnalysis p = true) {n : Int} (st : Store) (hn : 0 <= n) :
    totalNativeType.pred (progToPattern p) ∧
      totalAnalysis p = true ∧
        ∃ v st', eval (progHeight p + 1) orgE1Signature p (seed n) st = some (v, st') := by
  exact ⟨⟨p, rfl, htotal⟩, Seal.certified_total_sound htotal st hn⟩

end Mettapedia.OSLF.Framework.GauthierOEISNativeTypes
