import Mettapedia.OSLF.Framework.WMCalculusFullNativeExecutable

/-! # Full WM execution with output-producing relation premises -/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusFullNativeExecutable.Controls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus

def handles : List (String × TypeExpr) :=
  [("w", .base "State"), ("q", .base "Query"), ("equivalent", .base "Query"),
   ("scope", .base "Scope"), ("point", .base "PointedKripke"), ("phi", .base "ModalQuery")]

def reaches : Formula Traversal 1 := .mu (.disj (.var 1) (.diamond .future (.var 0)))

def query (rows : List GeneralPremise.ProviderRow) (source target : Pattern) :
    Except WMCalculusNativeExecutable.Issue Verdict :=
  ask handles rows (.base "BinaryEvidence") source (fun _ => (· == target)) reaches 1000 10000

def equivalentRow : GeneralPremise.ProviderRow :=
  ⟨"queryEquiv", [.fvar "q", .fvar "equivalent"]⟩

/- The target query is produced by the premise, not bound on the left side. -/
#guard query [equivalentRow] (pGenericEvidence (.fvar "w") (.fvar "q"))
  (pGenericEvidence (.fvar "w") (.fvar "equivalent")) == .ok .proved
#guard query [] (pGenericEvidence (.fvar "w") (.fvar "q"))
  (pGenericEvidence (.fvar "w") (.fvar "equivalent")) == .ok .refuted

/-- Erasure produces a scope consumed by the next premise. -/
def erasure : GeneralPremise.ProviderRow := ⟨"erasesInScope", [.fvar "scope", .fvar "w"]⟩
def outside : GeneralPremise.ProviderRow := ⟨"outsideScope", [.fvar "scope", .fvar "q"]⟩

#guard query [erasure, outside] (pExtract (.fvar "w") (.fvar "q")) pEvidenceZero == .ok .proved
#guard query [erasure] (pExtract (.fvar "w") (.fvar "q")) pEvidenceZero == .ok .refuted

/-- Refutation contributes negative singleton evidence, not zero evidence. -/
def refutation : GeneralPremise.ProviderRow := ⟨"kripkeNotSat", [.fvar "point", .fvar "phi"]⟩
def singletonQuery : Pattern := pKripkeEvidence (pSingleton (.fvar "point")) (.fvar "phi")

#guard query [refutation] singletonQuery pEvidenceOneNegative == .ok .proved
#guard query [refutation] singletonQuery pEvidenceZero == .ok .refuted

#print axioms ask_proved
#print axioms ask_refuted

end Mettapedia.OSLF.Framework.WMCalculusFullNativeExecutable.Controls
