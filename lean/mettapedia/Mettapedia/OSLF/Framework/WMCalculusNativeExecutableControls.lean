import Mettapedia.OSLF.Framework.WMCalculusNativeExecutable

/-! # Executable WM exploration: revision cycles, contextual guards, and refusal controls -/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeExecutable.Controls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus

def handles : List (String × TypeExpr) :=
  [("a", .base "State"), ("b", .base "State"), ("q", .base "Query"),
   ("inside", .base "Query"), ("scope", .base "Scope")]

def vertex : WMExtVertex :=
  {wmExtVertexMinimal with forgetting := .scopeBased, overlap := .overlapAware}

def provider : GeneralPremise.ProviderSnapshot where
  signatures := [⟨"outsideScope", [.base "Scope", .base "Query"], [.input, .input]⟩]
  rows := [⟨"outsideScope", [.fvar "scope", .fvar "q"]⟩]

def plan : Plan := compile vertex handles provider

#guard plan.complete

def readout (plan : Plan) (bound : List TypeExpr) (sort : TypeExpr)
    (source : Pattern) (work : Nat) : List Pattern × Bool :=
  let state := Complete.Step.rounds plan bound sort work (Complete.Step.begin plan bound sort source)
  (state.log.map (·.target), Complete.Step.status plan state == .complete)

def revision : Pattern := pExtract (pRevise (.fvar "a") (.fvar "b")) (.fvar "q")
def distributed : Pattern := pCombine (pExtract (.fvar "a") (.fvar "q"))
  (pExtract (.fvar "b") (.fvar "q"))

/-- Reach atom zero eventually; its index shifts under the fixed-point binder. -/
def reaches : Formula Traversal 1 := .mu (.disj (.var 1) (.diamond .future (.var 0)))

def query (source target : Pattern) (formula : Formula Traversal 1 := reaches)
    (work : Nat := 3000) (budget : Nat := 10000) : Except Issue Verdict :=
  ask vertex handles provider (.base "BinaryEvidence") source (fun _ state => state == target)
    formula work budget

#guard readout plan [] (.base "BinaryEvidence") revision 3000 ==
  ([distributed, pExtract (pRevise (.fvar "b") (.fvar "a")) (.fvar "q")], true)
#guard query revision distributed == .ok .proved

def guarded (query : Pattern) : Pattern :=
  pExtract (pForget (.fvar "scope") (.fvar "a")) query

def nested : Pattern := pCombine (guarded (.fvar "q")) pEvidenceZero
def nestedTarget : Pattern := pCombine (pExtract (.fvar "a") (.fvar "q")) pEvidenceZero

#guard (readout plan [] (.base "BinaryEvidence") nested 3000).1.contains nestedTarget
#guard query nested nestedTarget == .ok .proved
#guard query (guarded (.fvar "inside")) (pExtract (.fvar "a") (.fvar "inside")) == .ok .refuted

/-- Reachability is not inevitability: commutativity permits an endless cycle. -/
def inevitable : Formula Traversal 1 :=
  .mu (.disj (.var 1) (.conj (.diamond .future .tt) (.box .future (.var 0))))

#guard query revision distributed inevitable == .ok .refuted
#guard query revision distributed (work := 0) == .ok (.unknown .unsettled)
#guard query revision distributed (budget := 0) == .ok (.unknown .allowance)
#guard query revision distributed (.diamond .past .tt) == .ok (.unknown .pastModality)
#guard query revision distributed (.mu (.neg (.var 0))) == .ok (.unknown .notPositive)
#guard query (.fvar "q") distributed == .error .sourceSort
#guard (compile vertex handles {signatures := [], rows := []}).complete == false
#guard (match ask vertex handles {signatures := [], rows := []} (.base "BinaryEvidence")
  revision (fun _ : Fin 1 => fun state => state == distributed) reaches 3000 10000 with
  | .error (.admission _) => true
  | _ => false)

#guard query (pExtract (pOverlapMerge (.fvar "a") (.fvar "b")) (.fvar "q"))
  (pOverlapCorrect (pExtract (.fvar "a") (.fvar "q"))
    (pExtract (.fvar "b") (.fvar "q"))
    (pOverlapFactor (.fvar "a") (.fvar "b") (.fvar "q"))) == .ok .proved

#print axioms ask_admitted
#print axioms ask_proved
#print axioms ask_refuted

end Mettapedia.OSLF.Framework.WMCalculusNativeExecutable.Controls
